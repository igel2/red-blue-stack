{-# LANGUAGE CPP, DeriveDataTypeable, ViewPatterns #-}

-- | A Red-Blue-Stack behaves just like a normal stack. But it additionally tags
-- every pushed element with a colour (red or blue). It is possible to pop the
-- topmost (in the LIFO sense) red/blue element or the overall-top element (no
-- matter which colour it has been tagged with).
--
-- The tagging is done using the type system: A 'RedBlueStack' has two type
-- parameters: one for the red and one for the blue items. This way the type
-- system prevents us from mixing up red and blue items.
--
-- Whenever the /O/-notation is used, /n/ denotes the total number of elements
-- in the stack. /r/ (and /b/) denote the minimum of the lengths of the first
-- two red (or blue) subsequences on the stack. For instance an @[r,r,r,r,b,r,r]@
-- stack would have /r = 2/ and /b = 0/. /chunks/ denotes the total number chunks
-- of elements with the same colour, e.g. @[r,r,r,b,b,r,b,r]@ has 5 chunks.
--
-- This module is strongly inspired by a 2008\/09\/25 post of apfelmus on the
-- Haskell-cafe mailing list.
module Data.RedBlueStack
    ( -- * Red-blue-stack type
#ifdef __DEBUG__
      RedBlueStack(..)
#else
      RedBlueStack
#endif
      -- * Query
    , isEmpty, size
      -- * Construction
    , empty
    , singleton, redSingleton, blueSingleton
    , push, pushRed, pushBlue
    , append
      -- * Transformations
    , recolour, reverse
      -- * Deconstruction
      -- ** Views
    , view, viewRed, viewBlue
    , top, topRed, topBlue
    , pop, popRed, popBlue
      -- ** Substacks
    , take, drop, splitAt
    , takeWhile, dropWhile, span, break
    , filter, partition
      -- * Map
    , mapBoth, mapRed, mapBlue
      -- * Fold
    , foldrBoth, foldlBoth
    , foldrRed,  foldlRed
    , foldrBlue, foldlBlue
      -- * Conversion
      -- ** Lists
    , fromList, toList, toRedList, toBlueList, toLists
      -- ** Sequences
    , fromSeq, toSeq, toRedSeq, toBlueSeq, toSeqs
    ) where

import Control.Monad hiding ( forM_ )
import Data.Binary
import Data.Foldable hiding ( toList )
import qualified Data.Foldable as Foldable
import Data.Monoid
import Data.Ord
import Data.Sequence (Seq, ViewL(..), (><), (|>), (<|), length, null, viewl)
import qualified Data.Sequence as Seq
import Data.Typeable
import Prelude hiding
    ( break, drop, dropWhile, filter, foldl, foldr, length, null, reverse, span
    , splitAt, take, takeWhile )
import Text.Read hiding ( get )

-- | Red-blue-stack type. @r@ and @b@ are the types of red and blue items.
data RedBlueStack r b
    = Empty
    | RBStack (Seq r) (RedBlueStack b r) -- invariant: only first sequence may be empty
    deriving (Typeable)

instance (Show r, Show b) => Show (RedBlueStack r b) where
    showsPrec d stack = showParen (d > 10)
        $ showString "fromList" . (showsPrec 11 (toList stack))

instance (Read r, Read b) => Read (RedBlueStack r b) where
    readPrec = parens $ prec 10 $ do
        Ident "fromList" <- lexP
        fmap fromList readPrec
    readListPrec = readListPrecDefault

instance (Eq r, Eq b) => Eq (RedBlueStack r b) where
    stack1 == stack2 = (toList stack1) == (toList stack2)

instance (Ord r, Ord b) => Ord (RedBlueStack r b) where
    compare = comparing toList

instance Monoid (RedBlueStack r b) where
    mempty  = empty
    mappend = append

instance Functor (RedBlueStack r) where
    fmap = mapBlue

instance Foldable (RedBlueStack r) where
    foldr = foldrBlue
    foldl = foldlBlue

type RBSLenType = Int

instance (Binary r, Binary b) => Binary (RedBlueStack r b) where
    put Empty              = put (-1 :: RBSLenType)
    put (RBStack rs stack) = do put (length rs :: RBSLenType)
                                forM_ rs put
                                put stack

    get = do
        len <- get :: Get RBSLenType
        if len < 0
            then return Empty
            else liftM2 RBStack (fmap Seq.fromList $ sequence (replicate len get)) get

-- | /O(1)/. Find out if the stack is empty.
isEmpty :: RedBlueStack r b -> Bool
isEmpty Empty                          = True
isEmpty (RBStack (null -> True) Empty) = True -- first Seq may be empty
isEmpty _                              = False

-- | /O(chunks)/. Count the elements in the stack.
size :: RedBlueStack r b -> Int
size Empty              = 0
size (RBStack rs stack) = length rs + size stack

-- | /O(1)/. Construct an empty stack.
empty :: RedBlueStack r b
empty = Empty

-- | /O(1)/. Singleton stack holding either a red or a blue item.
singleton :: Either r b -> RedBlueStack r b
singleton = either redSingleton blueSingleton

-- | /O(1)/. Singleton stack holding a red item.
redSingleton :: r -> RedBlueStack r b
redSingleton r = RBStack (Seq.singleton r) Empty

-- | /O(1)/. Singleton stack holding a blue item.
blueSingleton :: b -> RedBlueStack r b
blueSingleton = recolour . redSingleton

-- | /O(1)/. Push either a red or a blue item on the stack.
push :: Either r b -> RedBlueStack r b -> RedBlueStack r b
push = either pushRed pushBlue

-- | /O(1)/. Push a red item on the stack.
pushRed :: r -> RedBlueStack r b -> RedBlueStack r b
pushRed r Empty              = redSingleton r
pushRed r (RBStack rs stack) = RBStack (r <| rs) stack

-- | /O(1)/. Push a blue item on the stack.
pushBlue :: b -> RedBlueStack r b -> RedBlueStack r b
pushBlue b = recolour . pushRed b . recolour

-- | /O(chunks + log lastchunk)/ (chunks of first stack + log of last chunk of
-- the first stack). Appends the elements of the 2nd stack to the first, so that
-- @append s1 s2 == fromList (toList s1 ++ toList s2)@.
append :: RedBlueStack r b -> RedBlueStack r b -> RedBlueStack r b
append stack1              Empty               = stack1
append Empty               stack2              = stack2
append (RBStack rs1 Empty) (RBStack rs2 tail2) = RBStack (rs1 >< rs2) tail2
append (RBStack rs1 blue1@(RBStack bs1 tail1)) stack2@(RBStack rs2 tail2)
    | null rs2  = RBStack rs1 (append blue1 tail2)
    | otherwise = RBStack rs1 (RBStack bs1 (append tail1 stack2))

-- | /O(1)/. Swaps the colours of all items.
recolour :: RedBlueStack r b -> RedBlueStack b r
recolour Empty                          = Empty
recolour (RBStack (null -> True) stack) = stack
recolour stack                          = RBStack mempty stack
{-# INLINE recolour #-}
{-# RULES "recolour/recolour" forall s. recolour (recolour s) = s #-}

-- | /O(n)/. Reverse the order of elements.
reverse :: RedBlueStack r b -> RedBlueStack r b
reverse Empty              = Empty
reverse (RBStack rs stack) = recolour (reverse stack)
    `append` RBStack (Seq.reverse rs) Empty

-- | /O(1)/. Finds the top item of the stack, whatever it colour it is tagged
-- with. Returns this item and the stack with that item removed or 'Nothing' if
-- the stack was empty.
view :: RedBlueStack r b -> Maybe (Either r b, RedBlueStack r b)
view Empty                              = Nothing
view (RBStack (viewl -> r :< rs) stack) = Just (Left r, RBStack rs stack)
view (RBStack (viewl -> EmptyL)  stack) =
    fmap (\(b, stack') -> (either Right Left b, recolour stack')) $ view stack
{-# INLINE view #-}

-- | /O(1)/ for the top element and /O(log r)/ for the remaining stack. Finds
-- the topmost red item in the stack and removes it from the stack. If the stack
-- doesn't contain any red item, 'Nothing' is returned.
viewRed :: RedBlueStack r b -> Maybe (r, RedBlueStack r b)
viewRed = fmap (fmap recolour) . viewBlue . recolour
{-# INLINE viewRed #-}

-- | /O(1)/ for the top element and /O(log b)/ for the remaining stack. Finds
-- the topmost blue item in the stack and removes it from the stack. If the
-- stack doesn't contain any blue item, 'Nothing' is returned.
viewBlue :: RedBlueStack r b -> Maybe (b, RedBlueStack r b)
viewBlue (RBStack rs (RBStack (viewl -> b :< bs) Empty))
    | null bs   = Just (b, RBStack rs Empty)
    | otherwise = Just (b, RBStack rs (RBStack bs Empty))
viewBlue (RBStack rs1 (RBStack (viewl -> b :< bs) (RBStack rs2 stack)))
    | null bs   = Just (b, RBStack (rs1 >< rs2) stack)
    | otherwise = Just (b, RBStack rs1 (RBStack bs (RBStack rs2 stack)))
viewBlue _      = Nothing
{-# INLINE viewBlue #-}

-- | /O(1)/. Find the top element of the stack, no matter how it is coloured.
top :: RedBlueStack r b -> Maybe (Either r b)
top = fmap fst . view

-- | /O(1)/. Find the top element of the stack that is red.
topRed :: RedBlueStack r b -> Maybe r
topRed = fmap fst . viewRed

-- | /O(1)/. Find the top element of the stack that is blue.
topBlue :: RedBlueStack r b -> Maybe b
topBlue = fmap fst . viewBlue

-- | /O(1)/. Remove the top element from the stack, no matter how it is
-- coloured.
pop :: RedBlueStack r b -> Maybe (RedBlueStack r b)
pop = fmap snd . view

-- | /O(log r)/. Remove the topmost red item from the stack.
popRed :: RedBlueStack r b -> Maybe (RedBlueStack r b)
popRed = fmap snd . viewRed

-- | /O(log b)/. Remove the topmost blue item from the stack.
popBlue :: RedBlueStack r b -> Maybe (RedBlueStack r b)
popBlue = fmap snd . viewBlue

-- | /O(n)/. The first /n/ elements of a 'RedBlueStack'.
take :: Int -> RedBlueStack r b -> RedBlueStack r b
take n = fst . splitAt n

-- | /O(n)/. A 'RedBlueStack' holding all elements after the /n/-th.
drop :: Int -> RedBlueStack r b -> RedBlueStack r b
drop n = snd . splitAt n

-- | /O(n)/. Split a 'RedBlueStack' at position /n/.
-- @'splitAt' n s = ('take' n s, 'drop' n s)@.
splitAt :: Int -> RedBlueStack r b -> (RedBlueStack r b, RedBlueStack r b)
splitAt _ Empty      = (mempty, mempty)
splitAt n (RBStack rs stack)
    | n >= redLength = let
        (first, remaining) = splitAt (n - redLength) stack
        in (RBStack rs Empty `append` recolour first, recolour remaining)
    | otherwise      = let
         (rs', rs'') = Seq.splitAt n rs
         in (RBStack rs' Empty, RBStack rs'' stack)
    where redLength = length rs

-- | /O(n)/. Returns the longest prefix of elements fulfilling the predicate.
takeWhile :: (Either r b -> Bool) -> RedBlueStack r b -> RedBlueStack r b
takeWhile p = fst . span p

-- | /O(n)/. Removes the longest prefix of elements not fulfilling the predicate.
dropWhile :: (Either r b -> Bool) -> RedBlueStack r b -> RedBlueStack r b
dropWhile p = snd . span p

-- | /O(n)/. Returns a tuple of 'RedBlueStack's. The first is the longest prefix
-- fulfilling the predicate, the second one is the rest of the 'RedBlueStack'.
-- @ 'span' p s = ('takeWhile' p s, 'dropWhile' p s) @.
span :: (Either r b -> Bool) -> RedBlueStack r b -> (RedBlueStack r b, RedBlueStack r b)
span _ (view -> Nothing) = (mempty, mempty)
span p stack@(view -> Just (x, xs))
     | p x       = let (yes, no) = span p xs in (push x yes, no)
     | otherwise = (mempty, stack)

-- | /O(n)/. Returns a tuple of 'RedBlueStack's. The first is the longest prefix
-- /not/ fulfilling the predicate, the second one is the rest of the
-- 'RedBlueStack'. @ 'break' p = 'span' ('not' . p) @.
break :: (Either r b -> Bool) -> RedBlueStack r b -> (RedBlueStack r b, RedBlueStack r b)
break p = span (not . p)

-- | /O(n)/. Only keep those elements that satisfy a given predicate.
filter :: (Either r b -> Bool) -> RedBlueStack r b -> RedBlueStack r b
filter p = fst . partition p

-- | /O(n)/. Separate a 'RedBlueStack' in one that satisfies the predicate and
-- one that doesn't.
-- @ 'partition' p s = ('filter' p s, 'filter' ('not' . p) s) @.
partition :: (Either r b -> Bool) -> RedBlueStack r b -> (RedBlueStack r b, RedBlueStack r b)
partition _ (view -> Nothing) = (mempty, mempty)
partition p (view -> Just (x, xs))
    | p x       = (push x yes, no)
    | otherwise = (yes, push x no)
    where (yes, no) = partition p xs

-- | /O(n)/. Map both red and blue elements.
mapBoth :: (r -> r') -> (b -> b') -> RedBlueStack r b -> RedBlueStack r' b'
mapBoth _ _ Empty              = Empty
mapBoth f g (RBStack rs stack) = RBStack (fmap f rs) $ mapBoth g f stack

-- | /O(n)/. Map red elements only.
mapRed :: (r -> r') -> RedBlueStack r b -> RedBlueStack r' b
mapRed _ Empty                           = Empty
mapRed f (RBStack rs Empty)              = RBStack (fmap f rs) Empty
mapRed f (RBStack rs (RBStack bs stack)) = RBStack (fmap f rs) (RBStack bs (mapRed f stack))

-- | /O(n)/. map blue elements only.
mapBlue :: (b -> b') -> RedBlueStack r b -> RedBlueStack r b'
mapBlue f = recolour . mapRed f . recolour

-- | Right-associative fold over all elements.
foldrBoth :: (r -> m -> m) -> (b -> m -> m) -> m -> RedBlueStack r b -> m
foldrBoth _ _ x Empty              = x
foldrBoth f g x (RBStack rs stack) = foldr f (foldrBoth g f x stack) rs

-- | Left-associative fold over all elements.
foldlBoth :: (m -> r -> m) -> (m -> b -> m) -> m -> RedBlueStack r b -> m
foldlBoth _ _ x Empty              = x
foldlBoth f g x (RBStack rs stack) = foldlBoth g f (foldl f x rs) stack

-- | Right-associative fold of the red elements.
foldrRed :: (r -> m -> m) -> m -> RedBlueStack r b -> m
foldrRed _ x Empty                          = x
foldrRed f x (RBStack rs Empty)             = foldr f x rs
foldrRed f x (RBStack rs (RBStack _ stack)) = foldr f (foldrRed f x stack) rs

-- | Left-associative fold of the red elements.
foldlRed :: (m -> r -> m) -> m -> RedBlueStack r b -> m
foldlRed _ x Empty                          = x
foldlRed f x (RBStack rs Empty)             = foldl f x rs
foldlRed f x (RBStack rs (RBStack _ stack)) = foldlRed f (foldl f x rs) stack

-- | Right-associative fold of the blue elements.
foldrBlue :: (b -> m -> m) -> m -> RedBlueStack r b -> m
foldrBlue f x = foldrRed f x . recolour

-- | Left-associative fold of the blue elements.
foldlBlue :: (m -> b -> m) -> m -> RedBlueStack r b -> m
foldlBlue f x = foldlRed f x . recolour

-- | /O(n)/. Build a stack from a list.
fromList :: [Either r b] -> RedBlueStack r b
fromList = fromListWithRed mempty

-- | /O(n)/. Build a stack from a list with a given red prefix.
fromListWithRed :: Seq r -> [Either r b] -> RedBlueStack r b
fromListWithRed prefix []     = RBStack prefix Empty
fromListWithRed prefix (x:xs) = case x of
    Left r  -> fromListWithRed (prefix |> r) xs
    Right b -> RBStack prefix $ fromListWithBlue (Seq.singleton b) xs

-- | /O(n)/. Build a stack from a list with a given blue prefix
fromListWithBlue :: Seq b -> [Either r b] -> RedBlueStack b r
fromListWithBlue prefix []     = RBStack prefix Empty
fromListWithBlue prefix (x:xs) = case x of
    Left r  -> RBStack prefix $ fromListWithRed (Seq.singleton r) xs
    Right b -> fromListWithBlue (prefix |> b) xs

-- | /O(n)/. Write the contents of the stack in a list (preserving their order).
toList :: RedBlueStack r b -> [Either r b]
toList = Foldable.toList . toSeq

-- | /O(n)/. List all red items in the stack.
toRedList :: RedBlueStack r b -> [r]
toRedList = fst . toLists

-- | /O(n)/. List all blue items in the stack.
toBlueList :: RedBlueStack r b -> [b]
toBlueList = snd . toLists

-- | /O(n)/. Split the contents of the stack in a red and a blue list, each of
-- them preserving the order of elements.
toLists :: RedBlueStack r b -> ([r], [b])
toLists stack = let (rs, bs) = toSeqs stack
    in (Foldable.toList rs, Foldable.toList bs)

-- | /O(n)/. Build a stack from a 'Seq'.
fromSeq :: Seq (Either r b) -> RedBlueStack r b
fromSeq = fromList . Foldable.toList

-- | Convert a stack to a 'Seq'.
toSeq :: RedBlueStack r b -> Seq (Either r b)
toSeq Empty                           = mempty
toSeq (RBStack rs Empty)              = fmap Left rs
toSeq (RBStack rs (RBStack bs stack)) = fmap Left rs >< fmap Right bs >< toSeq stack

-- | Return a 'Seq' of all red items in the stack.
toRedSeq :: RedBlueStack r b -> Seq r
toRedSeq = fst . toSeqs

-- | Return a 'Seq' of all blue items in the stack.
toBlueSeq :: RedBlueStack r b -> Seq b
toBlueSeq = snd . toSeqs

-- | Separate the red from the blue items in (order-preserving) 'Seq's.
toSeqs :: RedBlueStack r b -> (Seq r, Seq b)
toSeqs Empty                           = (mempty, mempty)
toSeqs (RBStack rs Empty)              = (rs,     mempty)
toSeqs (RBStack rs (RBStack bs stack)) = let (rss, bss) = toSeqs stack
    in (rs >< rss, bs >< bss)
