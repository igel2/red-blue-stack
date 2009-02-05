{-# LANGUAGE CPP, DeriveDataTypeable #-}

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
-- stack would have /r = 2/ and /b = 0/.
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
    , recolour
    , push, pushRed, pushBlue
    , append
      -- * Deconstruction
      -- ** Views
    , view, viewRed, viewBlue
    , top, topRed, topBlue
    , pop, popRed, popBlue
      -- ** Substacks
    , take, drop, splitAt
    , takeWhile, dropWhile, span, break
      -- * Map
    , mapBoth, mapRed, mapBlue
      -- * Fold
    , foldrBoth, foldlBoth
    , foldrRed,  foldlRed
    , foldrBlue, foldlBlue
      -- * Conversion
      -- ** Lists
    , fromList, toList, toLists
      -- ** Sequences
    , toSeq, toSeqs
    ) where

import Control.Exception (assert)
import Data.Foldable as Foldable hiding (toList)
import qualified Data.Foldable as Foldable
import Data.Monoid
import Data.Ord
import Data.Sequence hiding (drop, empty, fromList, singleton, splitAt, take)
import qualified Data.Sequence as Seq
import Data.Typeable
import Prelude hiding
    ( break, drop, dropWhile, foldl, foldr, length, null, span, splitAt, take
    , takeWhile )
import Text.Read

-- | Red-blue-stack type. @r@ and @b@ are the types of red and blue items.
data RedBlueStack r b
    = Empty
    | RBStack (Seq r) (RedBlueStack b r) -- invariant: only first sequence may be empty
    deriving (Typeable)

instance (Show r, Show b) => Show (RedBlueStack r b) where
    show = ("fromList " ++) . show . toList

instance (Read r, Read b) => Read (RedBlueStack r b) where
#ifdef __GLASGOW_HASKELL__
    readPrec = parens $ prec 10 $ do
        Ident "fromList" <- lexP
        xs               <- readPrec
        return (fromList xs)
    readListPrec = readListPrecDefault
#else
    readsPrec p = readParen (p > 10) $ \r -> do
        ("fromList", s) <- lex r
        (xs, t)         <- reads s
        return (fromList xs, t)
#endif

instance (Eq r, Eq b) => Eq (RedBlueStack r b) where
    stack1 == stack2 = (toList stack1) == (toList stack2)

instance (Ord r, Ord b) => Ord (RedBlueStack r b) where
    compare = comparing toList

instance Monoid (RedBlueStack r b) where
    mempty  = empty
    mappend = append

instance Functor (RedBlueStack r) where
    fmap = mapBlue

instance Foldable.Foldable (RedBlueStack r) where
    foldr = foldrBlue
    foldl = foldlBlue

-- | /O(1)/. Find out if the stack is empty.
isEmpty :: RedBlueStack r b -> Bool
isEmpty Empty              = True
isEmpty (RBStack rs stack) = null rs && isEmpty stack -- invariant => max. one recursion => O(1)

-- | /O(n)/. Count the elements in the stack.
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
redSingleton r = RBStack (Seq.singleton r) empty

-- | /O(1)/. Singleton stack holding a blue item.
blueSingleton :: b -> RedBlueStack r b
blueSingleton = recolour . redSingleton

-- | /O(1)/. Swaps the colours of all items.
recolour :: RedBlueStack r b -> RedBlueStack b r
recolour Empty                     = Empty
recolour stack@(RBStack rs stack') = if null rs
    then stack'
    else RBStack mempty stack
{-# INLINE recolour #-}
{-# RULES "recolour/recolour" forall s. recolour (recolour s) = s #-}

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

-- | /O(n)/ (length of the first stack). Appends the elements of the 2nd stack
-- to the first, so that @append s1 s2 == fromList (toList s1 ++ toList s2)@.
append :: RedBlueStack r b -> RedBlueStack r b -> RedBlueStack r b
append stack1              Empty               = stack1
append Empty               stack2              = stack2
append (RBStack rs1 Empty) (RBStack rs2 tail2) = RBStack (rs1 >< rs2) tail2
append (RBStack rs1 blue1@(RBStack bs1 tail1)) stack2@(RBStack rs2 tail2)
    | null rs2  = RBStack rs1 (append blue1 tail2)
    | otherwise = RBStack rs1 (RBStack bs1 (append tail1 stack2))

-- | /O(1)/. Finds the top item of the stack, whatever it colour it is tagged
-- with. Returns this item and the stack with that item removed or 'Nothing' if
-- the stack was empty.
view :: RedBlueStack r b -> Maybe (Either r b, RedBlueStack r b)
view Empty               = Nothing
view (RBStack rss stack) = case viewl rss of
    r :< rs -> Just (Left r, RBStack rs stack)
    EmptyL  -> case view stack of
        Nothing          -> Nothing
        Just (b, stack') -> Just (either Right Left b, recolour stack')
{-# INLINE view #-}

-- | /O(1)/ for the top element and /O(log r)/ for the remaining stack. Finds
-- the topmost red item in the stack and removes it from the stack. If the stack
-- doesn't contain any red item, 'Nothing' is returned.
viewRed :: RedBlueStack r b -> Maybe (r, RedBlueStack r b)
viewRed Empty               = Nothing
viewRed (RBStack rs1 stack) = case viewl rs1 of
    r :< rs -> Just (r, RBStack rs stack)
    EmptyL  -> case stack of
        RBStack bs (RBStack rs2 stack') -> case viewl rs2 of
            r :< rs -> if null rs
                then Just (r, recolour (pushMany bs stack'))
                else Just (r, recolour (RBStack bs (RBStack rs stack')))
            EmptyL  -> assert False Nothing -- only the 1st, not the 3rd Seq may be empty!
        _                               -> Nothing
    where
    pushMany :: Seq r -> RedBlueStack r b -> RedBlueStack r b
    pushMany rs Empty              = RBStack rs Empty
    pushMany rs (RBStack rs' rest) = RBStack (rs >< rs') rest
{-# INLINE viewRed #-}

-- | /O(1)/ for the top element and /O(log b)/ for the remaining stack. Finds
-- the topmost blue item in the stack and removes it from the stack. If the
-- stack doesn't contain any blue item, 'Nothing' is returned.
viewBlue :: RedBlueStack r b -> Maybe (b, RedBlueStack r b)
viewBlue stack = case viewRed (recolour stack) of
    Nothing          -> Nothing
    Just (x, stack') -> Just (x, recolour stack')
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
splitAt _ Empty = (empty, empty)
splitAt n (RBStack rs stack)
    | n >= redLength = let
        (first, remaining) = splitAt (n - redLength) stack
        in (RBStack rs Empty `append` recolour first, recolour remaining)
    | otherwise      = let
         (rs', rs'') = Seq.splitAt n rs
         in (RBStack rs' Empty, RBStack rs'' stack)
    where
    redLength = length rs

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
span p stack = case view stack of
    Nothing      -> (empty, empty)
    Just (x, xs) -> if p x
        then let (yes, no) = span p xs in (push x yes, no)
        else (empty, stack)

-- | /O(n)/. Returns a tuple of 'RedBlueStack's. The first is the longest prefix
-- /not/ fulfilling the predicate, the second one is the rest of the
-- 'RedBlueStack'. @ 'break' p = 'span' ('not' . p) @.
break :: (Either r b -> Bool) -> RedBlueStack r b -> (RedBlueStack r b, RedBlueStack r b)
break p = span (not . p)

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

-- | /O(log n)/. Build a stack from a list.
fromList :: [Either r b] -> RedBlueStack r b
fromList = Foldable.foldr' push empty

-- | /O(n)/. Write the contents of the stack in a list (preserving their order).
toList :: RedBlueStack r b -> [Either r b]
toList = Foldable.toList . toSeq

-- | /O(n)/. Split the contents of the stack in a red and a blue list, each of
-- them preserving the order of elements.
toLists :: RedBlueStack r b -> ([r], [b])
toLists stack = let (rs, bs) = toSeqs stack
    in (Foldable.toList rs, Foldable.toList bs)


-- | Convert a stack to a 'Seq'.
toSeq :: RedBlueStack r b -> Seq (Either r b)
toSeq Empty                           = mempty
toSeq (RBStack rs Empty)              = fmap Left rs
toSeq (RBStack rs (RBStack bs stack)) = fmap Left rs >< fmap Right bs >< toSeq stack

-- | Separate the red from the blue items in (order-preserving) 'Seq's.
toSeqs :: RedBlueStack r b -> (Seq r, Seq b)
toSeqs Empty                           = (mempty, mempty)
toSeqs (RBStack rs Empty)              = (rs,     mempty)
toSeqs (RBStack rs (RBStack bs stack)) = let
    (rss, bss) = toSeqs stack
    in (rs >< rss, bs >< bss)
