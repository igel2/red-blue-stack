{-# LANGUAGE CPP #-}

-- | A Red-Blue-Stack behaves just like a normal stack. But it additionally
-- tags every pushed element with a colour (red or blue). It is possible to pop
-- the topmost (in the LIFO sense) red/blue element or the overall-top element
-- (no matter which colour it has been tagged with).
--
-- The tagging is done using the type system: A 'RedBlueStack' has two type
-- parameters: one for the red and one for the blue items. This way the type
-- system prevents us from mixing up red and blue items.
--
-- Whenever the /O/ notation is used, /n/ denotes the total number of elements
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
      -- * Deconstruction
    , view, viewRed, viewBlue
    , top, topRed, topBlue
    , pop, popRed, popBlue
      -- * Conversion
      -- ** Lists
    , fromList, toList, toLists
      -- ** Sequences
    , toSeq, toSeqs
    ) where

import qualified Data.Foldable as Foldable
import Data.Monoid
import Data.Ord
import Data.Sequence hiding (empty, fromList, singleton)
import qualified Data.Sequence as Seq
import Prelude hiding (length, null)
import Text.Read

-- | Red-blue-stack type. @r@ and @b@ are the types of red and blue items.
data RedBlueStack r b
    = Empty
    | RBStack (Seq r) (RedBlueStack b r) -- invariant: only first sequence may be empty

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
recolour Empty                     = Empty -- remove due to RULES?
recolour stack@(RBStack rs stack') = if null rs
    then stack'
    else RBStack mempty stack
{-# INLINE recolour #-}

-- TODO: caution wrt invariant!
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
-- the topmost red item in the stack and removes it from the stack. If the
-- stack doesn't contain any red item, 'Nothing' is returned.
viewRed :: RedBlueStack r b -> Maybe (r, RedBlueStack r b)
viewRed Empty               = Nothing
viewRed (RBStack rs1 stack) = case viewl rs1 of
    r :< rs -> Just (r, RBStack rs stack)
    EmptyL  -> case stack of
        RBStack bs (RBStack rs2 stack') -> case viewl rs2 of
            EmptyL  -> Nothing -- shouldn't happen...
            r :< rs -> if null rs
                then Just (r, recolour (pushMany bs stack'))
                else Just (r, recolour (RBStack bs (RBStack rs stack')))
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
toSeq Empty              = mempty
toSeq (RBStack rs stack) = (fmap Left rs) >< toSeqBlue stack
    where
    toSeqBlue Empty               = mempty
    toSeqBlue (RBStack bs stack') = (fmap Right bs) >< toSeq stack'

-- | Seperate the red from the blue items in (order-preserving) 'Seq's.
toSeqs :: RedBlueStack r b -> (Seq r, Seq b)
toSeqs Empty                           = (mempty, mempty)
toSeqs (RBStack rs Empty)              = (rs,     mempty)
toSeqs (RBStack rs (RBStack bs stack)) = let
    (rss, bss) = toSeqs stack
    in (rs >< rss, bs >< bss)

