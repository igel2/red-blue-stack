module Test.RedBlueStack
    ( testRedBlueStack
    ) where

import Data.Binary
import qualified Data.List as List
import Data.RedBlueStack
import Data.Sequence hiding ( drop, fromList, splitAt, take )
import Prelude hiding ( break, drop, dropWhile, filter, null, span, splitAt, take, takeWhile )
import Test.QuickCheck

type TestStack  = RedBlueStack Int Char
type TestEither = Either Int Char

testRedBlueStack :: IO ()
testRedBlueStack = do
    putStr "Invariants:                                     "
    quickCheck (checkInvariants :: TestStack -> Bool)
    putStr "read . show === id                              "
    quickCheck (readShowProperty :: TestStack -> Bool)
    putStr "decode . encode === id                          "
    quickCheck (binaryProperty :: TestStack -> Bool)
    putStr "recolour . recolour === id                      "
    quickCheck (recolourProperty :: TestStack -> Bool)
    putStr "view (push x stack) == Just (x, stack)          "
    quickCheck (pushViewProperty :: TestEither -> TestStack -> Bool)
    putStr "popRed                                          "
    quickCheck (popRedProperty :: TestStack -> Bool)
    putStr "popBlue                                         "
    quickCheck (popBlueProperty :: TestStack -> Bool)
    putStr "fromList . toList === id                        "
    quickCheck (listProperty :: TestStack -> Bool)
    putStr "toList (append s1 s2) == toList s1 ++ toList s2 "
    quickCheck (appendProperty :: TestStack -> TestStack -> Bool)
    putStr "split n s == (take n s, drop n s)               "
    quickCheck (splitProperty :: TestStack -> Int -> Bool)
    putStr "span/break/takeWhile/dropWhile                  "
    quickCheck (spanProperty prop :: TestStack -> Bool)
    putStr "partition/filter                                "
    quickCheck (partitionProperty prop :: TestStack -> Bool)
    return ()
    where
    prop (Left n)  = n `mod` 2 == 0
    prop (Right c) = 'A' < c

instance (Arbitrary r, Arbitrary b) => Arbitrary (RedBlueStack r b) where
    arbitrary = do
        len  <- choose (0, 100)
        list <- vector len
        return (fromList list)

checkInvariants :: RedBlueStack r b -> Bool
checkInvariants Empty              = True
checkInvariants (RBStack rs stack) = if null rs
    then checkInvariants' stack
    else checkInvariants stack
    where
    checkInvariants' :: RedBlueStack r b -> Bool
    checkInvariants' Empty              = True
    checkInvariants' (RBStack rs stack) = not (null rs) && checkInvariants' stack

readShowProperty :: (Eq r, Eq b, Read r, Read b, Show r, Show b) => RedBlueStack r b -> Bool
readShowProperty stack = read (show stack) == stack

binaryProperty :: (Eq r, Binary r, Eq b, Binary b) => RedBlueStack r b -> Bool
binaryProperty stack = let
    stack' = decode (encode stack)
    in checkInvariants stack' && stack' == stack

recolourProperty :: (Eq r, Eq b) => RedBlueStack r b -> Bool
recolourProperty stack = let
    stack' = recolour (recolour stack)
    in
    stack == stack' && checkInvariants stack'

pushViewProperty :: (Eq r, Eq b) => Either r b -> RedBlueStack r b -> Bool
pushViewProperty x stack = Just (x, stack) == view (push x stack)

popRedProperty :: (Eq r, Eq b) => RedBlueStack r b -> Bool
popRedProperty = popBlueProperty . recolour

popBlueProperty :: (Eq r, Eq b) => RedBlueStack r b -> Bool
popBlueProperty stack = let
    list   = List.filter (\x -> case x of { Left _ -> True ; _ -> False }) $ toList stack
    stack' = popAllBlue stack
    in
    maybe False (\stack' -> list == toList stack') (popAllBlue stack)
    where
    popAllBlue stack = case popBlue stack of
        Nothing     -> Just stack
        Just stack' -> if checkInvariants stack'
            then popAllBlue stack'
            else Nothing

listProperty :: (Eq r, Eq b) => RedBlueStack r b -> Bool
listProperty stack = let
    list   = toList stack
    stack' = fromList list
    in
    checkInvariants stack' && stack == stack'

appendProperty :: (Eq r, Eq b) => RedBlueStack r b -> RedBlueStack r b -> Bool
appendProperty stack1 stack2 = let
    stack12 = stack1 `append` stack2
    in
    checkInvariants stack12 && toList stack12 == toList stack1 ++ toList stack2

splitProperty :: (Eq r, Eq b) => RedBlueStack r b -> Int -> Bool
splitProperty stack n = let
    (stack1, stack2) = splitAt n stack
    in
    checkInvariants stack1 && checkInvariants stack2
        && stack1 `append` stack2 == stack
        && stack1 == take n stack
        && stack2 == drop n stack

spanProperty :: (Eq r, Eq b) => (Either r b -> Bool) -> RedBlueStack r b -> Bool
spanProperty p stack = let
    (stack1, stack2) = span p stack
    redP             = p . Left
    blueP            = p . Right
    in
    checkInvariants stack1 && checkInvariants stack2
        && stack1 == takeWhile p stack
        && stack2 == dropWhile p stack
        && (stack1, stack2) == break (not . p) stack
        && foldlBoth (&&) (&&) True (mapBoth redP blueP stack1)
        && (case view stack2 of
            Nothing     -> True
            Just (x, _) -> not $ p x)

partitionProperty :: (Eq r, Eq b) => (Either r b -> Bool) -> RedBlueStack r b -> Bool
partitionProperty p stack = let
    (stack1, stack2) = partition p stack
    in
    (filter p stack, filter (not . p) stack) == (stack1, stack2)
        && (List.partition p (toList stack)) == (toList stack1, toList stack2)

