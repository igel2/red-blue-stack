module Test.RedBlueStack
    ( testRedBlueStack
    ) where

import Data.RedBlueStack
import Data.Sequence hiding (fromList)
import Prelude hiding (null)
import Test.QuickCheck

type TestStack  = RedBlueStack Int Char
type TestEither = Either Int Char

testRedBlueStack :: IO ()
testRedBlueStack = do
    putStr "Invariants:                             "
    quickCheck (checkInvariants :: TestStack -> Bool)
    putStr "read . show === id                      "
    quickCheck (readShowProperty :: TestStack -> Bool)
    putStr "recolour . recolour === id              "
    quickCheck (recolourProperty :: TestStack -> Bool)
    putStr "view (push x stack) == Just (x, stack)  "
    quickCheck (pushViewProperty :: TestEither -> TestStack -> Bool)
    putStr "popRed                                  "
    quickCheck (popRedProperty :: TestStack -> Bool)
    putStr "popBlue                                 "
    quickCheck (popBlueProperty :: TestStack -> Bool)
    return ()

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
    list   = filter (\x -> case x of { Left _ -> True ; _ -> False }) $ toList stack
    stack' = popAllBlue stack
    in
    list == toList stack' && checkInvariants stack'
    where
    popAllBlue stack = case popBlue stack of
        Nothing     -> stack
        Just stack' -> popAllBlue stack'

