{-# LANGUAGE RankNTypes, FlexibleContexts #-}

-- Inspired by Stephen Diehl's post on adjunctions http://www.stephendiehl.com/posts/adjunctions.html
import Data.Function

type Nat f g = forall a. f a -> g a

-- This is simply morphism composition
vert :: Nat g h -> Nat f g -> Nat f h
vert a b = a . b

-- Horizontal composition.
type NatComp f f' g g' = forall a. f' (f a) -> g' (g a)

-- These are simply two ways of defining horizontal composition.
horiz1 :: (Functor f, Functor f', Functor g, Functor g') =>
         Nat f' g' -> Nat f g -> NatComp f f' g g'
horiz1 a b = a . fmap b

horiz2 :: (Functor f, Functor f', Functor g, Functor g') =>
          Nat f' g' -> Nat f g -> NatComp f f' g g'
horiz2 a b = fmap b . a

-- See the above huge type signatures? They're also hard to write.
-- Let's define some type synonyms to tell GHC where the foralls are needed.

newtype Nat2 f g = N (Nat f g)
vertN :: Nat2 g h -> Nat2 f g -> Nat2 f h
vertN (N a) (N b) = N $ a . b

newtype NatComp2 f f' g g' = NC (NatComp f f' g g')

horiz1N (N a) (N b) = NC $ a . fmap b
horiz2N (N a) (N b) = NC $ fmap b . a

-- Let's write some equalities which we want to state. TODO: test them using
-- QuickCheck.

f1 :: (Functor f, Functor f', Functor g, Functor g') => Nat h' g' -> Nat f' h' -> Nat h g -> Nat f h -> NatComp f f' g g'
f1 a b a' b' = (a `vert` b) `horiz2` (a' `vert` b')

f2 :: (Functor f, Functor f', Functor g, Functor g', Functor h, Functor h') => Nat h' g' -> Nat f' h' -> Nat h g -> Nat f h -> NatComp f f' g g'
f2 a b a' b' = (a `horiz2` a') . (b `horiz2` b')

f :: Eq (NatComp2 f f' g g') => (Functor f, Functor f', Functor g, Functor g', Functor h, Functor h') => Nat h' g' -> Nat f' h' -> Nat h g -> Nat f h -> Bool
f a b a' b' = ((==) `on` NC) ((a . b) `horiz2` (a' . b')) ((a `horiz2` a') . (b `horiz2` b'))

-- Doesn't work because of the difference between N and NC.
-- fN a b a' b' = (==) ((a `vertN` b) `horiz2N` (a' `vertN` b')) ((a `horiz2N` a') `vertN` (b `horiz2N` b'))

-- testOrig a b a' b' = (a . b) `vert` (a' . b') == (a `horiz2N` a') . (b `horiz2N` b')
