{-# LANGUAGE RankNTypes, FlexibleContexts, DeriveFunctor, NoMonomorphismRestriction #-}

-- Inspired by Stephen Diehl's post on adjunctions http://www.stephendiehl.com/posts/adjunctions.html
import Data.Function

type Nat f g = forall a. f a -> g a

-- XXX Should arguably reuse the package defining this. But this is a
-- self-contained file, so cleaning this up required setting up a Cabal project,
-- so off the plan (with good tool support, which maybe exists, this argument
-- would be invalid).
newtype Compose f g a = C { unC :: f (g a) }
  deriving Functor

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

-- XXX probably this definition should be nuked, simply because we later need to
-- convert away from it - the composition of two Nats should be a Nat.
newtype NatComp2 f f' g g' = NC (NatComp f f' g g')

type NatComp3 f f' g g' = Nat2 (Compose f' f) (Compose g' g)
-- Show they are isomorphic
nC2to3 :: NatComp2 f f' g g' -> NatComp3 f f' g g'
nC2to3 (NC f) = N $ C . f . unC
nC3to2 :: NatComp3 f f' g g' -> NatComp2 f f' g g'
nC3to2 (N f) = NC $ unC . f . C

horiz1NC (N a) (N b) = NC $ a . fmap b
horiz2NC (N a) (N b) = NC $ fmap b . a

horiz2N a b = nC2to3 $ horiz2NC a b
-- Or equivalently:
--horiz2N = (nC2to3 .) . horiz2NC

-- Let's write some equalities which we want to state.
--
-- These equalities come from the above blog post; they are the so-called
-- *interchange law*. However, the blog post gets it wrong.
--
-- TODO: test them using
-- QuickCheck. But maybe QuickCheck produces non-parametric instances? Hm...
-- Also, can QuickCheck compare functions? (I guess on some inputs...)

-- However, stating the interchange law as checkable predicate is hard, simply because we need to assume an instance of Eq on functions...

-- XXX rename f to interchange.

-- First failed attempt.
-- Auxiliary definitions:
f1 :: (Functor f, Functor f', Functor g, Functor g') => Nat h' g' -> Nat f' h' -> Nat h g -> Nat f h -> NatComp f f' g g'
f1 a b a' b' = (a `vert` b) `horiz2` (a' `vert` b')

f2 :: (Functor f, Functor f', Functor g, Functor g', Functor h, Functor h') => Nat h' g' -> Nat f' h' -> Nat h g -> Nat f h -> NatComp f f' g g'
f2 a b a' b' = (a `horiz2` a') . (b `horiz2` b')

-- Main definition.
-- Does not work - the type signature is illegal.
--f' :: (Eq (f' (f a0) -> g' (g a0)), Functor f, Functor f', Functor g, Functor g', Functor h, Functor h') => Nat h' g' -> Nat f' h' -> Nat h g -> Nat f h -> Bool
--f' :: (Eq (NatComp f f' g g'), Functor f, Functor f', Functor g, Functor g', Functor h, Functor h') => Nat h' g' -> Nat f' h' -> Nat h g -> Nat f h -> Bool
--f' a b a' b' = f1 a b a' b' == f2 a b a' b'

-- Second failed attempt - it almost works, but it uses (.) instead of vertical
-- composition, like in the original blog post, which also says that one of
-- horiz is vertical composition.
f :: (Eq (NatComp2 f f' g g'), Functor f, Functor f', Functor g, Functor g', Functor h, Functor h') => Nat h' g' -> Nat f' h' -> Nat h g -> Nat f h -> Bool
f a b a' b' = ((==) `on` NC) ((a . b) `horiz2` (a' . b')) ((a `horiz2` a') . (b `horiz2` b'))

-- Final statement, which typechecks and uses both horizontal and vertical
-- composition.

-- It only works after we convert between N and NC
fN
  :: (Eq (NatComp3 f f' g g'), Functor g', Functor h') =>
     Nat2 h' g' -> Nat2 f' h' -> Nat2 h g -> Nat2 f h -> Bool

fN a b a' b' = (a `vertN` b) `horiz2N` (a' `vertN` b') == (a `horiz2N` a') `vertN` (b `horiz2N` b')

-- testOrig a b a' b' = (a . b) `vert` (a' . b') == (a `horiz2N` a') . (b `horiz2N` b')
