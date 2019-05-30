{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
module Data.Sheet where

import Control.Comonad
import Data.Distributive
import Data.Functor.Rep
import Data.Finite
import qualified Data.Vector.Sized as V
import GHC.TypeNats
import Data.Kind

data Sheet columns a where
 (:+:) :: x a -> Sheet xs a -> Sheet (x:xs) a
 FinalCol :: x a -> Sheet '[x] a

infix 6 :+:

data Ref columns where
 Y :: Rep x -> Ref (x:xs)
 N :: Ref xs -> Ref (x:xs)

instance (AllC Functor cols) => Functor (Sheet cols) where
  fmap f (FinalCol x) = FinalCol $ fmap f x
  fmap f (fa :+: rest) = fmap f fa :+: (fmap f rest)

type family AllC (c :: k -> Constraint) (xs :: [k]) = (r :: Constraint) where
  AllC _ '[] = ()
  AllC c (x:xs) = (c x, AllC c xs)

class (forall a. Show a => Show (f a)) => ShowX f

deriving instance (AllC ShowX cols, Show a) => Show (Sheet cols a)

-- data Size =
--   Dyn | Sz Int

data Rows k sz a where
  -- DynRows :: [a] -> Rows k Nothing a
  Rows :: V.Vector n a -> Rows k n a
  deriving anyclass ShowX

deriving instance (Show a) => Show (Rows k sz a)

instance Functor (Rows k sz) where
  fmap f (Rows v) = Rows $ fmap f v

instance (KnownNat n) => Distributive (Rows k n) where
  distribute = distributeRep

instance (KnownNat n) => Representable (Rows k n) where
  type Rep (Rows k n) = Finite n
  index (Rows v) n = V.index v n
  tabulate f = Rows $ V.generate f


instance ( AllC Functor (x : y : xs)
         , AllC Representable (x : y : xs)
         , Representable (Sheet (y : xs))
         , Rep (Sheet (y : xs)) ~ Ref (y : xs)
         ) => Distributive (Sheet (x : y : xs)) where
    distribute = distributeRep

instance ( AllC Functor (x : y : xs)
         , AllC Representable (x : y : xs)
         , Rep (Sheet (y : xs)) ~ Ref (y : xs)
         , (Representable (Sheet (y : xs)))
         ) => Representable (Sheet (x : y : xs)) where
    type Rep (Sheet (x : y : xs)) = Ref (x : y : xs)

    index (x :+: xs) (Y r) = index x r
    index (x :+: xs) (N r) = index xs r
    tabulate f = tabulate (f . down) :+: tabulate (f . up)
      where
        down :: Rep x -> Ref (x : y : xs)
        down = Y
        up :: Ref (y : xs) -> Ref (x : y : xs)
        up = N

instance (Functor x, Representable x) => Distributive (Sheet '[x]) where
    distribute = distributeRep

instance (Representable x) => Representable (Sheet '[x]) where
    type Rep (Sheet '[x]) = Ref '[x]

    index (x :+: xs) (Y r) = index x r
    tabulate f = FinalCol $ tabulate (f . Y)
      where
        down :: Rep x -> Ref (x : y : xs)
        down = Y
        up :: Ref (y : xs) -> Ref (x : y : xs)
        up = N

-- instance Representable (Sheet '[x]) where
--   type Rep (Sheet cs) = Ref cs
--   index (FinalCol x) (FinalRef r) = index x r
--   tabulate f = Rows $ V.generate f




-- instance Representable (Rows k Nothing) where
--   type Rep (Rows k Nothing) = Int
--   index (DynRows xs) n = xs !! n
--   tabulate f = DynRows $ generate (f . fromIntegral . getFinite)




data Items

s :: Sheet '[Rows Items 3] Char
s = tabulate go
  where
    go :: Ref '[Rows Items 3] -> Char
    go (Y 0) = 'A'
    go (Y 1) = 'B'
    go (Y 2) = 'C'

r :: Sheet '[Rows Items 3] Char
r = FinalCol $ Rows (V.fromTuple ('a', 'b', 'c'))
