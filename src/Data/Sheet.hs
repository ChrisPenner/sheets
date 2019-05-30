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
 (:+:) :: Rows k sz a -> Sheet xs a -> Sheet (Rows k sz : xs) a
 FinalCol :: Rows k sz a -> Sheet '[Rows k sz] a

infix 6 :+:

data Ref columns where
 Y :: Rep x -> Ref (x:xs)
 N :: Ref xs -> Ref (x:xs)

instance Functor (Sheet cols) where
  fmap f (FinalCol x) = FinalCol $ fmap f x
  fmap f (fa :+: rest) = fmap f fa :+: (fmap f rest)

type family AllC (c :: k -> Constraint) (xs :: [k]) = (r :: Constraint) where
  AllC _ '[] = ()
  AllC c (x:xs) = (c x, AllC c xs)

class (forall a. Show a => Show (f a)) => ShowX f

deriving instance (AllC ShowX cols, Show a) => Show (Sheet cols a)

data Rows k n a = Rows (V.Vector n a)
  deriving stock Show
  deriving anyclass ShowX
-- deriving instance (Show a) => Show (Rows k sz a)

instance Functor (Rows k sz) where
  fmap f (Rows v) = Rows $ fmap f v

instance (KnownNat n) => Distributive (Rows k n) where
  distribute = distributeRep

instance (KnownNat n) => Representable (Rows k n) where
  type Rep (Rows k n) = Finite n
  index (Rows v) n = V.index v n
  tabulate f = Rows $ V.generate f


instance (KnownNat sz, Representable (Sheet xs), Rep (Sheet xs) ~ Ref xs)
    => Distributive (Sheet (Rows j sz : xs)) where
    distribute = distributeRep

instance (KnownNat sz, Representable (Sheet xs), Rep (Sheet xs) ~ Ref xs)
    => Representable (Sheet (Rows j sz : xs)) where
    type Rep (Sheet (Rows j sz : xs)) = Ref (Rows j sz : xs)

    index (Rows x :+: xs) (Y r) = index x r
    index (_ :+: xs) (N r) = index xs r
    tabulate f = tabulate (f . down) :+: tabulate (f . up)
      where
        down = Y
        up = N

instance {-# OVERLAPPING #-} (KnownNat sz) => Distributive (Sheet '[Rows k sz]) where
    distribute = distributeRep

instance {-# OVERLAPPING #-} (KnownNat sz) => Representable (Sheet '[Rows k sz]) where
    type Rep (Sheet '[Rows k sz]) = Ref '[ Rows k sz ]

    index (FinalCol x) (Y r) = index x r
    tabulate f = FinalCol $ tabulate (f . Y)

data Items

-- s :: Sheet '[Rows Items 3] Char
-- s = tabulate go
--   where
--     go :: Ref '[Rows Items 3] -> Char
--     go (Y 0) = 'A'
--     go (Y 1) = 'B'
--     go (Y 2) = 'C'

-- r :: Sheet '[Rows Items 3] Char
-- r = FinalCol $ Rows (V.fromTuple ('a', 'b', 'c'))
