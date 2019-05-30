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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}

module Data.Sheet where

import Control.Comonad
import Data.Distributive
import Data.Functor.Rep
import Data.Finite
import qualified Data.Vector.Sized as V
import GHC.TypeNats
import Data.Kind
import Data.Function
import Control.Applicative

data Sheet columns a where
 (:+:) :: f a -> Sheet xs a -> Sheet (f : xs) a
 FinalCol :: f a -> Sheet '[f] a

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

instance (AllC Functor (j:xs), AllC Representable (j : xs), Representable (Sheet xs), Rep (Sheet xs) ~ Ref xs)
    => Distributive (Sheet (j : xs)) where
    distribute = distributeRep

instance (AllC Functor (j:xs), AllC Representable (j : xs), Representable (Sheet xs), Rep (Sheet xs) ~ Ref xs)
    => Representable (Sheet (j : xs)) where
    type Rep (Sheet (j : xs)) = Ref (j : xs)

    index (x :+: xs) (Y r) = index x r
    index (_ :+: xs) (N r) = index xs r
    tabulate f = tabulate (f . down) :+: tabulate (f . up)
      where
        down = Y
        up = N

instance {-# OVERLAPPING #-} (Functor k, Representable k) => Distributive (Sheet '[k]) where
    distribute = distributeRep

instance {-# OVERLAPPING #-} (Functor k, Representable k) => Representable (Sheet '[k]) where
    type Rep (Sheet '[k]) = Ref '[k]

    index (FinalCol x) (Y r) = index x r
    tabulate f = FinalCol $ tabulate (f . Y)


---------------------------


data Rows k n a = Rows (V.Vector n a)
  deriving stock Show
  deriving anyclass ShowX
  deriving Functor
-- deriving instance (Show a) => Show (Rows k n a)

data Single k a = Single a
  deriving stock Show
  deriving anyclass ShowX
  deriving (Functor)

-- instance Functor (Rows k n) where
--   fmap f (Rows v) = Rows $ fmap f v

instance (KnownNat n) => Distributive (Rows k n) where
  distribute = distributeRep

instance (KnownNat n) => Representable (Rows k n) where
  type Rep (Rows k n) = Finite n
  index (Rows v) n = V.index v n
  tabulate f = Rows $ V.generate f

instance Distributive (Single k) where
  distribute = distributeRep

instance Representable (Single k) where
  type Rep (Single k) = ()
  index (Single v) () = v
  tabulate f = Single $ f ()

data Columns = Items | Prices | Total
-- data Prices

-- s :: Sheet '[Items 3] Char
-- s = tabulate go
--   where
--     go :: Ref '[Items 3] -> Char
--     go (Y 0) = 'A'
--     go (Y 1) = 'B'
--     go (Y 2) = 'C'

-- pattern ItemsP :: forall n xs. Ref xs -> RowI Items n
pattern ItemsP :: forall n xs. Inject (RowI Items n) xs => Finite n -> Ref xs
pattern ItemsP n <- (flatten -> RowI n :: RowI Items n)
-- pattern inject (Inj :: Inj Items, n) <- ItemsP n


q :: Sheet '[Rows Items 3, Rows Prices 3, Single Total] Double
q = fix $ \w -> tabulate (go w)
  where
    go :: Sheet '[Rows 'Items 3, Rows 'Prices 3, Single 'Total] Double
       -> Ref '[Rows Items 3, Rows Prices 3, Single Total]
       -> Double
    -- go _ (ItemsP @3 0) = 10
    go _ (Y 1) = 20
    go _ (Y 2) = 30

    go _ (N (Y 0)) = 5
    go _ (N (Y 1)) = 10
    go _ (N (Y 2)) = 15

    go w (N (N (Y ()))) =
        let items = index w . Y <$> [0..]
            costs = index w . Y <$> [0..]
         in sum $ zipWith (*) items costs

data RowI d n = RowI (Finite n)
data SingleI d = SingleI
items :: KnownNat n => Int ->  RowI Items n
items = RowI . finite . toInteger
prices :: KnownNat n => Int ->  RowI Prices n
prices = RowI . finite . toInteger
total :: SingleI Total
total = SingleI

index' :: (Representable (Sheet xs), Inject d ys, Rep (Sheet xs) ~ Ref ys)
       => Inject d xs
       => Sheet xs a
       -> d
       -> a
index' w i = index w (inject i)

class Inject x xs where
  inject :: x -> Ref xs
  flatten :: Ref xs -> x

-- instance (x ~ Rep f) => Inject (Inj d, Finite n) '[Rows d n] where
--   inject (_, n) = Y n

instance {-# OVERLAPPING #-} Inject (RowI d n) (Rows d n : ys) where
  inject (RowI n) = Y n
  flatten (Y n) = (RowI n)

instance (Inject thing xs) => Inject thing (x : xs) where
  inject thing = N $ inject thing
  flatten (N r) = flatten r

instance {-# OVERLAPPING #-} Inject (SingleI d) (Single d : ys) where
  inject _ = Y ()
  flatten _ = SingleI

-- instance (Inject (Ref '[x]) ys) => Inject x (y : ys) where
--   inject = inject . N


-- sheet :: Sheet '[Rows ]'


-- r :: Sheet '[Rows Items 3] Char
-- r = FinalCol $ Rows (V.fromTuple ('a', 'b', 'c'))

data family Reff (r :: k) :: *
data instance Reff Items = ItemsR Int


-- data Reff k n r = Reff r

-- class Match columns col xs where
--   index' :: Sheet xs a -> Reff col -> a
--   tabulate' :: (Reff col -> a) -> Sheet xs a

-- instance (Representable col, Rep col ~ Reff col) => Match col '[col] where
--   index' (FinalCol c) r = index c r
--   tabulate' f = FinalCol $ tabulate f

-- instance (Representable col, Rep col ~ Reff col, Rep (Sheet xs)) => Match col (col:xs) where
--   index' (c :+: _) r = index c r
--   tabulate' f = tabulate f :+: tabulate f
