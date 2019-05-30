{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Data.HRep where

import Data.List

class HRepresentable f g | f -> g where
  type HRep f
  hIndex :: f a -> (HRep f) -> g a
  hTabulate :: (HRep f -> g a) -> f a

instance HRepresentable [] Maybe where
  type HRep [] = Int
  hIndex xs n | n < 0 || n > length xs = Nothing
  hIndex xs n = Just $ xs !! n
  hTabulate f = unfoldr go 0
    where
      go n = (,) <$> (f n) <*> pure (n+1)


less10 :: Int -> Maybe Int
less10 n | n < 10 = Just n
         | otherwise = Nothing

