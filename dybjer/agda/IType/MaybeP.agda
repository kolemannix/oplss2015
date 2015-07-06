module IType.MaybeP (A : Set) where

data Maybe : Set where
  just    : A → Maybe
  nothing : Maybe
