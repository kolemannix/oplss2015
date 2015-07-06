{-# OPTIONS --no-positivity-check #-}

module IType.NegativeData where

data Λ : Set where
  lam : (Λ → Λ) → Λ

app : Λ → Λ → Λ
app (lam f) a = f a





