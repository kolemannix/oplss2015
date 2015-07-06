{-# OPTIONS --no-termination-check #-}

module IR.McCarthy91 where

open import IType.Nat
open import IType.Bool

-- McCarthy's 91-function, a nested recursive function

mc91 : Nat → Nat
mc91 n = if (n < 101) then mc91 (mc91 (n + 11)) else n - 11

-- The Bove-Capretta method yields an inductive-recursive function

mutual
  data D : Nat → Set where
    base : (n : Nat)
      → So (¬ (n < 101))
      → D n
    nest : (n : Nat)
      → So (n < 101)
      → (p : D (n + 11))
      → D (mc91bc (n + 11) p)
      → D n
    
  mc91bc : (n : Nat) → D n → Nat
  mc91bc n (base .n x)     = n - 11
  mc91bc n (nest .n x p q) = mc91bc (mc91bc (n + 11) p) q

-- Relation implementation

data Mc91 : Nat → Nat → Set where
  base : (n : Nat)
    → So (¬ (n < 101))
    → Mc91 n (n - 11)
  nest : (n m r : Nat)
    → Mc91 (n + 11) m
    → Mc91 m r
    → Mc91 n r

  
    
