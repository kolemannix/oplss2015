module Semantics.TypingJudgments where

open import IType.Nat
open import Semantics.SyntaxComputationRulesITT

data isN : F zero → Set where
  zeroN : {a : F zero} → a => zeroV → isN a
  succN : {a b : F zero} → a => succV b → isN b → isN a

-- an inductive-recursive definition!

mutual
  data isset : F zero → Set where    
    piset : {A : F zero} → (B : F zero) → (C : F one)
      → A => piV B C
      → (p : isset B)
      → ((x : F zero) → isel x B p → isset (C [ x ]))
      → isset A
    Nset : {A : F zero}
      → A => NV
      → isset A
    
  isel : F zero → (A : F zero) → isset A → Set
  isel a A (piset B C d p q)
    = (x : F zero)
    → (y : isel x B p)
    → isel (a # x) (C [ x ]) (q x y)
  isel a A (Nset x) = isN a

mutual 
  data isTy : F zero → Set where
    piTy : {A : F zero} → (B : F zero) → (C : F one)
      → A => piV B C
      → (p : isTy B)
      → ((x : F zero) → isTm x B p → isTy (C [ x ]))
      → isTy A
    setTy : {A : F zero}
      → A => setV
      → isTy A
    NTy : {A : F zero}
      → A => NV
      → isTy A

  isTm : F zero → (A : F zero) → isTy A → Set
  isTm a A (piTy B C d p q)
    = (b : F zero)
    → (y : isTm b B p)
    → isTm (a # b) (C [ b ]) (q b y)
  isTm a A (setTy x) = isset a
  isTm a A (NTy x) = isN a

-- Meaning of hypothetical judgments.
-- The meaning x : A ⊢ b : B is the same as the meaning of
-- λ x → b : (x : A) → B, etc
-- The meaning of x : A ⊢ B is?

-- Exercise: extend the model with more types, e g Bool, Sigma, +, W,
-- Exercise: write meanings of equality judgments
-- Exercise: write meanings of the identity type

