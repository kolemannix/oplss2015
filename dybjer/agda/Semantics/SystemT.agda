module Semantics.SystemT where

open import IType.Nat
open import IFam.Fin
open import IFam.Vector renaming (_::_ to cons)

data Ty : Set where
  NF    : Ty
  _⇒_ : Ty → Ty → Ty

Ctx : Nat → Set
Ctx n = Vect Ty n

infixr 60 _⇒_

-- the set of n-place functions following Aczel

data F : Nat → Set where
  var   : {n : Nat} → Fin n → F n
  _#_   : {n : Nat} → F n → F n → F n -- application
  lam   : {n : Nat} → F (succ n) → F n
  zeroF : {n : Nat} → F n
  succF : {n : Nat} → F n
  recF  : {n : Nat} → F n

-- syntactic typing

data _⊢_∈_ : {n : Nat} → Ctx n → F n → Ty → Set where
  var-ty : {n : Nat} → {Γ : Ctx n} → {i : Fin n}
    → Γ ⊢ var i ∈ lookup i Γ
  app-ty : {n : Nat} → {Γ : Ctx n} → {A B : Ty} → {c a : F n}
    → Γ ⊢ c ∈ A ⇒ B
    → Γ ⊢ a ∈ A
    → Γ ⊢ c # a ∈ B
  lam-ty : {n : Nat} → {Γ : Ctx n} → {A B : Ty}
    → {b : F (succ n)} → {a : F n}
    → cons A Γ ⊢ b ∈ B
    → Γ ⊢ lam b ∈ A ⇒ B
-- etc for types of zeroF, succF, recF
    
infixl 50 _#_

-- Canonical forms

data Val : Set where
  lamV  : F 1 → Val
  zeroV : Val
  succV : F 0 → Val

-- we leave substitution as a postulate. Exercise: define it!

postulate
  _[_] : F 1 → F 0 → F 0

-- computation rules (big step semantics, natural semantics)

data _=>_ : F 0 → Val → Set where
  β : {c a : F 0} → {b : F 1} → {v : Val}
    → c => lamV b
    → b [ a ] => v
    → c # a => v
  lamVal : {b : F 1} → lam b => lamV b
  zeroVal : zeroF => zeroV
  succVal : {a : F 0} → succF # a => succV a
  reczeroVal : {n d e : F 0} → {v : Val}
    → n => zeroV
    → d => v
    → recF # d # e # n => v
  recsuccVal : {m n d e : F 0} → {v : Val}
    → n => succV m
    → e # m # (recF # d # e # m) => v
    → recF # d # e # n => v

-- Semantic natural numbers

data isN : F 0 → Set where
  zeroN : {a : F 0} → a => zeroV → isN a
  succN : {a b : F 0} → a => succV b → isN b → isN a

-- Semantic typing of closed terms

_::_ : F 0 → Ty → Set
c :: NF    = isN c
c :: A ⇒ B = (a : F 0) → a :: A → c # a :: B

-- Typing open terms
-- unncessary because can be reduced to typing functions

Env : Nat → Set
Env n = Vect (F 0) n

data _fits_ : {n : Nat} → Env n → Ctx n → Set where
  nilfits : [] fits []
  consfits : {n : Nat} → {a : F 0} → {A : Ty} → {ρ : Env n} → {Γ : Ctx n}
    → a :: A
    → ρ fits Γ
    → cons a ρ fits cons A Γ

postulate
  inst : {n : Nat} → F n → Env n → F 0
  
opentyping : {n : Nat} → Ctx n → F n → Ty → Set
opentyping {n} Γ a A = (ρ : Env n) → ρ fits Γ → inst a ρ :: A

_⊢_::_ : {n : Nat} → Ctx n → F n → Ty → Set
Γ ⊢ a :: A = opentyping Γ a A

-- syntactic typing implies semantic typing
-- soundness : {n : Nat} → {Γ : Ctx n} → {a : F n} → {A : Ty}
-- → Γ ⊢ a ∈ A
-- → Γ ⊢ a :: A


  
   
