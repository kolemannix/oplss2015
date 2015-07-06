module MLTT.PropositionalLogic where

-- Prop = Set
-- parameters vs Set → Set → Set

-- Intuitionistic propositional logic
-- introduction rules

data _∨_ (φ ψ : Set) : Set where
  ∨-intro₀ : φ → φ ∨ ψ 
  ∨-intro₁ : ψ → φ ∨ ψ

-- elimination rule and proof normalization

∨-elim : {φ ψ χ : Set} → (φ → χ) → (ψ → χ) → φ ∨ ψ → χ
∨-elim d e (∨-intro₀ a) = d a
∨-elim d e (∨-intro₁ b) = e b

data _∧_ (φ ψ : Set) : Set where
  ∧-intro : φ → ψ → φ ∧ ψ

∧-elim₀ : {φ ψ : Set} → φ ∧ ψ → φ
∧-elim₀ (∧-intro a b) = a

∧-elim₁ : {φ ψ : Set} → φ ∧ ψ → ψ
∧-elim₁ (∧-intro a b) = b

data _⊃_ (φ ψ : Set) : Set where
  ⊃-intro : (φ → ψ) → φ ⊃ ψ

⊃-elim : {φ ψ : Set} → φ ⊃ ψ → φ → ψ
⊃-elim (⊃-intro f) a = f a

-- empty pattern matching

data ⊥ : Set where

⊥-elim : {φ : Set} -> ⊥ -> φ
⊥-elim ()

data ⊤ : Set where
  ⊤-intro : ⊤

¬ : Set → Set
¬ φ = φ → ⊥

