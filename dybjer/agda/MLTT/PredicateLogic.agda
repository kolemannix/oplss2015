-- Predicate logic

module MLTT.PredicateLogic where

postulate D : Set

-- untyped vs typed predicate logic

data ∃ (φ : D -> Set) : Set where
  ∃-intro : (x : D) → φ x → ∃ φ

∃-elim : {φ : D -> Set} -> {ψ : Set}
  -> ((x : D) -> φ x -> ψ)
  -> ∃ φ -> ψ
∃-elim d (∃-intro x p) = d x p

data ∀' (φ : D -> Set) : Set where
  ∀-intro : ((x : D) → φ x) → ∀' φ

∀-elim : {φ : D -> Set} → ∀' φ → (x : D) → φ x
∀-elim (∀-intro f) a = f a

-- ∀ x → φ is Agda shorthand for (x : A) → φ



