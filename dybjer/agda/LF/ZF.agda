module LF.ZF where

-- ZF classical set theory

open import MLTT.PropositionalLogic
open import MLTT.PredicateLogic renaming (D to V)
open import MLTT.Identity

postulate

-- classical logic

  em : (φ : Set) → φ ∨ ¬ φ

-- a binary function symbol

  _∈_ : V → V → Set

-- empty set

  ∅ : V
  ax-∅ : (y : V) → ¬ (y ∈ ∅)
--  ax-∅ : ∃ (λ x → ∀ y → ¬ (y ∈ x))

-- pairing

  [_,_] : V → V → V
  ax-[_,_]₀ : ∀ x y → x ∈ [ x , y ]
  ax-[_,_]₁ : ∀ x y → y ∈ [ x , y ]
  
[_] : V → V
[ x ] = [ x , x ]

-- natural numbers

O : V

O = ∅

succ : V → V
succ x = [ x , [ x ] ]

-- axiom of infinity

postulate
  ω : V
  ax-ω : (O ∈ ω)
       ∧ (∀ x → x ∈ ω → succ x ∈ ω)

-- etc
  
  
