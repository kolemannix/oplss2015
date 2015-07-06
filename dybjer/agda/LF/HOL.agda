-- Church's simple theory of types 1940
-- see eg Stanford Encyclopedia of Philosophy
-- "Church's Type Theory" 

module LF.HOL where

postulate
-- base types
  i : Set
  o : Set
-- logical constants
  ~ : o → o
  _∨_ : o → o → o
  Π : (α : Set) → (α → o) → o
  ι : (α : Set) → (α → o) → α
  ∃! : (α : Set) → (α → o) → o -- definable
-- axioms
  T : o → Set
  em : (φ : o)
    → T (φ ∨ ~ φ)
  description-axiom :  (α : Set) → (φ : α → o)
    → T (∃! α φ)
    → T (φ (ι α φ))
-- etc
  
