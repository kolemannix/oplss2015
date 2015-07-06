module FiniteSubsets.Interface where

-- interface for finite subsets of natural numbers

open import IType.Nat
open import IType.Bool

record FiniteSubset : Set₁ where
  field
    set : Set
    _∈_ : Nat → set → Bool
    size : set → Nat
    empty : set
    insert : Nat → set → set
    ax-∈-insert : {n : Nat} → {ns : set} → So (n ∈ insert n ns)


