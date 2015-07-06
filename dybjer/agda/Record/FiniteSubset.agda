module Record.FiniteSubset where

open import IType.Bool
open import IType.Nat

record DSet : Set₁ where
  field
    obj : Set
    eq : obj → obj → Bool
    
-- eq must be an equivalence relation

NatEq : DSet
NatEq = record { obj = Nat
               ; eq = eqNat
               }

record FiniteSubset (A : DSet) : Set₁ where
  field
    set : Set
    _∈_ : DSet.obj A → set → Bool
    size : set → Nat
    empty : set
    insert : DSet.obj A → set → set
    ax : {a : DSet.obj A} → {as : set} → So (a ∈ insert a as)

-- finite subsets implemented as lists without duplicates

{- 
open import IType.List

ListFS : (A : DSet) → FiniteSubset A
ListFS A = record { set = List (DSet.obj A)
                  ; _∈_ = λ x s → member {DSet.obj A} (DSet.eq A) x s
                  ; size = length
                  ; empty = []
                  ; insert = λ x s → insertFresh (DSet.eq A) x s
                  ; ax = {!!}
                  }
-}
