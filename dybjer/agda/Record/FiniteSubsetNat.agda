module Record.FiniteSubsetNat where

open import IType.Bool
open import IType.Nat
-- open import MLTT.MlTT

record FiniteSubsetNat : Set₁ where
  field
    set : Set
    _∈_ : Nat → set → Bool
    size : set → Nat
    empty : set
    insert : Nat → set → set
--    ax-∈-empty : (n : Nat) → So (n ∈ empty) → ⊥
    ax-∈-insert : {n : Nat} → {ns : set} → So (n ∈ insert n ns)
--    ax-size-empty : I Nat (size empty) 0

-- finite subsets implemented as lists with possible duplicates

open import IType.List
-- open import MLTT.PropositionalLogic

member : Nat → List Nat → Bool
member m [] = false
member m (n :: ns) = eqNat m n || member m ns

sizeFS : List Nat → Nat
sizeFS [] = 0
sizeFS (n :: ns) = if member n ns then sizeFS ns else succ (sizeFS ns)

axFS : (n : Nat) → (ns : List Nat) → So (member n (n :: ns))
axFS n ns = ||-intro (eqNat n n) (member n ns) (refleqNat n) 

ListFS : FiniteSubsetNat
ListFS = record { set = List Nat
                  ; _∈_ = member
                  ; size = sizeFS
                  ; empty = []
                  ; insert = λ x s → x :: s
                  ; ax-∈-insert = (λ {n} {ns} → axFS n ns)
                  }
