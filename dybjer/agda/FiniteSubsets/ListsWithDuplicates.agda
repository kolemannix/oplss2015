module FiniteSubsets.ListsWithDuplicates where

open import IType.Bool
open import IType.Nat
open import IType.List
open import FiniteSubsets.Interface

member : Nat → List Nat → Bool
member m [] = false
member m (n :: ns) = eqNat m n || member m ns

sizeFS : List Nat → Nat
sizeFS [] = 0
sizeFS (n :: ns) = if member n ns then sizeFS ns else succ (sizeFS ns)

ax-member-cons : (n : Nat) → (ns : List Nat) → So (member n (n :: ns))
ax-member-cons n ns = ||-intro (eqNat n n) (member n ns) (refleqNat n)

ListsWithDuplicates : FiniteSubset
ListsWithDuplicates = record { set = List Nat
                  ; _∈_ = member
                  ; size = sizeFS
                  ; empty = []
                  ; insert = λ x s → x :: s
                  ; ax-∈-insert = (λ {n} {ns} → ax-member-cons n ns)
                  }



