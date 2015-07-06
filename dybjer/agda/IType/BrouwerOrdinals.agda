module IType.BrouwerOrdinals where

open import IType.Nat

data Ord : Set where
  zeroOrd : Ord
  succOrd : Ord → Ord
  limOrd : (Nat → Ord) → Ord

nat2ord : Nat → Ord
nat2ord zero = zeroOrd
nat2ord (succ n) = succOrd (nat2ord n)

ω : Ord
ω = limOrd (λ x → nat2ord x)

addOrd : Ord → Ord → Ord
addOrd α zeroOrd = α
addOrd α (succOrd β) = succOrd (addOrd α β)
addOrd α (limOrd f) = limOrd (λ x → addOrd α (f x))
