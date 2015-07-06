-- Integers

module Id.Int where

open import IType.Nat
open import IType.Bool

-- open import MLTT

data Z : Set where
  O : Z
  +1_ : Nat → Z
  -1_ : Nat → Z

inj+ : Nat → Z
inj+ zero = O
inj+ (succ n) = +1 n

inj- : Nat → Z
inj- zero = O
inj- (succ n) = -1 n

succZ : Z → Z
succZ O = +1 zero
succZ (+1 n) = +1 succ n
succZ (-1 n) = -1 pred n

data Z' : Set where
  _#_ : Nat → Nat → Z'

normalize : Z' → Z'
normalize (zero # n) = zero # n
normalize (succ m # zero) = succ m # zero
normalize (succ m # succ n) = normalize (m # n)

id : Z' → Z' → Bool
id (m # n) (m' # n') = eqNat m m' && eqNat n n'

eqZ' : Z' → Z' → Bool
eqZ' i j = id (normalize i) (normalize j)

data Z'' : Set where
  + : Nat → Z''
  - : Nat → Z''

eqZ'' : Z'' → Z'' → Bool
eqZ'' (+ m) (+ n) = eqNat m n
eqZ'' (+ m) (- n) = isZero m && isZero n
eqZ'' (- m) (+ n) = isZero m && isZero n
eqZ'' (- m) (- n) = eqNat m n

  
