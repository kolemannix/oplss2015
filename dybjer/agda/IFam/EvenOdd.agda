module IFam.EvenOdd where

-- a mutual inductive definition (heterogenous or many-sorted term algebra)

mutual
  data Even : Set where
    zero : Even
    succOdd : Odd → Even

  data Odd : Set where
    succEven : Even → Odd

open import IType.Bool

-- an indexed inductive definition (inductive family)

data EvenOdd : Bool → Set where
   zero : EvenOdd true
   succOdd : EvenOdd false → EvenOdd true
   succEven : EvenOdd true → EvenOdd false

-- Exercise: write the eliminator for EvenOdd and Even and Odd.

i : Even → EvenOdd true
j : Odd → EvenOdd false
i zero = zero
i (succOdd m) = succOdd (j m)
j (succEven n) = succEven (i n)

-- opposite direction, you need type valued function

EvenOdd' : Bool → Set
EvenOdd' true = Even
EvenOdd' false = Odd

i' : (b : Bool) → EvenOdd b → EvenOdd' b
i' .true zero = zero
i' .true (succOdd m) = succOdd (i' false m)
i' .false (succEven m) = succEven (i' true m)

-- inductive predicates

open import IType.Nat

mutual
  data EvenP : Nat → Set where
    zeroEvenP : EvenP zero
    succOddP : (m : Nat) → OddP m → EvenP (succ m)

  data OddP : Nat → Set where
    succEvenP : (m : Nat) → EvenP m → OddP (succ m)

-- a decidable predicate ("a Boolean is a bit uninformative")

evenP : Nat → Bool
evenP zero = true
evenP (succ m) = ¬ (evenP m)

