module IType.Bool where

data Bool : Set where
  true  : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

plus : Nat -> Nat -> Nat
plus a zero = a
plus a (succ b) = succ (plus a b)

_−_ : Nat -> Nat -> Nat
a − zero = a
zero − b = zero
(succ a) − (succ b) = a − b


-- Note that Agda has a standard library where many common types and functions are defined

not : Bool -> Bool
not true = false
not false = true

-- In Agda we have unicode and can for example write → for -> and ¬ for not: 

¬ : Bool → Bool
¬ = not

-- The names of unicode characters used by Agda are often the same as the names used in latex.

-- In Agda, we can write programs by gradual refinement, 
-- where we write ? for an unknown part of the program.
-- The ? becomes { - } when type-checked (a "hole").
-- Holes can be filled in either by writing a complete expression in the hole and doing ^C^SPC
-- or by writing a partial expression in the whole and doing ^C^R (refine)
-- or by writing the top level function and doing ^C^R

-- Exercise: write the following function by gradual refinement:

¬¬ : Bool → Bool
¬¬ b = ¬ (¬ b)

-- Agda can also create complete case analysis (pattern matching) automatically 
-- by writing the pattern variable in a hole and do ^C^C

-- Exercise: write not by gradual refinement and case analysis

-- This is how you declare an infix operator:

_&&_ : Bool → Bool → Bool
b && true  = b
b && false = false

_||_ : Bool → Bool → Bool
true || true = true
false || true = true
true || false = true
false || false = false

-- It is a special case of mixfix declarations:

if_then_else_ : {C : Set} → Bool → C → C → C
if true  then y else z = y
if false then y else z = z

-- You can compute ("normalize") closed expressions by writing ^C^N and then write the expression afterwards.

-- Exercise: compute a few expressions!

eqNat : Nat → Nat → Bool
eqNat zero zero = true
eqNat zero (succ n) = false
eqNat (succ m) zero = false
eqNat (succ m) (succ n) = eqNat m n

natrec : {a : Set} → a → (Nat → a → a) → Nat → a
natrec base step zero     = base
natrec base step (succ n) = step n (natrec base step n)


isZero : Nat → Bool
isZero n = natrec true (λ x y → false) n

help : (Nat → Bool) → Nat → Bool
help f zero = false
help f (succ n) = f n

eqNat' : Nat → Nat → Bool
eqNat' zero = isZero
eqNat' (succ m) = help (eqNat' m)

open import MLTT.PropositionalLogic

data So : Bool -> Set where 
  Oh : So true

||-intro : (b c : Bool) → So b → So (b || c)
||-intro true true Oh = Oh
||-intro true false Oh = Oh
||-intro false c ()

refleqNat : (n : Nat) → So (eqNat n n)
refleqNat zero = Oh
refleqNat (succ n) = refleqNat n

_<_ : Nat → Nat → Bool
m < zero = false
zero < succ n = true
succ m < succ n = m < n

-- Exercise 1.
bimp : Bool → Bool → Bool
bimp false  _ = true
bimp true b = b

em : (b : Bool) → So (b || (not b))
em false = Oh
em true = Oh

_<==>_ : Bool -> Bool -> Bool
true<==>true = true
false<==>false = true
_ <==> _ = false

-- dm : (a b : Bool) -> So (not (a && b) <==> (not a || not b))
-- dm true false = Oh
-- dm true true = ()
-- dm false true = {!!}
-- dm false false = {!!}

Pred : Nat -> Set
Pred zero = Bool
Pred (succ n) = Bool -> Pred n

taut : (n : Nat) -> Pred n -> Bool
taut zero P = P
taut (succ n) P = taut n (P true) && taut n (P false)


_×_ : Nat -> Nat -> Nat
a × zero = zero
a × (succ n) = plus a (a × n)


pow : Nat -> Nat -> Nat
pow n zero = succ zero
pow n (succ m') = n × (pow n m')

powrec : Nat -> Nat -> Nat
powrec n = natrec (succ zero) (λ m' b → n × b)


_==_ : Nat -> Nat -> Bool
zero == zero = true
zero == succ m = false
succ n == zero = false
succ n == succ m = n == m

-- natrec : {a : set} → a → (nat → a → a) → nat → a
-- natrec base step zero     = base
-- natrec base step (succ n) = step n (natrec base step n)

iszero : Nat -> Bool
iszero = natrec {Bool} true (λ x y → false)

arezero : Nat -> Nat -> Bool
arezero = natrec {Nat -> Bool} iszero (λ x y → natrec {Bool} true (λ n m → false))

eqrec : Nat -> Nat -> Bool
eqrec = natrec (natrec true (λ x y → false))
                             (λ _ _ → natrec true
                                      (λ _ step' → step'))

works : (n m : Nat) → (So (eqNat n m)) -> (So (eqrec n m))
works zero zero = λ _ → Oh
works zero (succ n) = λ z → z
works (succ n) zero = λ _ → Oh
works (succ n') (succ m') = {!!}
