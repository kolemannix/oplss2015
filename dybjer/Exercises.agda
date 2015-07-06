module Exercises where

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

_&&_ : Bool → Bool → Bool
true && b  = b
false && b = false

_||_ : Bool → Bool → Bool
true || b = true
false || b = b

data So : Bool -> Set where 
  Oh : So true

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

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data even : Nat → Set where
  zero_even : even zero 
  ssn_even : {n : Nat} → even n → even (succ (succ n))

plus : Nat -> Nat -> Nat
plus a zero = a
plus a (succ b) = succ (plus a b)

_−_ : Nat -> Nat -> Nat
a − zero = a
zero − b = zero
(succ a) − (succ b) = a − b


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

natrec : {a : Set} → a → (Nat → a → a) → Nat → a
natrec base step zero     = base
natrec base step (succ n) = step n (natrec base step n)

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
eqrec = natrec (natrec true (λ _ _ → false)) (λ _ r → natrec false (λ p _ → r p))

donkey_cong : (x : Nat) → (f : Nat -> Nat) → So (eqrec (f x) (f x))
donkey_cong x f = {!!}
--------- 3. predicate logic -------------

data _∨_ (φ : Set) (ψ : Set) : Set where
  ∨-introₗ : φ → φ ∨ ψ
  ∨-introᵣ : ψ → φ ∨ ψ

∨-elim : {φ ψ χ : Set} → (φ → χ) → (ψ → χ) → φ ∨ ψ → χ
∨-elim d e (∨-introₗ a) = d a
∨-elim d e (∨-introᵣ b) = e b

data _∧_ (φ : Set) (ψ : Set) : Set where
  ∧-intro : φ → ψ → φ ∧ ψ
 
∧-elimₗ : {φ ψ : Set} → (φ ∧ ψ) → φ
∧-elimₗ (∧-intro a b) = a

∧-elimᵣ : {φ ψ : Set} → (φ ∧ ψ) → ψ
∧-elimᵣ (∧-intro a b) = b

data _⊂_ (φ ψ : Set) : Set where
  ⊂-intro : (φ → ψ) → (φ ⊂ ψ)

⊂-elim : {φ ψ : Set} → (φ ⊂ ψ) → φ → ψ
⊂-elim (⊂-intro f) x = (f x)

data _⇔_ (φ ψ : Set) : Set where
  ⇔-intro : (φ ⊂ ψ) → (ψ ⊂ φ) → φ ⇔ ψ

⇔-elimₗ : {φ ψ : Set} → (φ ⇔ ψ) → φ ⊂ ψ
⇔-elimₗ (⇔-intro l r) = l

⇔-elimᵣ : {φ ψ : Set} → (φ ⇔ ψ) → ψ ⊂ φ
⇔-elimᵣ (⇔-intro l r) = r

data ⊥ : Set where

⊥-elim : {φ : Set} → ⊥ → φ
⊥-elim ()

data ⊤ : Set where
  ⊤-intro : ⊤

-- no top elim

¬ : Set → Set
¬ φ = φ → ⊥


-- 6a

sixa : {P : Set} → (¬ (¬ (¬ P))) ⊂ (¬ P)
sixa {P} = ⊂-intro (λ z x → z (λ x₁ → x₁ x))

-- 6b  ¬(P ∨ Q) ↔ ¬P&¬Q.
sixb : {P Q : Set} → (¬(P ∨ Q)) ⇔ ((¬ P) ∧ (¬ Q))
sixb = ⇔-intro (⊂-intro
                  (λ z → ∧-intro (λ x → z
                  (∨-introₗ x)) (λ x → z (∨-introᵣ x)))) (⊂-intro (λ x → λ y → ∨-elim (∧-elimₗ x) (∧-elimᵣ x) y))

-- ∨-elim : {φ ψ χ : Set} → (φ → χ) → (ψ → χ) → φ ∨ ψ → χ

test' : {a b c : Set} → (a ∨ b) → (a → c) → (b → c) → c
test' = λ x y z → ∨-elim y z x

orswap : {A B : Set} → (A ∨ B) → (B ∨ A)
orswap (∨-introₗ a) = ∨-introᵣ a
orswap (∨-introᵣ b) = ∨-introₗ b

orswap' : {A B : Set} → (A ∨ B) → (B ∨ A)
orswap' = λ x → (∨-elim (λ a → ∨-introᵣ a ) (λ b → ∨-introₗ b) x )


test : {a b c : Set} → (a ⊂ c) → (b ⊂ c) → (a ∨ b) → c
test = λ x y z → ∨-elim (⊂-elim y) (⊂-elim x) (∨-elim (λ α → ∨-introᵣ α) (λ β → ∨-introₗ β) z)

-- 7 Excluded Middle implies double-negation!
sevena : {α : Set} → (α ∨ (¬ α)) ⊂ ((¬ (¬ α)) ⊂ α)
sevena = ⊂-intro (λ x → ⊂-intro (λ x₁ → ∨-elim (λ x₂ → x₂) (λ x₂ → ⊥-elim (x₁ x₂)) x))

-- Double-negation implies excluded middle!
-- Not possible?!
-- sevenb : {α : Set} → ((¬ (¬ α)) ⊂ α) ⊂ (α ∨ (¬ α))
-- sevenb = ⊂-intro (λ x → ∨-introₗ (⊂-elim x (λ x₁ → {!!})))

-- Same problem!
sevenc : ({a : Set} → ((¬ (¬ a)) → a)) → ({a : Set} → (a ∨ (¬ a)))
sevenc = λ x → {!!}

sevend : ({a : Set} → (a ∨ (¬ a))) → ({a : Set} → ((¬ (¬ a)) → a))
sevend = λ x x₁ → ∨-elim (λ b → b) (λ b → ⊥-elim (x₁ b)) x


-- Church booleans
ChurchTrue : {a : Set} → a → a → a
ChurchTrue = λ a₁ a₂ → a₁
ChurchFalse : {a : Set} → a → a → a
ChurchFalse = λ a₁ a₂ → a₂

ChurchAnd : ({a : Set} → (a → a → a)) →
            ({a : Set} → (a → a → a)) →
            ({a : Set} → (a → a → a))
ChurchAnd = λ p q → p q p

ChurchOr : ({a : Set} → (a → a → a)) →
            ({a : Set} → (a → a → a)) →
            ({a : Set} → (a → a → a))
ChurchOr = λ p q → p p q

-- Church Numerals

{-# BUILTIN NATURAL Nat #-}

ChurchZero : {a : Set} → (f : a → a) → a → a
ChurchZero = λ f x → x

ChurchOne : {a : Set} → (f : a → a) → a → a
ChurchOne = λ f x → f x

ChurchTwo : {a : Set} → (f : a → a) → a → a
ChurchTwo = λ f x → f (f x)

ChurchThree : {a : Set} → (f : a → a) → a → a
ChurchThree = λ f x → f (f (f x))

ChurchAdd : ({a : Set} → (f : a → a) → a → a) →
            ({a : Set} → (f : a → a) → a → a) →
            ({a : Set} → (f : a → a) → a → a)
ChurchAdd = λ m n f x → m f (n f x)

ChurchMult : ({a : Set} → (f : a → a) → a → a) →
            ({a : Set} → (f : a → a) → a → a) →
            ({a : Set} → (f : a → a) → a → a)
ChurchMult = λ m n f → m (n f)

data list (a : Set) : Set where
  [] : list a
  _::_ : a → list a → list a

{-# BUILTIN LIST list #-}
{-# BUILTIN NIL  []  #-}
{-# BUILTIN CONS _::_ #-}

_++_ : {a : Set} → list a → list a → list a
[] ++ b = b
(h :: t) ++ b = h :: (t ++ b)

data vect (a : Set) : Nat → Set where
  vnil : vect a zero
  vcons : {n : Nat} → a → vect a n → vect a (succ n)

plus' : Nat -> Nat -> Nat
plus' zero b = b
plus' (succ a) b = succ (plus' a b)

vapp : {a : Set} → {n m : Nat} → vect a n → vect a m → vect a (plus' n m)
vapp vnil ys = ys
vapp (vcons x xs) ys = vcons  x (vapp xs ys)
