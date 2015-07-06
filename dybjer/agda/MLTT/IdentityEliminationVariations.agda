module MLTT.IdentityEliminationVariations where

open import MLTT.MLTT

-- The identity eliminator in MLTT.MLTT is due to Christine Paulin.
-- It is obtained by considering one of the elements "a" to be a
-- parameter. So that we instead define a unary predicate in A → Set
-- "to be identical to a". It is closer to identity elimination in
-- predicate logic.

-- Martin-Löf's original identity eliminator from 1973 instead
-- defines a binary relation in A → A → Set, inductively generated
-- by the reflexivity axiom. It is:

J-ml : {A : Set} → {C : (x y : A) → I A x y → Set}
  → ((x : A) → C x x r)
  → (a b : A) → (c : I A a b) → C a b c
J-ml d .b b r = d b

-- Streicher introduced a new identity eliminator, not derivable by J

K-st : {A : Set} → {C : (x : A) → I A x x → Set}
  → ((x : A) → C x r)
  → (a : A) → (c : I A a a) → C a c
K-st d a r = d a
-- K-st {A} {C} d a c = K {A} {a} {λ z → C a z} (d a) c

-- Here is the formulation as a unary predicate:

K : {A : Set} → {a : A} → {C : I A a a → Set}
  → C r
  → (c : I A a a) → C c
K d r = d

-- It entails uniqueness of identity proofs:

uip' : {A : Set} → (a : A) → (p : I A a a) → I (I A a a) p r
uip' {A} a p = K {A} {a} {λ x → I (I A a a) x r} r p

uip : {A : Set} → (a b : A) → (p c : I A a b) → I (I A a b) p c
uip a .a p r = uip' a p

-- The last definition is by pattern matchin.
-- Exercise: prove uip with J and K: hint start with
-- uip {A} a a' p p' = J {A} {a} (λ y z → ?) (uip' a r) a' p'
-- uip a .a r r = r

-- Equality reflection: from Γ ⊢ c : I A a a' deduce  Γ ⊢ a = a' : A
-- definitionally, cannot be formulated as a constant in LF.
