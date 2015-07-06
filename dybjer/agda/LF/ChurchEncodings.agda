module LF.ChurchEncodings where

-- a predicative type of Church-numerals,
-- natural numbers as iterators
-- Set₁ is the second universe, a universe of "large" sets
-- In the Calculus of Constructions the type of N-church is Set!

N-church : Set₁
N-church = {X : Set} -> (X -> X) -> X -> X

zero-church : N-church
zero-church s z = z

succ-church : N-church → N-church
succ-church n s z = s (n s z)

-- but note that add-church does not type-check because of predicativity

-- add-church : N-church → N-church → N-church
-- add-church m n {N-church} s z = n succ-church m

N-church₁ : Set₂
N-church₁ = {X : Set₁} -> (X -> X) -> X -> X

succ-church₁ : N-church₁ → N-church₁
succ-church₁ n s z = s (n s z)

add-church : N-church → N-church₁ → N-church₁
add-church m n {N-church₁} s z = {!!}

-- There is operation "Lift : Set → Set₁" in the file "Level"
-- in the standard library
--
-- open import Level

postulate
   So₁ : Set → Set₁

I-leibnitz₁ : {A : Set} → A → A → Set₁
I-leibnitz₁ {A} a a' = {X : A → Set} → So₁ (X a) → So₁ (X a')

-- the following does not type-check:
-- I-leibnitz : {A : Set} → A → A → Set
-- I-leibnitz {A} a a' = {X : A → Set} → (X a) → (X a')



