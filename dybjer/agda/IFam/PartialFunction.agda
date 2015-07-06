{-# OPTIONS --no-termination-check #-}

module IFam.PartialFunction where

open import IType.Nat
open import IType.Bool

-- the following is incorrect since div is not a total function
-- the termination-check will not accept it

div : Nat → Nat → Nat
div m n = if m < n then zero else succ (div (m - n) n)

-- Bove-Capretta encoding, partial function f : A → B as binary function
-- fbc : (x : A) → D x → B, where D x means f x is defined.

data D : Nat → Nat → Set where
  zeroq : (m n : Nat) → So (m < n) → D m n
  succq : (m n : Nat) → D (m - n) n → D m n

divbc : (m n : Nat) → D m n → Nat
divbc m n (zeroq .m .n p) = zero
divbc m n (succq .m .n p) = succ (divbc (m - n) n p)

-- Relation encoding (cf Prolog)

data Div : Nat → Nat → Nat → Set where
  zeroq : (m n : Nat) → So (m < n) → Div m n zero
  succq : (m n q : Nat) → Div (m - n) n q → Div m n (succ q)

-- Prove determinacy! Prove equivalence!
