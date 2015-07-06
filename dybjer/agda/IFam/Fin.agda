module IFam.Fin where

open import IType.Nat
open import IFam.Vector

-- Finite sets. Fin n represents natural numbers smaller than n.

data Fin : Nat → Set where
  zer : ∀ {n} → Fin (succ n)
  suc  : ∀ {n} → Fin n → Fin (succ n)

onefin : ∀ {n} → Fin (succ (succ n))
onefin = suc zer

-- private

  -- Examples.

′0 : ∀ {n} → Fin (succ n)
′0 = zer

′1 : ∀ {n} → Fin (succ (succ n))
′1 = suc zer

′2 : ∀ {n} → Fin (succ (succ (succ n)))
′2 = suc (suc zer)

-- A safe lookup function.

lookup : ∀ {A n} → Fin n → Vect A n → A
lookup zer     (x :: xs) = x
lookup (suc i) (x :: xs) = lookup i xs
