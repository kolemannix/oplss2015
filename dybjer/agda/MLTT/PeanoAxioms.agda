-- 6. Peano's axioms

module MLTT.PeanoAxioms where

open import MLTT.MLTT

-- pattern matching with dependent types

peano3pm : {m n : N} → I N (s m) (s n) → I N m n
peano3pm r = r

-- do it with J-eliminator!

pred : N → N
pred O = O
pred (s m) = m

peano3mltt : {m n : N} → I N (s m) (s n) → I N m n
peano3mltt {m} {n'} p = J {a = s m} {C = λ y z → I N m (pred y)} r (s n') p

-- pattern matching with dependent types - empty pattern

peano4pm : {n : N} → I N O (s n) → N₀
peano4pm ()

-- do it with J-eliminator!

-- a large family, this needs to be done by rec and T

TN : N → Set
-- TN O = N₁
-- TN (s m) = N₀
TN m = T (R {λ x → U} n₁ (λ x y → n₀) m)

peano4mltt : {n : N} → I N O (s n) → N₀
peano4mltt {m} p = J {A = N} {a = O} {C = λ y z → TN y} 0₁ (s m) p

-- Heyting arithmetic is a subsystem of MLTT (we need to define + and * and their equations too)

