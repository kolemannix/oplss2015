module IType.PatternMatching where

open import IType.Nat
open import IType.Bool

-- some functions which are not straightforward to turn into primitive recursion

eq : Nat → Nat → Bool
eq zero     zero     = true
eq zero     (succ n) = false
eq (succ m) zero     = false
eq (succ m) (succ n) = eq m n

min : Nat → Nat → Nat
min zero     n        = zero
min (succ m) zero     = zero
min (succ m) (succ n) = succ (min m n)

-- Colson showed that with primitive recursion you cannot compute min
-- in O(min m n) steps
-- Exercise: define it in Gödel System T

half : Nat → Nat
half zero = zero
half (succ zero) = zero
half (succ (succ n)) = half n

fib : Nat → Nat
fib zero            = zero
fib (succ zero)     = one
fib (succ (succ n)) = fib n + fib (succ n)

-- in general "size-change termination" or "sized types"

-- worse: what to do with division, Euclidean division?
