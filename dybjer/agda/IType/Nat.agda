-- 2. Natural numbers

module IType.Nat where

-- Unary natural numbers, you can get access
-- to decimal notation 
-- and machine arithmetic 
-- by using "builtin" numbers (below)

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

one = succ zero
two = succ one

pred : Nat → Nat
pred zero = zero
pred (succ n) = n

-- We define + and * by primitive recursion:

_+_ : Nat → Nat → Nat
m + zero     = m
m + (succ n) = succ (m + n)

_*_ : Nat → Nat → Nat
m * zero   = zero
m * succ n = m + (m * n)

-- ^C^C in the hole to refine a pattern

_-_ : Nat → Nat → Nat
zero - n = zero
succ m - zero = succ m
succ m - succ n = m - n

-- Decimal notation by "built in" natural numbers: 

{-# BUILTIN NATURAL Nat #-}

ten : Nat
ten = 10

-- Binary machine arithmetic for + and *:

{-# BUILTIN NATPLUS _+_ #-}

-- ^C^N 3 + 7

-- {-# BUILTIN NATTIMES _*_ #-}

-- There are many other built-in types:
-- (integers, floats, strings, characters) 

-- An example of how to compute by reduction: ^C-^N
--   one * one 
-- = one * succ zero
-- = one + one * zero
-- = one + zero
-- = one 

-- We can declare precedences and associations in Agda.
-- + and * are both infix operations which associate to the left
-- * binds harder than +:

infixl 60 _+_
infixl 70 _*_

-- Thus x + y + z parses as (x + y) + z

f : Nat → Nat → Nat → Nat
f x y z = x + y + z


-- the primitive recursion combinator
-- is a polymorphic higher order function:

natrec : {X : Set} -> X -> (Nat -> X -> X) -> Nat -> X
natrec base step zero     = base
natrec base step (succ n) = step n (natrec base step n)

-- Given a base case base : X and a step function step : Nat -> X -> X, 
-- we can define a function from
-- n : Nat to X by induction (primitive recursion) on the number n!

_+‘_ : Nat → Nat → Nat
m +‘ n = natrec m (λ _ x → succ x) n

-- Gödel system T is simply typed lambda calculus with Nat, zero, succ, and natrec
-- a programming language where all programs terminate. 
-- Agda is a more expressive language where all programs 
-- terminate

-- If we try to write a non-terminating program:

-- loop : Nat → Nat
-- loop x = loop x

-- Then Agda's termination checker will protest and colour the culprit in light salmon.
-- Note that Agda's termination checker will reject some terminating programs.

-- Exercises. Define exponential, factorial, ackerman-peter function (wikipedia)
-- http://en.wikipedia.org/wiki/Primitive_recursive_function gives a number of primitive recursive functions

-- what does the termination checker do to see that ack terminates? lexicographic ordering

iter : {X : Set} → (X → X) → X → Nat → X
iter f a zero = a
iter f a (succ n) = f (iter f a n)

h : (Nat → Nat) → Nat → Nat
-- h f zero = f 1
-- h f (succ n) = f (h f n)
-- h f = natrec (f 1) (λ x y → f y)
h f = iter f (f one)

ack : Nat → Nat → Nat
-- ack zero = succ 
-- ack (succ m) = h (ack m)
-- ack = natrec succ (λ x y → h y)
ack = iter h succ

-- In Gödel's T we can write primitive recursive functions, and functionals. A challenge is division



