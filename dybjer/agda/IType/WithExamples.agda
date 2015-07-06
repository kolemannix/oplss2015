module IType.WithExamples where

open import IType.Nat
open import IType.Bool

min : Nat -> Nat -> Nat
min x y with x < y
min x y | true  = x
min x y | false = y

-- written with if

if : Bool → Nat → Nat → Nat
if true  x y = x
if false x y = y

min' : Nat -> Nat -> Nat
min' x y = if (x < y) x y 

open import IType.List

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x :: xs) with p x
... | true  = x :: filter p xs
... | false = filter p xs

-- written with if ...

