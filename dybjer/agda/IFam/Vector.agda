module IFam.Vector where

open import IType.Nat
open import IType.Product

-- List is a polymorphic type. In Haskell we have the type [a] of lists where the elements belong
-- to an arbitrary type a. In Agda we declare the polymorphic data type of lists as follows:

data Vect (A : Set) : Nat → Set where
  []   : Vect A zero
  _::_ : {n : Nat} → A → Vect A n → Vect A (succ n)

-- This notation means that we define a list constructor
--
-- List : Set → Set
--
-- and two polymorphic constructors with implicit arguments:
--
-- [] : {A : Set} → List A
-- _::_ : {A : Set} → A → List A → List A

-- head is a partial functions in Haskell,
-- it is not defined on the empty list

head : {A : Set} → {n : Nat} → Vect A (succ n) → A
head (a :: as) = a

tail : {A : Set} → {n : Nat} → Vect A (succ n) → Vect A n
tail (a :: as) =  as

-- We can define polymorphic map

map : {A B : Set} → {n : Nat} → (A → B) → Vect A n → Vect B n
map f []        = []
map f (a :: as) = f a :: map f as

-- and polymorphic zip as in Haskell (we need to import and open the type of pairs first)

zip : {A B : Set} → {n : Nat} → Vect A n → Vect B n → Vect (A × B) n
zip []        []        = []
zip (x :: xs) (y :: ys) = < x , y > :: zip xs ys

-- The intention is to "zip" lists of the same length, the last clause will
-- only be used when lists are of different lengths


