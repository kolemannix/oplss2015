module IType.List where

-- List is a polymorphic type. In Haskell we have the type [a] of lists where the elements belong
-- to an arbitrary type a. In Agda we declare the polymorphic data type of lists as follows:

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

-- This notation means that we define a list constructor
--
-- List : Set -> Set
--
-- and two polymorphic constructors with implicit arguments:
--
-- [] : {A : Set} -> List A
-- _::_ : {A : Set} -> A -> List A -> List A

-- head is a partial functions in Haskell,
-- it is not defined on the empty list (note that A can be empty!)

-- head : {A : Set} → List A -> A
-- head []        = {!!}
-- head (a :: as) =  a

-- we can make tail total by conventionally define tail [] = []

tail : {A : Set}-> List A -> List A
tail []        =  []
tail (a :: as) =  as

-- We can define polymorphic map

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (a :: as) = f a :: map f as

-- and polymorphic zip as in Haskell (we need to import and open the type of pairs first)

open import IType.Product
open import MLTT.PredicateLogic

zip : {A B : Set} -> List A -> List B -> List (A × B)
zip []        []        = []
zip (x :: xs) (y :: ys) = < x , y > :: zip xs ys
zip _         _         = []

-- The intention is to "zip" lists of the same length, the last clause will
-- only be used when lists are of different lengths

