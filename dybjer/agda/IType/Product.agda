module IType.Product where

-- The Cartesian product of two types (the type of pairs, cf Pierce, figure 11-5 p 126) is a data type
-- one constructor:

data _×_ (A B : Set) : Set where
  <_,_> : A -> B -> A × B

infixr 50 _×_

-- Exercise: write out the full types of _×_ and <_,_>. Hint: look at the definition of the data type List.
-- Pierce uses {_,_}

-- We can now define the first and the second projection:

fst : {A B : Set} -> A × B -> A
fst < a , b > = a

-- Pierce uses t.1 for fst t, the "first projection"

snd : {A B : Set} -> A × B -> B
snd < a , b > = b

-- Pierce uses t.2 for snd t, the "second projection"

-- Pierce's evaluation rules are for "strict" pairs, evaluating the first component to a value, then the second component. When projections are computed we first compute both components of the pair, then throw one away

-- In general we can have tuples (pairs, triples, quadruples, ...)

data Unit : Set where
  <> : Unit

