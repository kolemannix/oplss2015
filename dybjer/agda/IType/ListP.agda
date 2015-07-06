module IType.ListP (A : Set) where

data List : Set where
  []   : List
  _::_ : A -> List -> List

[_] : A → List
[ a ] = a :: []

tail : List → List
tail []        =  []
tail (a :: as) =  as
