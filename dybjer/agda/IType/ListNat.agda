module IType.ListNat where

open import IType.Nat
open import IType.ListP Nat

hd : List → Nat
hd [] = zero
hd (n :: ns) = n
