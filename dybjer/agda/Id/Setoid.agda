module Id.Setoid where

open import IType.Bool

record Setoid : Set₁ where
  field
    obj : Set
    _==_ : obj → obj → Set
    trans : (x y z : obj) → x == y → y == z → x == z
    refl : (x : obj) → x == x
    symm : (x y : obj) → x == y → y == x

-- the type of setoids is a type of quintuples

{- eqBool : Bool → Bool → Bool

record {
  carrier = Bool
  _==_ = eqBool
  trans = transEqBool
  refl = reflEqBool
  symm = symmEqBool
  }

-- Exercise: Prove in Agda that any set with propositional identity is a setoid-}
