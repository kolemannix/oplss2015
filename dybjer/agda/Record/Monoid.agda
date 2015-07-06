module Record.Monoid where

open import MLTT.MLTT

record IMonoid : Set₁ where
  field
    obj : Set
    _*_ : obj → obj → obj
    id  : obj
    α : (a b c : obj) → I obj ((a * b) * c) (a * (b * c))
    l : (a : obj) → I obj (id * a) a
    ρ : (a : obj) → I obj (a * id) a

record EMonoid : Set₁ where
  field
    obj : Set
    _==_ : obj → obj → Set
    _*_ : obj → obj → obj
    *-pres : (a a' b b'  : obj)
      → a == a' → b == b' → (a * b) == (a' * b')
    id  : obj
    α : (a b c : obj) → ((a * b) * c) == (a * (b * c))
    l : (a : obj) → (id * a) == a
    ρ : (a : obj) → (a * id) == a
