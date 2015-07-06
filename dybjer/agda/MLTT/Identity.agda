module MLTT.Identity where

open import MLTT.PredicateLogic

data _==_ : D → D → Set where
  =-intro : (x : D) → x == x

=-elim : {φ : D → Set} → {x y : D} → x == y → φ y → φ x
=-elim (=-intro x) p = p
