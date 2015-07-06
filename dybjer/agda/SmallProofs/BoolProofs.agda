module SmallProofs.BoolProofs where

open import IType.Bool
open import MLTT.PropositionalLogic
open import MLTT.MLTT renaming (r to refl)

-- proving equality of two boolean expressions

notnotI : (b : Bool) → I Bool b (not (not b))
notnotI true = refl
notnotI false = refl

-- notnotI x = if x then refl else refl

-- Now prove the same equality as above using So

_<==>_ : Bool → Bool → Bool
true <==> true = true
true <==> false = false
false <==> true = false
false <==> false = true

sonotnot : (b : Bool) → So (b <==> not (not b))
sonotnot true = ⊤-intro
sonotnot false = ⊤-intro

