module Semantics.IdentityReflection where

open import Semantics.SyntaxComputationRulesITT79
open import Semantics.EqualityJudgments

id-formation : (A a a' : F 0)
  → (d : isTy A)
  → isTm a A d
  → isTm a' A d
  → isTy (IdF # A # a # a')
id-formation A a a' d p p' = {!!}
  
idrefl : (A c c' a a' : F 0)
  → (d : isTy A)
  → isTm a A d
  → isTm a' A d
  → isEqTm₁ c c' (IdF # A # a # a') {!!}
  → isEqTm₁ a a' A d
idrefl A c c' a a' p q = {!!}


