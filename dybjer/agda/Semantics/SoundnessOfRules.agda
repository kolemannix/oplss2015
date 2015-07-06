module Semantics.SoundnessOfRules where

open import IType.Nat
open import Semantics.SyntaxComputationRulesITT
open import Semantics.TypingJudgments

-- |- B B |- C
-- -----------
-- |- Pi B C

pi-formation : (B : F zero) → (C : F one)
  → (p : isTy B)
  → ((x : F zero) → isTm x B p → isTy (C [ x ]))
  → isTy (pi B C)
pi-formation B C p q = piTy B C piVal p q

postulate
  subst-lemma-Ty : (C : F one) → (B b : F zero)
    → (p : isTy B)
    → (q : (x : F zero) → isTm x B p → isTy (C [ x ]))
    → (s : isTm b B p)
    → isTy (C [ b ])
  subst-lemma-Tm : (C c : F one) → (B b : F zero)
    → (p : isTy B)
    → (q : (x : F zero) → isTm x B p → isTy (C [ x ]))
    → (s : isTm b B p)
    → (t : (x : F zero) → (y : isTm x B p) → isTm (c [ x ]) (C [ x ]) (q x y)) 
    → isTy (C [ b ])
    → isTm (c [ b ]) (C [ b ]) (subst-lemma-Ty C B b p q s)

-- proof by induction on C and q?
-- need a more general substitution lemma with arbitrary many variables
  
pi-elimination : (B f b : F zero) → (C : F one)
  → (p : isTy B)
  → (q : (x : F zero) → isTm x B p → isTy (C [ x ]))
  → (r : isTm f (pi B C) (pi-formation B C p q))
  → (s : isTm b B p)
  → isTm (f # b) (C [ b ]) (subst-lemma-Ty C B b p q s)
pi-elimination B f b C p q r s with (subst-lemma-Ty C B b p q s)
pi-elimination B f b C p q r s | piTy B' C' d p' q' = {!!}
pi-elimination B f b C p q r s | setTy d = {!!}
pi-elimination B f b C p q r s | NTy d = {!!}
  
-- -- |- set

-- rulesetty : isTy set
-- rulesetty = setTy setVal

-- -- |- A : set
-- -- -----------
-- -- |- A

-- ruleAsetAtype : (A : F zero) → isTm A set (setTy setVal) → isTy A
-- ruleAsetAtype (var i) d = {!!}
-- ruleAsetAtype (A # A₁) d = {!!}
-- ruleAsetAtype (lam A) d = {!!}
-- ruleAsetAtype (pi B C) (piset B₁ C₁ x d x₁) = piTy {!!} {!!} {!!} (ruleAsetAtype B {!!}) {!!}
-- ruleAsetAtype (pi B C) (Nset x) = {!!}
-- ruleAsetAtype set d = {!!}
-- ruleAsetAtype zeroF d = {!!}
-- ruleAsetAtype succF d = {!!}
-- ruleAsetAtype recF d = {!!}
-- ruleAsetAtype NF d = NTy NVal -- NTy NVal

-- -- |- N : set

-- ruleNset : isTm NF set (setTy setVal)
-- ruleNset = Nset NVal
