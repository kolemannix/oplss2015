module Semantics.SyntaxComputationRulesITT where

open import IType.Nat
open import IFam.Fin

-- F n is the set of n-place functions of a lambda structure following Aczel

data F : Nat → Set where
  var   : {n : Nat} → Fin n → F n
  _#_   : {n : Nat} → F n → F n → F n
  lam   : {n : Nat} → F (succ n) → F n
  pi    : {n : Nat} → F n → F (succ n) → F n
  set   : {n : Nat} → F n
  zeroF : {n : Nat} → F n
  succF : {n : Nat} → F n
  recF  : {n : Nat} → F n
  NF    : {n : Nat} → F n

infixl 50 _#_

data Val : Set where
  lamV  : F 1 → Val
  piV   : F 0 → F 1 → Val
  setV  : Val
  zeroV : Val
  succV : F 0 → Val
  NV    : Val

postulate
  _[_] : F 1 → F 0 → F 0

data _=>_ : F 0 → Val → Set where
  β : {c a : F 0} → {b : F 1} → {v : Val}
    → c => lamV b
    → b [ a ] => v
    → c # a => v
  lamVal : {b : F 1} → lam b => lamV b
  piVal : {A : F 0} → {B : F 1} → pi A B => piV A B
  setVal : set => setV
  zeroVal : zeroF => zeroV
  succVal : {a : F 0} → succF # a => succV a
  succVal₀ : succF => lamV (succF # (var ′0))
  reczeroVal : {n d e : F 0} → {v : Val}
    → n => zeroV
    → d => v
    → recF # d # e # n => v
  recsuccVal : {m n d e : F 0} → {v : Val}
    → n => succV m
    → e # m # (recF # d # e # m) => v
    → recF # d # e # n => v
  recVal₀ : recF => lamV (lam (lam (recF # (var ′2) # (var ′1) # (var ′0))))
  NVal : NF => NV
