module Semantics.SyntaxComputationRulesITT79 where

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
  refF  : {n : Nat} → F n
  IdF   : {n : Nat} → F n

infixl 50 _#_

data Val : Set where
  lamV  : F one → Val
  piV   : F zero → F one → Val
  setV  : Val
  zeroV : Val
  succV : F zero → Val
  NV    : Val
  refV  : Val
  IdV   : (A A' a a' : F zero) → Val

IdV₁ : (A a a' : F zero) → Val
IdV₁ A a a' = IdV A A a a'

postulate
  _[_] : F one → F zero → F zero

data _=>_ : F zero → Val → Set where
  β : {c a : F zero} → {b : F one} → {v : Val}
    → c => lamV b → b [ a ] => v → c # a => v
  lamVal : {b : F one} → lam b => lamV b
  piVal : {a : F zero} → {b : F one} → pi a b => piV a b
  setVal : set => setV
  zeroVal : zeroF => zeroV
  succVal : {a : F zero} → succF # a => succV a
  reczeroVal : {n d e : F zero} → {v : Val}
    → n => zeroV
    → d => v
    → recF # d # e # n => v
  recsuccVal : {m n d e : F zero} → {v : Val}
    → n => succV m
    → e # m # (recF # d # e # m) => v
    → recF # d # e # n => v
  NVal : NF => NV
  refVal : refF => refV
  IdVal : {A A' a a' : F zero} → IdF # A # a # a' => IdV₁ A a a'
