module Semantics.EqualityJudgments1 where

open import Semantics.SyntaxComputationRulesITT79
open import IType.Nat
open import IType.Product

data isEqN : F zero → F zero → Set where
  zeroEqN : {a a' : F zero}
    → a => zeroV
    → a' => zeroV
    → isEqN a a'
  succEqN : {a a' b b' : F zero}
    → a => succV b
    → a' => succV b'
    → isEqN b b'
    → isEqN a a'

mutual
  data isEqset : F zero → F zero → Set where
    NEqset : {A A' : F zero}
      → A => NV
      → A' => NV
      → isEqset A A'
    piEqset : {A A' : F zero} → (B B' : F zero) → (C C' : F one)
      → A => piV B C
      → A' => piV B' C'
      → (p : isEqset B B')   
      → ((x : F zero) → isEl x B p → isEqset (C [ x ]) (C' [ x ]))
      → isEqset A A'
{-    IdEqset : {A A' : F zero} → (B C b c B' C' b' c' : F zero)
      → A => IdV B C b c
      → A' => IdV B' C' b' c'
      → isEqset B C
      → isEqset B' C'
      → (q : isEqset B B')   
      → (r : isEqset C C')   
      → isEqel b b' B B' q
      → isEqel c c' C C' r 
      → isEqset A A' -}

  isSet : F zero → Set
  isSet A = isEqset A A
    
  isEqel : F zero → F zero → (A : F zero) → isSet A → Set
  isEqel a a' A p = ?

  isEl : F zero → (A : F zero) → isSet A → Set
  isEl a A p = isEqel a a A p

  isEqel a a' A p → isEl a A p
  
{-  isEqel a a' A A' (IdEqset B C b c B' C' b' c' d d' p p' q r x y)
    = (isEqel b c B C p)
    × (isEqel b' c' B' C' p')
    × (a => refV)
    × (a' => refV)

mutual
  data isEqTy : F zero → F zero → Set where
    NEqTy : {A A' : F zero}
      → A => NV
      → A' => NV
      → isEqTy A A'
    piEqTy : {A A' : F zero} → (B B' : F zero) → (C C' : F one)
      → A => piV B C
      → A' => piV B' C'
      → (p : isEqTy B B')   
      → ((x x' : F zero) → isEqTm x x' B B' p → isEqTy (C [ x ]) (C' [ x' ]))
      → isEqTy A A'
    setEqTy : {A A' : F zero}
      → A => setV
      → A' => setV
      → isEqTy A A'
    IdEqTy : {A A' : F zero} → (B C b c B' C' b' c' : F zero)
      → A => IdV B C b c
      → A' => IdV B' C' b' c'
      → (q : isEqTy B B')   
      → (r : isEqTy C C')
      → isEqTy B C
      → isEqTy B' C'
      → isEqTm b b' B B' q
      → isEqTm c c' C C' r 
      → isEqTy A A'
      
  isEqTm : F zero → F zero → (A A' : F zero) → isEqTy A A' → Set
  isEqTm a a' A A' (NEqTy d d') = isEqN a a'
  isEqTm a a' A A' (piEqTy B B' C C' d d' p q) = (x x' : F zero)
    → (y : isEqTm x x' B B' p)
    → isEqTm (a # x) (a' # x') (C [ x ]) (C' [ x' ]) (q x x' y)
  isEqTm a a' A A' (setEqTy d d') = isEqset a a'
  isEqTm a a' A A' (IdEqTy B C b c B' C' b' c' d d' q r p p' x y)
    = (isEqTm b c B C p)
    × (isEqTm b' c' B' C' p')
    × (a => refV)
    × (a' => refV)

-- the last clause implies equality reflection

isTy : F zero → Set
isTy A = isEqTy A A

-- refEqTy : (A : F zero) → isTy A → isEqTy A A
-- refEqTy A p = p

isEqTm₁ : F zero → F zero → (A : F zero) → isTy A → Set
isEqTm₁ a a' A p = isEqTm a a' A A p

isTm :  F zero → (A : F zero) → isTy A → Set
isTm a A p = isEqTm₁ a a A p
-}

