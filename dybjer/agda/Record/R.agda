module Record.R (A₁ : Set) (A₂ : A₁ → Set) (a₁ : A₁) (a₂ : A₂ a₁) where

-- R = (x₁ : A₁) × A₂ x

record R : Set where
  constructor <_,_>
  field
    x₁ : A₁
    x₂ : A₂ x₁

-- r = (a₁ , a₂)

r : R
r = record {x₁ = a₁; x₂ = a₂}

r' : R
r' = < a₁ , a₂ >

-- projections

π₁ : R → A₁
π₁ = R.x₁

π₂ : (x : R) → A₂ (π₁ x)
π₂ = R.x₂

-- surjective pairing

open import MLTT.MLTT hiding (R) renaming (r to refl)

surjective-pairing : (x : R) → I R x < π₁ x , π₂ x >
surjective-pairing x = refl
