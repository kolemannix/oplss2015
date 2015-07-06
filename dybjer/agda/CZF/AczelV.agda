module CZF.AczelV where

open import MLTT.MLTT

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

V : Set
V = W U T

-- equality as bisimulation, cf isomorphism

_≈_ : V → V → Set
sup a v ≈ sup a' v' = ((i : T a) → Σ (T a') (λ i' → v i ≈ v' i')) × 
                      ((i' : T a') → Σ (T a) (λ i → v' i' ≈ v i))

-- sup a v = sup a' v' = (f : T a → T a') x (forall i : T a. v i ≈ v' (f i)) x
--                      (f' : T a' → T a) x (forall i' : T a'. v' i' ≈ v (f' i'))

-- extensional membership

_∈_ : V → V → Set
u ∈ sup a v = Σ (T a) (λ i → u ≈ v i)

≈-refl : (u : V) → u ≈ u
≈-refl (sup a v) = ((λ i → i , ≈-refl (v i)) , (λ i → i , ≈-refl (v i)))

≈-sym : (u v : V) → u ≈ v → v ≈ u
≈-sym (sup a v) (sup a' v') (p , p') = (p' , p)

{-
Exercise: prove transitivity of ≈!

Exercise: prove the axiom of extensionality

_iff_ : Set → Set → Set
A iff B = (A → B) × (B → A)

extL : (x y z : V) → (x ≈ y) iff (z ∈ x → z ∈ y)
-}

∅ : V
∅ = sup n₀ R₀

∅-axiom : (x : V) → x ∈ ∅ → N₀
∅-axiom c (() , v) 

_∪_ : V → V → V
sup a b ∪ sup a' b' = sup (a ⊕ a') (D b b')

-- Exercise: Prove the ∪-axiom:
-- ∪-axiom : (a b c : V) → ((c ∈ (a ∪ b)) iff ((c ∈ a) + (c ∈ b)))
-- ∪-axiom (sup a b) (sup a₁ b₁) c = ({!!} , {!!})
-- Exercise: prove that ∪ preserves ≈
-- Exercise: define disjoint union
-- Exercise (hard): define the function space in V!

-- Natural numbers:
-- 0 = ∅
-- succ x = x ∪ { x }

[_] : V → V
[ a ] = sup n₁ (λ x → a)

zeroV = ∅

succV : V → V
succV x = x ∪ [ x ]

oneV = [ zeroV ]

ω : V
ω = sup n (R ∅ (λ x y → succV y))

-- a bigger ordinal

ω+ω : V
ω+ω = sup (n ⊕ n) (D (R ∅ (λ x y → succV y)) (R ω (λ x y → succV y)))

-- Unordered pairs:

n₂ : U
n₂ = n₁ ⊕ n₁

pairV : V → V → V -- unordered pair
pairV a b = sup n₂ (D (λ _ → a) (λ _ → b))


