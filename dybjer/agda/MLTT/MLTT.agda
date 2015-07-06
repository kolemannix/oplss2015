------------------------------------------------------------------------
-- 5. Martin-Löf type theory 
------------------------------------------------------------------------

-- We present the intensional monomorphic version of Martin-Löf type theory from 1986,
-- see Nordström, Petersson, and Smith 1989. (It is not exactly the same theory
-- since Agda has (x : A) -> B : Set provided A : Set, B : (x : A) -> Set, 
-- whereas (x : A) -> B in Martin-Löf type theory is only a type.)
-- Notes:
--   Peano Arithmetic + Intuitionistic Predicate Logic with equality = Heyting Arithmetic
--   prop = Set
module MLTT.MLTT where

-- generalization of Curry-Howard encoding of predicate logic

data N₀ : Set where

R₀ : {C : N₀ -> Set}
  -> (c : N₀)
  -> C c
R₀ ()

data  N₁ : Set where
  0₁ : N₁

R₁ : {C :  N₁ -> Set}
  → C 0₁
  → (c :  N₁)
  → C c
R₁ d 0₁ = d

data _+_ (A B : Set) : Set where
  i : A → A + B
  j : B → A + B

D : {A B : Set} → {C : A + B → Set}
  → ((a : A) → C (i a))
  → ((b : B) → C (j b))
  → (c : A + B)
  → C c
D d e (i a) = d a
D d e (j b) = e b

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

E : {A : Set} → {B : A → Set} → {C : Σ A B → Set}
  → ((x : A) → (y : B x) → C (x , y))
  → (z : Σ A B) → C z
E d (x , y) = d x y

fst : {A : Set} → {B : A → Set} → Σ A B → A
fst (a , b) = a

snd : {A : Set} → {B : A → Set} → (c : Σ A B) → B (fst c)
snd (a , b) = b

-- in intensional type theory E (split) is not derivable from the projections,
-- hence it is taken as a primitive

data Π (A : Set) (B : A → Set) : Set where
  Λ : ((a : A) → B a) → Π A B

syntax Π A (λ x → B) = Π[ x ∈ A ] B

F :  {A : Set} → {B : A → Set} → {C : Π A B → Set}
  → ((b : (x : A) → B x) → C (Λ b))
  → (z : Π A B) → C z
F d (Λ b) = d b

-- in intensional type theory F (funsplit) is more general than application and -- taken as a primitive

-- In the Agda version of Martin-Löf type theory, the framework function
-- space (x : A) → B x more or less replaces Π A B.

data I (A : Set) (a : A) : A → Set where
  r : I A a a
-- I: Martin Luuh defined I as the identity type - the least reflexive relation

J : {A : Set} → {a : A}
  → (C : (y : A) → I A a y → Set)
  → C a r
  → (b : A) → (c : I A a b) → C b c
J C d a r = d

-- Agda's .-notation

data N : Set where
  O : N
  s : N → N

R : {C : N → Set} → C O → ((n : N) → C n → C (s n)) → (c : N) → C c
R d e O     = d
R d e (s n) = e n (R d e n)

-- added in Martin-Löf 1979 (cf Scott 1970)

data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) → (b : B a → W A B) → W A B

wrec : {A : Set} → {B : A → Set} → {C : W A B → Set} 
     → ((a : A) → (b : B a → W A B) → ((x : B a) → C (b x)) → C (sup a b)) 
     → (c : W A B) → C c
wrec {C = C} d (sup a b) = d a b (λ x → wrec {C = C} d (b x))

-- a universe a la Tarski introduced in Martin-Löf 1984

mutual
  data U : Set where
     n₀ : U
     n₁ : U
     _⊕_ : U → U → U
     σ : (a : U) → (T a → U) → U
     π : (a : U) → (T a → U) → U
     n : U
     w : (a : U) → (T a → U) → U
     i : (a : U) → T a → T a → U

  T : U → Set
  T n₀        = N₀
  T n₁        = N₁
  T (a ⊕ b)   = T a + T b
  T (σ a b)   = Σ (T a) (λ x → T (b x))
  T (π a b)   = Π (T a) (λ x → T (b x))
  T n         = N
  T (w a b)   = W (T a) (λ x → T (b x))
  T (i a b c) = I (T a) b c




