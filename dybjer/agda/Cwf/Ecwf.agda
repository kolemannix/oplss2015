module Cwf.Ecwf where

postulate

-- the category of contexts and substitutions

  Ctxt : Set -- the set of objects
  _⇒_ : Ctxt -> Ctxt -> Set -- the hom-sets
  _==_ : {Δ Γ : Ctxt} -> Δ ⇒ Γ -> Δ ⇒ Γ -> Set -- equal arrows
  r : {Δ Γ : Ctxt} -> {γ : Δ ⇒ Γ}
    -> γ == γ -- reflexivity
  t : {Δ Γ : Ctxt} -> {γ γ' γ'' : Δ ⇒ Γ} 
    -> γ == γ' -> γ' == γ'' 
    -> γ == γ'' -- transitivity
  s : {Δ Γ : Ctxt} -> {γ γ' : Δ ⇒ Γ} 
    -> γ == γ' 
    -> γ' == γ -- symmetry
  _∘_ : {Θ Δ Γ : Ctxt} -> Δ ⇒ Γ -> Θ ⇒ Δ -> Θ ⇒ Γ -- composition
  compeq : {Θ Δ Γ : Ctxt} -> {γ γ' : Δ ⇒ Γ} -> {δ δ' : Θ ⇒ Δ} 
    -> γ ∘ δ ==  γ' ∘ δ' -- ... is an E-function
  id :  {Γ : Ctxt} -> Γ ⇒ Γ -- identity
  α : {Λ Θ Δ Γ : Ctxt} -> (θ : Λ ⇒ Θ) -> (δ : Θ ⇒ Δ) -> (γ : Δ ⇒ Γ) 
    -> (γ ∘ δ) ∘ θ == γ ∘ (δ ∘ θ) -- associativity
  l : {Γ : Ctxt} -> (γ : Γ ⇒ Γ) 
    -> id ∘ γ == γ -- left identity law
  ρ : {Γ : Ctxt} -> (γ : Γ ⇒ Γ) 
    -> γ ∘ id == γ -- right identity law

-- the family-valued functor - types and type substitution
 
  Ty : Ctxt -> Set -- the set of types in context
  _==₀_ : {Γ : Ctxt} -> Ty Γ -> Ty Γ -> Set -- equal types
  r₀ : {Γ : Ctxt} -> {A : Ty Γ} 
    -> A ==₀ A
  t₀ : {Γ : Ctxt} -> {A A' A'' : Ty Γ} 
    -> A ==₀ A' -> A' ==₀ A'' 
    -> A ==₀ A''
  s₀ : {Γ : Ctxt} -> {A A' : Ty Γ} 
    -> A ==₀ A' 
    -> A' ==₀ A
  _[_]₀ : {Δ Γ : Ctxt} -> (A : Ty Γ) -> (Δ ⇒ Γ) -> Ty Δ -- substitution in types
  subeq₀ : {Δ Γ : Ctxt} -> {A A' : Ty Γ} -> {γ γ' : Δ ⇒ Γ} 
    -> A ==₀ A' -> γ == γ' 
    -> A [ γ ]₀ ==₀ A' [ γ' ]₀ -- ... is an E-function
  subcomp₀ : {Θ Δ Γ : Ctxt} -> {A : Ty Γ} -> (γ : Δ ⇒ Γ) -> (δ : Θ ⇒ Δ) 
    -> A [ γ ]₀ [ δ ]₀ ==₀ A [ γ ∘ δ ]₀ -- functor law: preservation of composition
  subid₀ : {Γ : Ctxt} -> {A : Ty Γ} 
    -> (A [ id ]₀) ==₀ A -- functor law: preservation of identity

-- the family valued functor - terms and term substitution

  _⊢_ : (Γ : Ctxt) -> Ty Γ -> Set -- the set of terms
  _==₁_ : {Γ : Ctxt} -> {A : Ty Γ} -> Γ ⊢ A -> Γ ⊢ A -> Set -- equality of terms
  r₁ : {Γ : Ctxt} -> {A : Ty Γ} -> {a : Γ ⊢ A} 
    -> a ==₁ a
  t₁ : {Γ : Ctxt} -> {A : Ty Γ} -> {a a' a'' : Γ ⊢ A} 
    -> a ==₁ a' -> a' ==₁ a'' 
    -> a ==₁ a''
  s₁ : {Γ : Ctxt} -> {A : Ty Γ} -> {a a' : Γ ⊢ A} 
    -> a ==₁ a' 
    -> a' ==₁ a
  ι : {Γ : Ctxt} -> {A A' : Ty Γ} -> A' ==₀ A -> Γ ⊢ A -> Γ ⊢ A' -- type equality rule / transport map for E-families
  irr : {Γ : Ctxt} -> {A A' : Ty Γ} -> {p p' : A' ==₀ A} -> (a a' : Γ ⊢ A)
    -> a ==₁ a' -> ι p a ==₁ ι p' a' -- proof irrelevance of transport
  _[_]₁ : {Δ Γ : Ctxt} -> {A : Ty Γ} -> (a : Γ ⊢ A) -> (γ : Δ ⇒ Γ) -> Δ ⊢ A [ γ ]₀ -- substitution in terms
  subeq₁ : {Δ Γ : Ctxt} -> {A : Ty Γ} -> {a a' : Γ ⊢ A} -> {γ γ' : Δ ⇒ Γ} 
    -> a ==₁ a' -> (φ : γ == γ') 
    -> a [ γ ]₁ ==₁ ι (subeq₀ r₀ φ) (a' [ γ' ]₁) -- is an E-function
  subcomp₁ : {Θ Δ Γ : Ctxt} -> {A : Ty Γ} -> (a : Γ ⊢ A) -> (γ : Δ ⇒ Γ) -> (δ : Θ ⇒ Δ) 
    -> a [ γ ]₁ [ δ ]₁ ==₁ ι (subcomp₀ γ δ) (a [ γ ∘ δ ]₁) -- a functor law: preservation of composition
  subid₁ : {Γ : Ctxt} -> {A : Ty Γ}-> (a : Γ ⊢ A) 
    -> a [ id ]₁ ==₁ ι subid₀ a -- functor law: preservation of identity
 -- there are missing laws like (ι p a) [ γ ] == ι (p γ) (a [ γ ])

-- the terminal object 

  ε : Ctxt -- the empty context
  <> : {Γ : Ctxt} -> Γ ⇒ ε -- the empty substitution
  <>-! : {Γ : Ctxt} -> (γ : Γ ⇒ ε) -> γ == <> -- ... is the terminal arrow

-- context comprehension

  _,_ :  (Γ : Ctxt) -> Ty Γ -> Ctxt -- context extension
  p : {Γ : Ctxt} -> {A : Ty Γ} -> Γ , A ⇒ Γ -- first projection / display map
  q : {Γ : Ctxt} -> {A : Ty Γ} -> Γ , A ⊢ A [ p ]₀ -- second projection / last variable
  <_,_> : {Δ Γ : Ctxt} -> {A : Ty Γ} -> (γ : Δ ⇒ Γ) -> (a : Δ ⊢ A [ γ ]₀) -> Δ ⇒ Γ , A -- substitution extension
  paireq : {Δ Γ : Ctxt} -> {A : Ty Γ} ->  (γ γ' : Δ ⇒ Γ) -> (a : Δ ⊢ A [ γ ]₀) -> (a' : Δ ⊢ A [ γ' ]₀) 
    -> (φ : γ == γ') -> a ==₁ ι (subeq₀ r₀ φ) a' 
    -> < γ , a > == < γ' , a' > -- ... is an E-function
  ppair : {Δ Γ : Ctxt} -> {A : Ty Γ} -> (γ : Δ ⇒ Γ) -> (a : Δ ⊢ A [ γ ]₀) 
    -> p ∘ < γ , a > == γ -- first projection law
  qpair : {Δ Γ : Ctxt} -> {A : Ty Γ} -> (γ : Δ ⇒ Γ) -> (a : Δ ⊢ A [ γ ]₀) 
    -> q [ < γ , a > ]₁ ==₁ ι (t₀ (subcomp₀ p < γ , a >) (subeq₀ r₀ (ppair γ a))) a -- second projection law
  pair-! : {Δ Γ : Ctxt} -> {A : Ty Γ} -> (γ : Δ ⇒ Γ , A) 
    -> γ == < p ∘ γ , ι (s₀ (subcomp₀ p γ)) (q [ γ ]₁) > -- uniqueness law for context extension (cf surjective pairing)

infix 5 _==_  
infix 5 _==₀_  
infix 5 _==₁_
infix 10  _⇒_
infix 10 _⊢_
infixl 10 _,_
infixl 20 _[_]₀
infixl 20 _[_]₁
infixr 30 _∘_ 


