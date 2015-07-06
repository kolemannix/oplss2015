module LF.Combinators where

-- explicit polymorphism
-- unicode
-- ^C^L - type-check file

I : (X : Set) → X → X
I = λ X x → x

-- wildcard: I = λ _ x → x
-- Church-style: I = λ (X : Set) (x : X) → x
-- fp-style: I X x = x

-- implicit argument, polymorphism, anonymous function

I₂ : {X : Set} → X → X
I₂ = λ x → x

-- Normalize with ^C^N only works for closed expressions

-- fp-style, named function

I₃ : {X : Set} → X → X
I₃ x = x

-- insert implicit arguments (i) in the right place -- not a good examples

I₄ : {X : Set} → X → X
I₄ {X} x = x

-- (ii) by variable name (changing X to Y)

I₅ : {X : Set} → X → X
I₅ {X = X} x = x

-- infix declaration
-- show ?, give (put expression with ?),
-- commands with cursor in hole:
-- ^C^SPC - give
-- ^C^R - refine (put outermost, more general)
-- ^C^T - type of hole
-- ^C^A - auto

_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → X → Z
(g ∘ f) x = g (f x)

-- exercises: define other combinators: K, S, swap, etc. Define their dependently typed variants

