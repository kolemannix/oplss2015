module Id.Groupoid where

record Groupoid : Set₁ where
  field
    obj : Set
    hom : obj → obj → Set
    _∘_ : {x y z : obj} → hom y z → hom x y → hom x z
    id : {x : obj} → hom x x
    inv : {x y : obj} → hom x y → hom y x
    _==_ : {x y : obj} → hom x y → hom x y → Set
    α : {x y z s : obj} → (f : hom x y) → (g : hom y z) → (h : hom z s)
      → ((h ∘ g) ∘ f) == (h ∘ (g ∘ f))
    l : {x y : obj} → {f : hom x y} → (id ∘ f) == f
    r : {x y : obj} → {g : hom y x} → (g ∘ id) == g
    i : {x y : obj} → {f : hom x y} → ((inv f) ∘ f) == id
    j : {x y : obj} → {f : hom x y} → (f ∘ (inv f)) == id

-- example: small sets and bijections - a large groupoid

-- obj = Set
-- bij x y = (f : x → y) × (g : y → x)
