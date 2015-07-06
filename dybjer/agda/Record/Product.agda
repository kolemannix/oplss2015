module Record.Product where

-- Labelled records, Figure 11-7 in Pierce, are tuples with named components

record _×_ (A B : Set) : Set where
  field
    l1 : A
    l2 : B

-- This is like A × B but with labels l1 and l2. (Recall also that we have "surjective pairing" for records, cf lecture)

-- Instead of < a , b > we write

<_,_> : {A B : Set} -> A -> B -> A × B
< a , b > = record { l2 = b
                   ; l1 = a
                   }

-- and we then we can write _×_.l1  _×_.l2 for the projections (cf fst and snd):

fst : {A B : Set} -> A × B -> A
fst = _×_.l1 

snd : {A B : Set} -> A × B -> B
snd = _×_.l2

record _×'_ (A B : Set) : Set where
  constructor <_,_>'
  field
    l1 : A
    l2 : B


