-- Iterating a dependent function whose codomain mismatches its domain
-- only by the application of a function 'g'.
depGIter
    : {A : Set}
    → {B : A → Set}
    → (g : A → A → A)
    → (f : {a : A} → B a → Σ[ d ∈ A ] (B $ g a d))
    → ℕ → Σ[ a ∈ A ] B a → Σ[ a ∈ A ] B a
    --^ The final type is iterable!
depGIter {A} {B} g f 0 (a , b) = (a , b)
depGIter {A} {B} g f (suc n) (a , b) = 
    let (a' , b') = depGIter {A} {B} g f n (a , b)
    in
    let (d , b'') = f {a'} b'
    in
    (g a' d , b'')

getWeight : {C : ℕ → Set} → (g : ℕ → ℕ → ℕ) → (w : ℕ) → Σ[ h ∈ ℕ ] C (g h w) → ℕ
getWeight {C} g w (h , t) = g h w
