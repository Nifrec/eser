-- Stuff previously in Eser/Definitions.agda

-- Really local version of NFLeq : assume previous outputs are OK
-- already (f m ≤ m for all m < n), only check the last one (i.e., f n ≤ n).
NFLeqReallyLoc : LocProp
NFLeqReallyLoc 0 [] = ⊤
NFLeqReallyLoc (ℕ.suc n) v = last v ≤ n



--------------------------------------------------------------------------------
-- Correspondences up to homotopy
--
-- Both DecEquiv and NFFun have the form of
-- Σ[ g ∈ (A → B) ](a bunch of properties).
-- Let X and Y be types that have a similar form,
-- and let h : X → Y and k : Y → X.
-- We define X ≊ Y 
-- (In nvim Cornelis the default mapping for ≊ is \approxeq)
-- as
-- (1) for all (g , p) ∈ X, a homotopy π₁ k(h(g, p)) ≈ g
-- and
-- (2) for all (f , q) ∈ Y, a homotopy π₁ h(k(f, q)) ≈ f
-- So ≊ expresses 
-- "isomorphism up to homotopy and proof-relevance of the bunches of properties"
--------------------------------------------------------------------------------

-- FunsWithProps is the type of dependent functions A → B
-- with some properties.
FunsWithProps : {A : Set}
    {B : A → Set}
    → (((a : A) → B a) → Set)
    → Set
FunsWithProps {A} {B} Properties = Σ[ g ∈ ((a : A) → B a)](Properties g)

-- "Equivalence between types of functions-with-properties
-- up to first-projection-homotopy and proof-relevance of the properties".
record _≊_ 
    {A A' : Set}
    {B : A → Set}
    {B' : A' → Set}
    (P : ((a : A) → B a) → Set)
    (P' : ((a : A') → B' a) → Set)
    : Set
    where
    field
        leftToRight : FunsWithProps P  → FunsWithProps P'
        rightToLeft : FunsWithProps P' → FunsWithProps P
        almostInvL 
            : (F : FunsWithProps P) 
            → (proj₁ ∘ rightToLeft ∘ leftToRight) F ≈ proj₁ F
        almostInvR 
            : (F : FunsWithProps P')
            → (proj₁ ∘ leftToRight ∘ rightToLeft) F ≈ proj₁ F


-- #TODO: remove? currently it is more of a personal note.
--
-- If f, g : A → B → C
-- have that (f a b) ≡ (g a b),
-- then we can prove that 
--      λ(a, b) ∈ A×B → f a b
--  is homotopic to
--      λ(a, b) ∈ A×B → g a b
--  (and also that f a ≈ g a for all a : A,
--  but we CANNOT prove that f ≈ g without function extensionality).
doubleArgHomot
    : {A B C : Set}
    → (f g : A → B → C)
    → ((a : A) → (b : B) → f a b ≡ g a b)
    → uncurry f ≈ uncurry g
doubleArgHomot R S H = uncurry H


-- Equivalence between two types.
-- The stdlib uses an overly general definition
-- what requires also showing `n ≈₁ m → (f n) ≈₂ (f m)`
-- given setoids (N, ≈₁) and (M, ≈₂).
-- We just use propositional equality _≡_ for both the domain and codomain,
record HomotEquivalence (Left Right : Set) : Set where 
    field
        LR : Left → Right
        RL : Right → Left
        homotLRL : (RL ∘ LR) ≈ id
        homotRLR : (LR ∘ RL) ≈ id

_≊_ : Set → Set → Set
A ≊ B = HomotEquivalence A B

