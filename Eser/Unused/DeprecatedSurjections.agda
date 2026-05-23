
--------------------------------------------------------------------------------
-- Notation for surjections
--------------------------------------------------------------------------------
-- In my font, '↠' looks really messed up. So define a synonym for it:
infixr 1 _->>_
_->>_ : Set → Set → Set
A ->> B = A ↠ B

--------------------------------------------------------------------------------
-- Basic surjection properties.
--------------------------------------------------------------------------------
module _ where
    open import Function.Properties.Surjection

    ->>-refl : Reflexive _->>_
    ->>-refl = Function.Properties.Surjection.refl

--------------------------------------------------------------------------------
-- Lemmas
--------------------------------------------------------------------------------
-- One can project a surjection out of any equivalence.
equiv-impl-surj
    : {A B : Set}
    → A ≃ B
    → A ->> B
equiv-impl-surj {A} {B} A≃B = surj
    where
        A→B : A → B
        A→B = Inverse.to A≃B
        surj = LeftInverse.surjection $ Inverse.leftInverse A≃B
