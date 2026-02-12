-- Unused definitions related to lists.

module deprecated/Liststuff where

open import Data.List
open import Level
--------------------------------------------------------------------------------
-- ListToType
-- Interpreting the elements of a list as a type.
--------------------------------------------------------------------------------

data ListToType {ℓ : Level.Level} {A : Set ℓ} : List A → Set ℓ where
    first : (a : A) → ListToType (a ∷ [])
    cons  : (a : A) (as : List A) → ListToType (a ∷ as)
    inj   : (a : A) (as : List A) (v : ListToType as) → ListToType (a ∷ as)

data ListToType {ℓ : Level.Level} {A : Set ℓ} : List A → Set ℓ where
    idx : (i : Indices L) → ListToType L
