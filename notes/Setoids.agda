-- Module      : Setoids
-- Description : ∞-Setoids and n-truncated higher Setoids
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Higher setoids with composability of arrows on all levels.
-- They don't satisfy all the coherences of higher groupoids.
--------------------------------------------------------------------------------

open import Level renaming (suc to lvlsuc)
open import Data.Nat
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function.Structures
open import Function hiding (_↔_)

open import Eser.Equivalences.Notation using (_≃_)
open import Eser.Equivalences.Properties using (≃-trans)

module Setoids where

IsSubtype : Set → Set → Set
IsSubtype X Y = Σ[ i ∈ (Y → X) ] IsInjection _≡_ _≡_ i
-- Singleton types over A.
data El {A : Set} : A → Set where
    el _ : (a : A) → El a

IsComposable
    : {A : Set}
    → {hom : Set}
    → IsSubtype (Σ[ a ∈ A ] Σ[ b ∈ A ] (El a ≃ El b)) hom
    → Set
IsComposable {A} {hom} (i , inj-i) =
    (f' g' : hom)
    → (a b c : A)
    → (f : El a ≃ El b)
    → (g : El b ≃ El c)
    → i f' ≡ (a , b , f)
    → i g' ≡ (b , c , g)
    → Σ[ g'∘f' ∈ hom ] i g'∘f' ≡ (a , c , ≃-trans f g)

-- n-truncated higher setoid.
data Setoid (A : Set) : ℕ → Set → Set₁ where
    zero-lvl
        : (hom : Set)
        → (sub : IsSubtype (Σ[ a ∈ A ] Σ[ b ∈ A ] (El a ≃ El b)) hom)
        → IsComposable sub
        → Setoid A 0 hom
    add-lvl
        : {n : ℕ}
        → {hom' : Set}
        → Setoid A n hom'
        → (hom : Set)
        → (sub : IsSubtype (Σ[ p ∈ hom' ] Σ[ q ∈ hom' ] (El p ≃ El q)) hom)
        → IsComposable sub
        → Setoid A (suc n) hom

_⊂_ : {A : Set} 
    → {n : ℕ} 
    → {X Y : Set} 
    → Setoid A n X 
    → Setoid A (suc n) Y 
    → Set₁
_⊂_ {A} {n} {X} s (add-lvl {n} {Z} s' _ _ _) = 
    Σ[ eq ∈ (Z ≡ X) ] (s ≡ subst (Setoid A n) eq s')

-- Like an Exence, but then for setoid restrictions instead of
-- equivalence-relation-constrictions.
∞-Setoid : (A : Set) → Set₁
∞-Setoid A = Σ[ lvl ∈ ((n : ℕ) → Σ[ X ∈ Set ] (Setoid A n X)) ]
           ((n : ℕ) → (proj₂ $ lvl n) ⊂ (proj₂ $ lvl (suc n)))
