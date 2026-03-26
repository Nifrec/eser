-- Module      : Eser.Equivalences.Properties
-- Description : General theorems about commonly used equivalences
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties 
    renaming (setoid to mk-≡-setoid)
open import Relation.Nullary
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)

open import Function
open import Function.Properties.Inverse hiding (refl ; trans ; sym)

open import Eser.Equivalences.Notation

module Eser.Equivalences.Properties where

≃-refl : {A : Set} → (A ≃ A)
≃-refl = ↔-refl

mk≃ = mk↔

-- If a ≡ a' then B a ≃ B a'.
≃-subst
    : {A : Set}
    → {B : A → Set}
    → {a a' : A}
    → a ≡ a'
    → B a ≃ B a'
≃-subst {A} {B} {a} a≡a' = subst (λ x → B a ≃ B x) a≡a' (≃-refl {B a})

-- If Ba ≃ Ca for all a ∈ A then Σ[a∈A]Ba ≃ Σ[a∈A]Ca.
rewr-≃-under-Σ
    : {A : Set}
    → {B C : A → Set}
    → ((a : A) → (B a ≃ C a))
    → (Σ[ a ∈ A ] B a) ≃ (Σ[ a ∈ A ] C a)
rewr-≃-under-Σ H = ?
