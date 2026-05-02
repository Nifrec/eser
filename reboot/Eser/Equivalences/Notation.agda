-- Module      : Eser.Equivalences
-- Description : Notation for equivalence used in Eser.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- In this library, an `equivalence` between types A and B
-- is a pair of function f : A → B and g : B → A
-- whose compositions are homotopic to the identity functions on A and B,
-- i.e., f(g(b)) ≡ b and g(f(a)) ≡ a.
-- This coincides with the definition of `Inverse` in the stdlib
-- in Function.Bundles initialised with the _≡_ relation.
--
-- The standard library gives this the notation _↔_, but Eser
-- uses _≃_ instead, since  A ↔ B looks more like (A → B) × (B → A);
-- a much weaker statement!

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties
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
open import Data.Vec 

open import Function
open import Function.Properties.Inverse hiding (refl ; trans ; sym)
open import Relation.Binary.Reasoning.Syntax

open import Eser.Aux using (_≈_)
module Eser.Equivalences.Notation where

--------------------------------------------------------------------------------
-- Notation for equivalences
--------------------------------------------------------------------------------

infixr 1 _≃_
_≃_ : Set → Set → Set
A ≃ B = A ↔ B

-- Convenient getter methods for the _≃_ relation.
-- We get functions A → B and B → A whose compositions
-- are homomorphic to the identities on A and B respectively.
module _ {A B : Set} (A≃B : A ≃ B) where
    open import Function.Consequences.Propositional 
        using (inverseˡ⇒strictlyInverseˡ 
              ; inverseʳ⇒strictlyInverseʳ
              ; inverseʳ⇒injective
              )
    ≃-to : A → B
    ≃-to = Inverse.to A≃B

    ≃-from : B → A
    ≃-from = Inverse.from A≃B

    ≃-toFrom : (≃-to ∘ ≃-from) ≈ id {_} {B}
    ≃-toFrom = inverseˡ⇒strictlyInverseˡ $ Inverse.inverseˡ A≃B

    ≃-fromTo : (≃-from ∘ ≃-to) ≈ id {_} {A}
    ≃-fromTo = inverseʳ⇒strictlyInverseʳ $ Inverse.inverseʳ A≃B

    ≃-from-injective : Injective _≡_ _≡_ ≃-from 
    ≃-from-injective = Bijection.injective $ ↔⇒⤖ (↔-sym A≃B)

module ≃-Reasoning where
  open begin-syntax {A = Set} _≃_ {_≃_} id public
  open ≃-syntax {A = Set}     _≃_ _≃_ ↔-trans ↔-sym public
  open end-syntax {A = Set}   _≃_ ↔-refl public
open ≃-Reasoning public

module EquivShorthands
    {A B : Set}
    (A≃B : A ≃ B)
    where

    φ : A → B
    φ = ≃-to A≃B

    φ⁻¹ : B → A
    φ⁻¹ = ≃-from A≃B

    φ∘φ⁻¹≈id : (φ ∘ φ⁻¹) ≈ id
    φ∘φ⁻¹≈id = ≃-toFrom A≃B

    φ⁻¹∘φ≈id : (φ⁻¹ ∘ φ) ≈ id
    φ⁻¹∘φ≈id = ≃-fromTo A≃B

    elift : (A → A) → B → B
    elift f = φ ∘ f ∘ φ⁻¹

module EquivShorthandsForEnumSet
    {A : Set}
    (A≃ℕ : A ≃ ℕ)
    where

    φ : A → ℕ
    φ = ≃-to A≃ℕ

    φ⁻¹ : ℕ → A
    φ⁻¹ = ≃-from A≃ℕ

    φ∘φ⁻¹≈id : (φ ∘ φ⁻¹) ≈ id
    φ∘φ⁻¹≈id = ≃-toFrom A≃ℕ

    φ⁻¹∘φ≈id : (φ⁻¹ ∘ φ) ≈ id
    φ⁻¹∘φ≈id = ≃-fromTo A≃ℕ

    -- Smaller-term relation: the ℕ-encoding of t' is ℕ-< smaller than t.
    _«_ : Rel A 0ℓ
    t' « t = (φ t') < (φ t)
    -- Smaller-than-or-equal
    _«=_ : Rel A 0ℓ
    t' «= t = (t' « t) ⊎ (t' ≡ t)
