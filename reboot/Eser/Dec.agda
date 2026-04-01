-- Module      : Eser.Dec
-- Description : Tools for working with decidable types.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- When defining a function f via a case distinction on a decidable
-- type (e.g., "foo x y with x ≟ y"),
-- then anything you want to prove about the function will need to make the same
-- case distinction, and you typically want f to normalise within
-- your proof.
-- This file provides tools for doing so.
--
-- The main idea is that your proof has two sublemmas,
-- one for the case "yourDecision ≡ yes p" and one for the case
-- "yourDecision ≡ no ¬p"; the sublemmas are in a different context and (by the
-- J rule) can assume these cases to be refl, allowing f to normalise.
-- Your top-level proof then makes a case distinction.
-- Below are some function that give terms of type 
-- "yourDecision ≡ yes p" and "yourDecision ≡ no ¬p" that serve as input
-- to the sublemmas.


-- #TODO: remove unused imports.
open import Level
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties 
    renaming (setoid to mk-≡-setoid)
open import Relation.Nullary
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)
open import Data.Fin.Properties 

open import Function.Related.TypeIsomorphisms
open import Function
open import Function.Properties.Inverse hiding (refl ; trans ; sym)
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Data.Product.Function.NonDependent.Propositional using (_×-↔_)

open import Eser.Equivalences.Notation
open import Eser.Stdlib using (fin-≡-irrelevant)

module Eser.Dec where

dec-as-case 
    : {A : Set} 
    → {P : A → Set} 
    → (a : A) 
    → (f : (a' : A) → (Dec (P a'))) 
    → ((Σ[ p ∈ (P a) ](f a ≡ yes p)) ⊎ (Σ[ ¬p ∈ (¬ (P a)) ](f a ≡ no ¬p)))
dec-as-case {A} {P} a f with (f a)
... | yes p = inj₁ (p , refl)
... | no ¬p = inj₂ (¬p , refl)

-- If you have *some* proof for P a,
-- then the decision function f must output "yes".
dec-yes-case
    : {A : Set} 
    → {P : A → Set} 
    → (a : A) 
    → (f : (a' : A) → (Dec (P a'))) 
    → P a
    → Σ[ p ∈ (P a) ](f a ≡ yes p)
dec-yes-case {A} {P} a f p with dec-as-case {A} {P} a f
... | inj₁ z = z
... | inj₂ (¬p , _) = ⊥-elim (¬p p)

-- If you have *some* proof for ¬ (P a),
-- then the decision function f must output "no".
dec-no-case
    : {A : Set} 
    → {P : A → Set} 
    → (a : A) 
    → (f : (a' : A) → (Dec (P a'))) 
    → ¬ P a
    → Σ[ ¬p ∈ ¬ (P a) ](f a ≡ no ¬p)
dec-no-case {A} {P} a f ¬p with dec-as-case {A} {P} a f
... | inj₁ (p , _) = ⊥-elim (¬p p)
... | inj₂ z = z
