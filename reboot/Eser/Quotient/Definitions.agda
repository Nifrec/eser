-- Module      : Eser.Quotient.Definitions
-- Description : Defining a quotient type of an enumerable type.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Constructing quotient types
--
-- Given an enumerable type A with φ : A ≃ ℕ
-- and an equivalence relation represented by a normal-form function
-- f : NFFun,
-- we can define the quotient type φ / f 
-- whose terms are representatives of equivalence classes of funToRel f.
-- Those representatives, AKA normal forms, are the least elements
-- of equivalence classes in the enumertion of A according to φ.
-- Normal forms are exactly the fixpoints of f,
-- since f n ≤ n and f (f n) ≡ f n.
--
-- #TODO: also add support for A ≃ Fin n. Low priority because quotients can
-- obviously be constructed for such types.
--------------------------------------------------------------------------------

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties using (¬-not ; not-¬)
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_≤_ ; _≤?_)
open import Data.Vec hiding (restrict)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; ≤-<-trans ; n≤0⇒n≡0 
                                       ; n≤1+n ; m≤n⇒m<n∨m≡n ; _≤?_ ; ≰⇒≥)
open import Data.Fin.Properties using (toℕ<n)
open import Relation.Nullary -- Needed for with-abstractions on decidable ≡.
open import Function hiding (_↔_)


open import Eser.Equivalences
open import Eser.EqRel

module Eser.Quotient.Definitions where

-- Quotient type of an enumerated type A by a relation (the latter being
-- represented by a normal-form function).
_/_ : {A : Set} → (A ≃ ℕ) → NFFun → Set
_/_ {A} A≃ℕ (f , nfleqF , nffixF) = Σ[ a ∈ A ]( f a ≡ a)
