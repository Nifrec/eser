-- Module      : Eser.Equivalences.ReasoningTest
-- Description : Test if the ≃⟨ ⟩ reasoning works
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
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
open import Relation.Binary.Reasoning.Syntax

open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties

module Eser.Equivalences.ReasoningTest where
lemma : {n : ℕ} → (Fin (n ∸ n) ≃ Fin 0)
lemma {n} = 
        begin 
            Fin (n ∸ n)
        ≃⟨ ≃-subst {ℕ} {Fin} {n ∸ n} {0} (H n)  ⟩
            Fin 0 
        ∎
        where
            H : (m : ℕ) → m ∸ m ≡ 0
            H 0 = refl
            H (suc m) = H m
