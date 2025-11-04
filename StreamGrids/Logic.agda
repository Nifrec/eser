-- Module      : StreamGrids.Logic
-- Description : Basic logic auxiliary functions
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

module StreamGrids.Logic where

open import Data.Sum
open import Relation.Nullary
open import Data.Empty

-- #TODO: probably already in library?
-- This also works with `¬ (A ⊎ B)`, as it is a shorthand for `C := empty`.
orWeakenLeft : {A B C : Set} → (A ⊎ B → C) → A → C
orWeakenLeft p = λ a → p (inj₁ a)
orWeakenRight : {A B C : Set} → (A ⊎ B → C) → B → C
orWeakenRight p = λ b → p (inj₂ b)

elimCaseLeft : {A B : Set} → (A ⊎ B) → (¬ A) → B
elimCaseLeft (inj₁ a) ¬A = ⊥-elim (¬A a)
elimCaseLeft (inj₂ b) = λ _ → b
elimCaseRight : {A B : Set} → (A ⊎ B) → (¬ B) → A
elimCaseRight (inj₁ a) = λ _ → a
elimCaseRight (inj₂ b) ¬B = ⊥-elim (¬B b)
