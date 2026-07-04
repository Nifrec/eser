-- Module      : Eser.Logic
-- Description : Basic logic auxiliary functions
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

module Eser.Logic where

open import Data.Sum
open import Relation.Nullary
open import Data.Empty

-- This also works with `¬ (A ⊎ B)`, as it is a shorthand for `A ⊎ B → ⊥` 
-- (i.e., special case with `C := ⊥`).
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

-- If X⊎Y and X→Z then Z⊎Y.
implCongrLeft
    : {X Y Z : Set}
    → X ⊎ Y
    → (X → Z)
    → Z ⊎ Y
implCongrLeft (inj₁ x) f = inj₁ (f x)
implCongrLeft (inj₂ y) f = inj₂ y

implCongrRight
    : {X Y Z : Set}
    → X ⊎ Y
    → (Y → Z)
    → X ⊎ Z
implCongrRight (inj₁ x) f = inj₁ x
implCongrRight (inj₂ y) f = inj₂ (f y)

--------------------------------------------------------------------------------
-- Logic on terms of Data.Bool (instead of on types-as-propositions)
--------------------------------------------------------------------------------
open import Data.Bool
open import Relation.Binary.PropositionalEquality

true≢false : true ≢ false
true≢false ()

-- If A ∧ B is true then both A and B are true.
∧-elim-left
    : (a b : Bool)
    → a ∧ b ≡ true
    → a ≡ true
∧-elim-left true true refl = refl
∧-elim-right
    : (a b : Bool)
    → a ∧ b ≡ true
    → b ≡ true
∧-elim-right true true refl = refl



