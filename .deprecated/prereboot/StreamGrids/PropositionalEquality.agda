-- Module      : StreamGrids.PropositionalEquality
-- Description : Auxiliary lemmas about propositional equality
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality

module StreamGrids.PropositionalEquality where

-- According to the book PROGAM=PROOF, this is in the standard library,
-- but I cannot find it.
coe : {A B : Set} → A ≡ B → A → B
coe p x = subst (λ A → A) p x
