-- Module      : StreamGrids.Fold
-- Description : Folding of finite sets
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

module StreamGrids.Fold where

open import Data.Fin
open import Data.List
open import Data.Nat
open import Relation.Binary.PropositionalEquality 

-- Restrict a function from a set with n+1 elements to a set with n elements.
constrain : {P : Set} → {n : ℕ} → (Fin (suc n) → P) → (Fin n → P)
constrain f m = f (inject₁ m)

-- Fold a finite set of n+1 elements using a binary operator.
-- This folds the greatest element to the left.
-- E.g., when folding `Fin 3` using `f` and `_+_`, the outcome is
-- `(f 2) + (f 1) + (f 0) + p`.
-- Note: the `fold` and `fold′` functions in `Data.Fin.Base` seem
-- to do something wholly different.
fold′′ : {P : Set} → {n : ℕ} → (Fin (suc n) → P → P) → P → P
fold′′ {P} {zero} comb p = comb zero p
fold′′ {P} {suc n} comb p = comb (fromℕ (suc n)) (fold′′ {P} {n} 
    (constrain comb) p)

--------------------------------------------------------------------------------
--  Testcases
--------------------------------------------------------------------------------
private
    -- Counting the number of elements in a set with 3+1 elements
    -- should give 4.
    checkFold1 : fold′′ {ℕ} {3} (λ x p → suc p) 0 ≡ 4
    checkFold1 = refl

    -- 3 + 2 + 1 + 0 + 0 = 6.
    checkFold2 : fold′′ {ℕ} {3} (λ x p →  Data.Nat._+_ (toℕ x) p) 0 ≡ 6
    checkFold2 = refl

    -- This check verifies the elements are folded in the right order
    -- (the previous checks use `_+_` which is commutative).
    checkFold3 : fold′′ {List ℕ} {3} (λ x p → (toℕ x) ∷ p) [] ≡ (3 ∷ 2 ∷ 1 ∷ 0 ∷ [])
    checkFold3 = refl

    -- Nonzero base case:
    -- 3 + 2 + 1 + 0 + 10 = 16.
    checkFold4 : fold′′ {ℕ} {3} (λ x p →  Data.Nat._+_ (toℕ x) p) 10 ≡ 16
    checkFold4 = refl 
