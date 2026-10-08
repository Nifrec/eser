-- Module      : Eser.Relation.Binary.Path
-- Description : Paths where each step exists in one of two relations.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Path R S x y
-- is a finite sequence x = z_1 < z_2 < ... < z_k = y
-- such that each z_i is related to z_{1+i} by either R or S.
-- E.g. 1 R 2 S 5 R 7 R 10
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions using (Transitive)
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)

module Eser.Relation.Binary.Path where

data <Path (R S : ℕ → ℕ → Set) : ℕ → ℕ → Set where
    laststep 
        : {x y : ℕ} 
        → x < y 
        → R x y ⊎ S x y 
        → <Path R S x y
    addstep
        : {x y z : ℕ}
        → x < y
        → y < z
        → R x y ⊎ S x y
        → <Path R S y z
        → <Path R S x z

-- Paths where one of the two relations is uninhabited and the other
-- is transitive, are just this last relation.
path-uninhabited-right
    : {R S : ℕ → ℕ → Set}
    → ((x y : ℕ) → ¬ (S x y))
    → Transitive R
    → <Path R S ⊆ R
-- Proof: induction on the `<Path R S x y`.
path-uninhabited-right {R} {S} ¬S trans-R x y p = ?
