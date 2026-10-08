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
open import Relation.Binary.Core using () renaming (_⇒_ to _⊆_)
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

path-map-left
    : {R S T : ℕ → ℕ → Set}
    → R ⊆ T
    → <Path R S ⊆ <Path T S
path-map-left R⊆T {x} {y} (laststep x<y (inj₁ xRy)) = 
    laststep x<y $ inj₁ $ R⊆T xRy
path-map-left R⊆T {x} {y} (laststep x<y (inj₂ xSy)) = laststep x<y (inj₂ xSy)
path-map-left {R} {S} {T} R⊆T {x} {y} 
    (addstep {x} {z} {y} x<z z<y (inj₁ xRz) p) =
    let xTz = R⊆T xRz in
    addstep {T} {S} x<z z<y (inj₁ xTz) $ path-map-left R⊆T {z} {y} p
path-map-left R⊆T {x} {y} (addstep {x} {z} {y} x<z z<y (inj₂ xSz) p) =
    addstep x<z z<y (inj₂ xSz) $ path-map-left R⊆T p

-- Paths where one of the two relations is uninhabited and the other
-- is transitive, are just this last relation.
path-uninhabited-right
    : {R S : ℕ → ℕ → Set}
    → ((x y : ℕ) → ¬ (S x y))
    → Transitive R
    → <Path R S ⊆ R
-- Proof: induction on the `<Path R S x y`.
path-uninhabited-right {R} {S} ¬S trans-R {x} {y} 
    (laststep x<y (inj₁ xRy)) = xRy
path-uninhabited-right {R} {S} ¬S trans-R {x} {y} 
    (laststep x<y (inj₂ xSy)) = ⊥-elim $ ¬S x y xSy
path-uninhabited-right {R} {S} ¬S trans-R {x} {y} 
    (addstep {x} {z} {y} x<z z<y (inj₁ xRz) p) = trans-R xRz zRy
        where
            zRy : R z y
            zRy = path-uninhabited-right ¬S trans-R {z} {y} p
path-uninhabited-right {R} {S} ¬S trans-R {x} {y} 
    (addstep {x} {z} {y} _ _ (inj₂ xSz) _) = ⊥-elim $ ¬S x z xSz
