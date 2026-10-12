-- Module      : Eser.Relation.Binary.Path
-- Description : Paths where each step exists in one of two relations.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- A `Path R S x y` is a constructive proof 
-- that the reflexive-symmetric-transitive closure
-- of R ∪ S relates x to y.
--
-- Informally it consists of a number
--      k : ℕ
-- and elements 
--      a₁ a₂ , ... , aₖ
-- such that
--      xTa₁Ta₂Ta₃T...TaₖTy
-- where
--      aTb ≔ aRb ∨ bRa ∨ aSb ∨ bSa ∨ a≡b 
--
-- (the last option adds reflexivity).
--
--
-- I came up with two inductive definitions, and I didn't know which one was
-- better; so I implemented both and showed they are logically equivalent
-- (so not ≃ but just implications both ways).
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat
open import Data.Nat.Properties -- using (<-trans)
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Data.Unit
open import Relation.Binary.Core using () renaming (_⇒_ to _⊆_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions using (Transitive)
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function hiding (_↔_)
open import Relation.Binary.Structures

open import Eser.Aux using (_↔_)

open import Eser.Equivalences

module Eser.Relation.Binary.Path {A : Set} (R S : A → A → Set) where

data Path : A → A → Set where
    empty : (x : A) → Path x x
    step 
        : {x y z : A}
        → R x y ⊎ R y x ⊎ S x y ⊎ S y x
        → Path y z
        → Path x z

-- Path concatenation.
path-trans
    : {x y z : A}
    → Path x y
    → Path y z
    → Path x z
path-trans {x} {y} {z} (empty x) p = p
path-trans {x} {y} {z} (step v q) p = step v (path-trans q p)

path-sym
    : {x y : A}
    → Path x y
    → Path y x
path-sym {x} {x} (empty x) = empty x
path-sym {x} {z} (step {y = y} (inj₁ Rxy) p) =
    -- Note the types:
    --               p : y ⇝ z
    --      path-sym p : z ⇝ y
    path-trans  (path-sym p) (step (inj₂ $ inj₁ Rxy)  (empty x))
path-sym {x} {z} (step {y = y} (inj₂ (inj₁ Ryx)) p) = 
    path-trans  (path-sym p) (step (inj₁ Ryx)  (empty x))
path-sym {x} {z} (step {y = y} (inj₂ (inj₂ (inj₁ Sxy))) p) =
    path-trans  (path-sym p) (step (inj₂ $ inj₂ $ inj₂ Sxy) (empty x))
path-sym {x} {z} (step {y = y} (inj₂ (inj₂ (inj₂ Syx))) p) =
    path-trans  (path-sym p) (step (inj₂ $ inj₂ $ inj₁ Syx) (empty x))

-- Alternative formulation.
data Path' : A → A → Set where
    p-atomic
        : {x y : A}
        → R x y ⊎ S x y
        → Path' x y
    p-refl 
        : (x : A) 
        → Path' x x
    p-sym 
        : {x y : A} 
        → Path' x y 
        → Path' y x
    p-trans 
        : {x y z : A} 
        → Path' x y
        → Path' y z
        → Path' x z

Path→Path' : {x y : A} → Path x y → Path' x y
Path→Path' {x} {x} (empty x) = p-refl x
Path→Path' {x} {z} (step {y = y} (inj₁ Rxy) p) = 
    p-trans (p-atomic (inj₁ $ Rxy)) (Path→Path' p)
Path→Path' {x} {z} (step {y = y} (inj₂ (inj₁ Ryx)) p) =
    p-trans (p-sym $ p-atomic $ inj₁ Ryx) (Path→Path' p)
Path→Path' {x} {z} (step {y = y} (inj₂ (inj₂ (inj₁ Sxy))) p) =
    p-trans (p-atomic (inj₂ $ Sxy)) (Path→Path' p)
Path→Path' {x} {z} (step {y = y} (inj₂ (inj₂ (inj₂ Syx))) p) =
    p-trans (p-sym $ p-atomic $ inj₂ Syx) (Path→Path' p)

Path'→Path : {x y : A} → Path' x y → Path x y
Path'→Path {x} {y} (p-atomic (inj₁ Rxy)) = step (inj₁ Rxy) (empty y)
Path'→Path {x} {y} (p-atomic (inj₂ Sxy)) = 
    step (inj₂ $ inj₂ $ inj₁ Sxy) (empty y)
Path'→Path {x} {x} (p-refl x) = empty x
Path'→Path {x} {y} (p-sym p) = 
    path-sym $ Path'→Path p
Path'→Path {x} {z} (p-trans {y = y} p q) = 
    path-trans (Path'→Path p) (Path'→Path q)
