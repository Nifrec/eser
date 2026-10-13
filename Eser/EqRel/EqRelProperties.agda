-- Module      : Eser.EqRel.EqRelProperties
-- Description : Properties of and additional definitions on EqRel.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

--{-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions 
    using (Tri ; Reflexive ; Symmetric ; Transitive ; DecidableEquality)
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)

open import Eser.EqRel.Definitions
open import Eser.EqRel.Conversions
open import Eser.EqRel.Correspondences
open import Eser.Filters.PointwiseProperties

open import Eser.Aux using (_≈_ ; _≈≈_ ; _↔_ ; ↔-to ; ↔-from ; doubleCong)
open import Eser.Relation.Binary.Path

open import Eser.Filters.Conversions.NFFunToExence
open import Eser.Filters.Base
open import Eser.Filters.Properties
open import Eser.Filters.PointwiseProperties
open import Eser.Filters.Resurface

module Eser.EqRel.EqRelProperties where

--------------------------------------------------------------------------------
-- New definitions involving Exence and Filter
--------------------------------------------------------------------------------
-- These could not have defined in EqRel.Definitions because of circular import
-- problems.

Rel-sats : Filter → EqRel → Set
Rel-sats F R = NFFun-sats F (RelToFun R)

rel-to-exence : EqRel → Exence
rel-to-exence = restrict+ ∘ RelToFun

exence-to-rel : Exence → EqRel
exence-to-rel = FunToRel ∘ combine

-- Restriction of a relation to an NFRestr.
_↾_ : EqRel → (n : ℕ) → NFRestr n
R ↾ n = restrict (RelToFun R) n

-- Using an Exence as a relation.
ExRel : Exence → ℕ → ℕ → Set
ExRel E = (exence-to-rel E) relates_to_

--------------------------------------------------------------------------------
-- General properties
--------------------------------------------------------------------------------

relates-to-refl : (R : EqRel) → Reflexive (R relates_to_)
relates-to-refl = ?

relates-to-sym : (R : EqRel) → Symmetric (R relates_to_)
relates-to-sym = ?

relates-to-trans : (R : EqRel) → Transitive (R relates_to_)
relates-to-trans = ?

⊆-refl : (R : EqRel) → R ⊆ R
⊆-refl R x y xRy = xRy

--------------------------------------------------------------------------------
-- Conversion to Exence and back is bijection-up-to-funext.
--------------------------------------------------------------------------------
-- The function ℕ → ℕ → Bool underlying the relation outputted by FunToRel
-- is entirely determined by the function ℕ → ℕ underlying the input NFFun.
FunToRel-proof-irrel
    : (f g : NFFun)
    → (proj₁ f) ≈ (proj₁ g)
    → (proj₁ (FunToRel f)) ≈≈ (proj₁ (FunToRel g))
FunToRel-proof-irrel f'@(f , _ , _) g'@(g , _ , _) homot x y = 
    begin 
        proj₁ (FunToRel f') x y
    ≡⟨⟩
        f x ≡ᵇ f y
    ≡⟨ doubleCong _≡ᵇ_ (homot x) (homot y) ⟩
        g x ≡ᵇ g y
    ≡⟨⟩
        proj₁ (FunToRel g') x y
    ∎
    where
        open ≡-Reasoning
RFRHomot-nocurry
    : (R : EqRel) 
    → (proj₁ ∘ FunToRel ∘ RelToFun) R ≈≈ proj₁ R
RFRHomot-nocurry R x y = 
    -- That curry (uncurry f) ≡ f holds judgementally.
    -- `cong curry` also was not needed (and didn't even type check).
    begin 
        (proj₁ ∘ FunToRel ∘ RelToFun) R x y
    ≡⟨ RFRHomot R (x , y) ⟩
        (proj₁ R) x y
    ∎
    where
        open ≡-Reasoning

eqrel-exence-round-trip
    : (R : EqRel)
    → ((proj₁ ∘ FunToRel ∘ combine ∘ restrict+ ∘ RelToFun) R) ≈≈ (proj₁ R)
eqrel-exence-round-trip R x y =
    begin 
        (proj₁ ∘ FunToRel ∘ combine ∘ restrict+ ∘ RelToFun) R x y
    ≡⟨ FunToRel-proof-irrel f' f f'≈f x y ⟩
        (proj₁ ∘ FunToRel ∘ RelToFun) R x y
    ≡⟨ RFRHomot-nocurry R x y ⟩
        (proj₁ R) x y 
    ∎
    where
        open ≡-Reasoning
        f : NFFun
        f = RelToFun R
        f' : NFFun
        f' = (combine ∘ restrict+ ∘ RelToFun) R
        f'≈f : (proj₁ f') ≈ (proj₁ f)
        f'≈f = theo-combine∘restrict+ (RelToFun R)
    


--------------------------------------------------------------------------------
-- Properties of Filter satisfiability for equivalence relations
--------------------------------------------------------------------------------

exence-sat-to-rel-sat
    : {R : EqRel}
    → {F : Filter}
    → Exence-sats F (rel-to-exence R)
    → Rel-sats F R
exence-sat-to-rel-sat = ?

getchoice-to-relate
    : {R : EqRel}
    → {y : ℕ}
    → (c : Choices (restrict (RelToFun R) y))
    → c ≡ getChoiceFromExence (rel-to-exence R) y
    → R relates y to (choiceToℕ c)
getchoice-to-relate = ?

unique-choice-to-relate
    : {F : Filter}
    → {R : EqRel}
    → {y : ℕ}
    → (c : Choices (restrict (RelToFun R) y))
    → LocallyOneHot F (restrict (RelToFun R) y) c
    → R relates y to (choiceToℕ c)
unique-choice-to-relate = ?


