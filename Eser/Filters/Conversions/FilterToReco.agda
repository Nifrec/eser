-- Module      : Eser.Filters.Conversions.FilterToReco
-- Description : Converting a Filter to a Reco and back, plus inversity proof.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_)

open import Eser.Filters.Base
open import Eser.Filters.PointwiseProperties

module Eser.Filters.Conversions.FilterToReco where

--------------------------------------------------------------------------------
-- Correspondence Filters and Recos
--------------------------------------------------------------------------------
-- Remark: (recoToFilter ∘ filterToReco) F outputs a filter
-- that might be strictly stronger than F,
-- because the resulting filter disallows all of Choices r
-- if r contains an earlier choice that F disallows
-- (in implementation: 
-- see the `∧ (h r)` in the definition of h in filterToReco below).
-- This is necessary because the output of filterToReco must be coherent.
--
-- Note that this artefact is not problematic,
-- since it does not influence which normalisation
-- functions are accepted by the predicate that the filter encodes.
-- It just means that we cannot define the bijective correspondence directly as
-- a homotopy between input and output, but instead define it in acceptance
-- of normalisation functions.

filterToReco : Filter → Reco
filterToReco F = reco h H refl
    where
        h : {n : ℕ} → (r : NFRestr n) → Bool
        h {0} empty = true
        h {suc n} (newNF r) = (F r here) ∧ (h r)
        h {suc n} (oldNF r c) = (F r (earlier-new c)) ∧ (h r)
        H   : {n : ℕ}
            → (r : NFRestr n)
            → (s : NFRestr (ℕ.suc n))
            → r ⋖ s
            → h s ≡ true
            → h r ≡ true
        H {zero} empty s r⋖s hs = refl
        H {suc n} r s (⋖-newNF r) hs = {! !}
        H {suc n} r (oldNF r c) (⋖-oldNF r c) hs = {! !}

infixl 4 filterToReco
syntax filterToReco F = ↑ F

recoToFilter : Reco → Filter
recoToFilter = ?

infixl 4 recoToFilter
syntax recoToFilter P = ↓ P

Filter-to-pred : Filter → Predicate
Filter-to-pred F R = Filter-sats F (RelToFun R)

Reco-to-pred : Reco → Predicate
Reco-to-pred P R = Reco-sats P (RelToFun R)

theo-filter-reco-correspondence
    : (F : Filter)
    → (f : NFFun)
    → Filter-sats F f ↔ Filter-sats (↓ ↑ F) f
theo-filter-reco-correspondence F f = ?
    
theo-reco-filter-correspondence
    : (P : Reco)
    → (f : NFFun)
    → Reco-sats P f ↔ Reco-sats (↑ ↓ P) f
theo-reco-filter-correspondence P f = ?

--------------------------------------------------------------------------------
-- Auxiliary concepts used by proof of theo-filter-reco-correspondence
--------------------------------------------------------------------------------

-- G is stronger than F if G disallows any choice that F disallows.
-- G might disallow also choices that F allows.
stronger : Filter → Filter → Set
stronger F G = 
    {n : ℕ} 
    → (r : NFRestr n) 
    → (c : Choices r) 
    → F r c ≡ false 
    → G r c ≡ false

lemma-↓↑-stronger : (F : Filter) → stronger (↓ ↑ F) F
lemma-↓↑-stronger = ?

