-- Module      : Eser.Filters
-- Description : Sketch of the 'filter'-version of localisible predicates.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- # Big-picture summary
--
-- This story is about an inductive way of constructing certain predicates
-- on decidable equivalence relations on enumerable types.
--
-- The idea is as follows.
-- Let A = {a₀, a₁, a₂, a₃, ...} ≃ ℕ be the enumerable type.
-- Identify equivalence relations with normalisation functions:
-- f : ℕ → ℕ
-- f (f n) ≡ f n
-- f n ≤ n
-- So an equivalence relation is an assignment of normal forms to terms of A.
-- For every prefix of A, denoted Aₙ = {a₀, a₁, ..., aₙ₋₁},
-- corresponding to {0, 1, ..., n-1} under the A ≃ ℕ equivalence.
-- We can build an equivalence relation by inductively extending, for all n : ℕ,
-- a partial equivalence relation fₙ : Fin n → Fin n
-- by choosing the normal form of n, extending the function 
-- to Fin (1+n) → Fin(i+n). We start with the empty relation at n = 0.
--
-- Which choices are available?
-- * One existing normal of fₙ, i.e., a number in the image of fₙ.
-- * Make n a new normal form, i.e., the least element of a new equivalence
-- class.
--
-- ## Filters
--
-- Now, a 𝐅𝐈𝐋𝐓𝐄𝐑 restricts those choices.
-- Consequently, this restricts the possible equivalence relations one can
-- construct.
-- We say that a normalisation function f satisfies a filter F, if 
-- all fₙ₌₁ extend fₙ with a choice that F(fₙ) allows.
-- Thus, every filter gives rise to a predicate on equivalence relations.
--
-- We implement filters as functions mapping restricted normalisation functions
-- (fₙ can be encoded as a vector of numbers of length n) to Bool.
-- This allows to easily compose filters by pointwise taking their ∧.
-- 
-- If one can prove that there is a series of choices such that all are allowed
-- by a filter, then one can extract a normalisation function from the filter;
-- for example, by picking the maximum allow choice at every point.
-- This normalisation function f then, by construction,
-- satisfies the filter, and also f (f n) ≡ f n and f n ≤ n.
--
-- The latter two conditions could also have been implemented as filters,
-- but instead we build those two conditions in our representation of
-- restrictions such that they hold by construction -- we are not interested in
-- functions that are not normalisation functions anyway.
--
-- ## Restriction Coherent families of predicates
--
-- Another concept we introduce are "Restriction Choherent families of
-- predicates", or just '𝐑𝐞𝕔𝕠's for short.
-- They are families P of predicates on restrictions of nf functions,
-- such that if P (f₁₊ₙ) ≡ true then also P (fₙ) ≡ true.
-- They are in a bijective correspondence with filters,
-- up to extensionality: for every predicate implementable as a filter
-- there exists a reco that also implements it, and vice versa.
--------------------------------------------------------------------------------

module Eser.Filters where

-- Imports are sorted in order of dependence:
open import Eser.Filters.Base                      public 
open import Eser.Filters.Conversions.NFFunToExence public 
open import Eser.Filters.PointwiseProperties       public 
open import Eser.Filters.Conversions.FilterToReco  public 


