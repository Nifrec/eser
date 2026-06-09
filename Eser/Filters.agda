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

module Eser.Filters where

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

--------------------------------------------------------------------------------
-- Representation of restrictions of normalisation functions
--------------------------------------------------------------------------------
-- We could have used functions `Fin n → Bool` or `Vec ℕ n`,
-- but then the conditions `f (f n) ≡ f n` and `f n ≤ n`
-- must either be omitted or given externally.
-- More convenient is to use correct-by-construction vectors.
-- They are a bit like fresh lists, but instead of a freshness condition
-- on appendable elements
-- we have a constraint set of choices of appendable elements.
-- This set of choices depends on the *entire* existing list,
-- unlike in fresh lists where the appendum needs to be < than all elements in
-- the list.
--
-- There are three constructors:
-- 1. empty: the canonical normalisation function on ∅.
-- 2. newNF: extend a nf function on {0, 1, ..., n-1} 
--  to {0, 1, ..., n} by making n a new normal form.
-- 3. oldNF: extend a nf function f on {0, 1, ..., n-1} 
--  to {0, 1, ..., n} by normalising n to an existing normal form of f.
--
-- Note that oldNF requires the type of normal-forms of f.
-- We define those via mutual induction.
-- It has three constructors:
-- 1. here: if the last element of a NFRestr is a normal form, 
--  then pick that one.
-- 2. earlier-new: pick a normal form (not the last one!) of a NFRestr
--  whose last element is a normal form.
-- 3. earlier-old: pick a normal form of a NFRestr
--  whose last element is NOT a normal form.
--
-- NOTE: earlier-old takes two normal forms as input.
-- Don't confure them: the first is the normal form of the last element of the
-- NFRestr, which we need just to express the index in the type. 
-- The second is the normal form that the constructor tries to describe.

data NFRestr : ℕ → Set 
data NFS : {n : ℕ} → NFRestr n → Set

data NFRestr where
    empty : NFRestr 0
    newNF 
        : {n : ℕ} 
        → NFRestr n 
        → NFRestr (ℕ.suc n)
    oldNF 
        : {n : ℕ}
        → (r : NFRestr n)   --^ Function to extend.
        → NFS r             --^ Existing normal form.
        → NFRestr (ℕ.suc n)
    
data NFS where
    here 
        : {n : ℕ} 
        → (r : NFRestr n) 
        → NFS (newNF r)
    earlier-new
        : {n : ℕ} 
        → (r : NFRestr n) 
        → NFS r
        → NFS (newNF r)
    earlier-old
        : {n : ℕ} 
        → (r : NFRestr n) 
        → (c : NFS r)       --^ Normal form of last element of r.
        → NFS r             --^ Normal form that we are now describing.
        → NFS (oldNF r c)

