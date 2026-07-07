-- Module      : Eser.Filters.Congruence
-- Description : Initial sketch how to implement 'is-a-congruence' as a Filter.
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
open import Data.Maybe

open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n)

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_)

module Eser.Filters.Congruence where

--------------------------------------------------------------------------------
-- 𝐂𝐎𝐍𝐆𝐑𝐔𝐄𝐍𝐂𝐄
-- This story is about implementing the 'is-a-congruence' predicate
-- for relations over term algebras over signatures.
-- The low-level definition of 'congruence' depends on the operations in
-- the signature, but it is unpractical to reimplement congruence 
-- for every signature.
--
-- So instead we define a generalisation of 'congruence' for any 'ReplaceStruct',
-- which are abstractions capturing only the minimal features of term algebras
-- needed to define congruence.
-- ReplaceStructs are enumerable types together with an
-- 'is-argument-of'-relation denoted as _⊂_,
-- and a replacement operation allowing to swap 'arguments'.
-- We only impose the minimal set of axioms needed to define
-- the generalisation of 'congruence', which we call 'ReplaceRespecting'.
-- Consequently, not all ReplacementStructs correspond to term algebras;
-- for example, we do not require that replacing an 
-- argument in a term with the same argument
-- leaves the term unchanged, nor that changing an argument x in a term t by x'
-- gives a term actually containing x' as argument.
-- However, when specialising to ReplaceStructs that do correspond to actual
-- term algebras, one does recover the traditional notion of congruence.
--
-- We only consider enumerable term algebras T, 
-- so w.l.o.g. we omit the bijection T ≃ ℕ and just work directly on ℕ.
--
-- Concretely, we will do the following:
-- 1. Define ReplaceStructs.
-- 2. Define two notions of ReplaceRespecting (parametrised by a ReplaceStruct).
--   Recall that decidable equivalence relations correspond
--   to normalisation functions ℕ → ℕ, which correspond to extension-sequences
--   (Exences). We can define predicates globally on equivalence relations,
--   or locally as Filters that constrain choices for the equivalence class
--   of n when extending the domain a restricted 
--   equivalence relation from {0, ..., n-1} to {0, ..., n}.
--   The notions are:
-- 2.1. A global notion on equivalence relations ℕ → ℕ → Bool.
-- 2.2. A local notion implemented as a Filter.
-- 3. We prove that the global notion holds if and only if the local does.
--
-- Thereafter we will demonstrate this terse generalisation of congruence
-- 'works as intended' in practial contexts,
-- by specialising it to our implementation of signatures and term algebras
-- (from the modules in `Eser.Signature`, using the `Signatures` and
-- `ClosedTerms' of the `Eser` library):
-- 4. Show that the closed terms over any Signature from a ReplaceStruct.
-- 5. Define the traditional notion of 'congruence' (as a predicate
--  on relations).
-- 6. Show that a relation satisfies this notion of congruence
--  if and only if it satisfies the (global notion) of 'ReplaceRespecting'.
--------------------------------------------------------------------------------

