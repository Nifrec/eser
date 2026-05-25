-- Module      : Eser.Signature.NoWeights
-- Description : Representation of terms of a signature with weight annotations.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Eser.Signature.Definitions defines the `OpenTerms` of a signature
-- as an inductive type indexed by
-- (1) the weight of a term
-- (2) the number of open argument-holes of a term
--
-- For enumerating the terms, indeed both indices are needed:
-- the proof of enumeration uses <-rec on the weights to inductively number all
-- terms of weight 0, then of weight 1, then of weight 2, etc.
--
-- But the weight indices are very annoying when destructing a term via
-- pattern-matching, since the weight of a giveArg-constructed term
-- is `wₐ + wₜ` and Agda tends to fail unifying `w ≗ wₐ + wₜ`.
--
-- The solution is simply to also define an alternative representation
-- of open terms without weight index.
-- (We must keep the argument-holes index, since it is used as a constraint
-- which terms we can build; we should avoid applying arguments to a closed
-- type!)
--------------------------------------------------------------------------------

module Eser.Signature.NoWeight where
    open import Eser.Signature.NoWeight.Definitions public
    open import Eser.Signature.NoWeight.Properties public
