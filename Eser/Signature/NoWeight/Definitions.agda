-- Module      : Eser.Signature.NoWeights.Definitions
-- Description : Definitions of the no-weight-annotated open and closed terms.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
open import Level
open import Data.Nat
open import Data.Nat.Properties

open import Eser.Card
open import Eser.Signature.Definitions
open import Eser.Aux

module Eser.Signature.NoWeight.Definitions where

data OpenTermsNW {μ ζ : ℕ∞} (S : Signature μ ζ) : ℕ → Set where
    mk-nullary-nw 
        : (c : cardToSet μ) 
        → OpenTermsNW S 0
    mk-multiary-nw 
        : (c : cardToSet ζ) 
        → OpenTermsNW S (arity {μ} {ζ} {S = S} c)
    giveArg-nw
        : {m : ℕ} 
        → (t : OpenTermsNW {μ} {ζ} S (ℕ.suc m))
        → (a : OpenTermsNW {μ} {ζ} S 0)
        → OpenTermsNW {μ} {ζ} S m
    
-- Closed terms: open terms needing no more arguments.
-- For the NoWeight representation, we do not need to distinguish
-- between `ClosedTermsNW` and `AllTerms := Σ[ w ∈ ℕ ] (ClosedTermsW w)`
ClosedTermsNW : {μ ζ : ℕ∞} (S : Signature μ ζ) → Set
ClosedTermsNW {μ} {ζ} S =  OpenTermsNW {μ} {ζ} S 0

