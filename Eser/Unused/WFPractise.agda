-- Module      : Eser.WFPractise
-- Description : Experiment to figure out the WF-recursion tools of the stdlib.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- The stdlib gives a lot of tools for getting Well-Founded recursion principles
-- out of a Well-Founded relation, but those tools are poorly documented and
-- confusingly typed (too many layers of abstraction).

open import Level
open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Induction.WellFounded
open import Data.Nat.Induction
open import Data.Nat.Properties using (n<1+n)

module Eser.WFPractise where

P : ℕ → Set
P n = ℕ × ℕ

test : (n : ℕ) → P n
test = <-rec {0ℓ} P f
    where
        f : (x : ℕ) → ({y : ℕ} → (y < x) → P y) → P x
        f 0 rec = (0 , 0)
        f (suc n) rec = rec {n} (n<1+n n)

