-- Module      : Eser.Examples.Integers.NFFix
-- Description : Proof that nf (nf n) ≡ nf n
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Proof that the normal form function satisfies, for all n : ℕ:
-- nf-fix : nf (nf n) ≡ nf n
--------------------------------------------------------------------------------

open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties

module Eser.Examples.Integers.NFFix where

open import Eser.Examples.Integers.Definitions
open import Eser.Examples.Integers.DirectEncProperties

nf-fix : (n : ℕ) → elift f (elift f n) ≡ elift f n
nf-fix = elift-fix f f-fix
