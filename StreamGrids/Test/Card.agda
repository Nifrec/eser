-- Module      : StreamGrids.Test.Card
-- Description : Testcases for StreamGrids.Card
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

-- TODO: probably not all of these are needed.
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.Empty
open import Data.Fin hiding (_<_)
open import Function using (Inverseᵇ)
open import Data.List
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Vec
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary


open import StreamGrids.Card

module StreamGrids.Test.Card where

--------------------------------------------------------------------------------
-- NequalsCardToSetElem testcases
--------------------------------------------------------------------------------

-- It does NOT hold that 2 ∈ ℕ equals 1 ∈ {0, 1}.
testℕComparison1 : ¬ (ℕequalsCardToSetElem {fin 2} 2 (suc zero))
testℕComparison1 ()

-- It does hold that 2 ∈ ℕ equals 2 ∈ {0, 1, 2, 3}.
testℕComparison2 : ℕequalsCardToSetElem {fin 4} 2 (suc (suc zero))
testℕComparison2 = refl

-- It does hold that 2 ∈ ℕ equals 2 ∈ ℕ
testℕComparison3 : ℕequalsCardToSetElem {∞} 2 2
testℕComparison3 = refl

-- It does NOT hold that 2 ∈ ℕ equals 0 ∈ ℕ
testℕComparison4 : ¬ (ℕequalsCardToSetElem {∞} 2 0)
testℕComparison4 ()

--------------------------------------------------------------------------------
-- cardToClipSuc
--------------------------------------------------------------------------------

one : Fin 3
one = suc zero

two : Fin 3
two = suc (suc zero)

-- Clipping occurs.
testClipSuc1 : clipSuc two ≡ two
testClipSuc1 = refl

-- No clipping occurs.
testClipSuc2 : clipSuc one ≡ two
testClipSuc2 = refl

-- Clipping occurs.
testCardToClipSuc1 : cardToClipSuc {fin 3} two ≡ two
testCardToClipSuc1 = refl

-- No clipping occurs.
testCardToClipSuc2 : cardToClipSuc {fin 3} one ≡ two
testCardToClipSuc2 = refl

-- No clipping ever occurs for finite inputs in the natural numbers case.
testCardToClipSuc3 : cardToClipSuc {∞} 10 ≡ 11
testCardToClipSuc3 = refl
