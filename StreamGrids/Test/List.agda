-- Module      : StreamGrids.Test.List
-- Description : Testcases for StreamGrids.List
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------


module StreamGrids.Test.List where

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
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary


open import StreamGrids.List


DL : List (List ℕ)
DL = ( 1 ∷ 2 ∷ 3 ∷ [] ) ∷ ( 4 ∷ 5 ∷ 6 ∷ [] ) ∷ []
-- Indices live in Fin n, not in ℕ, so we cannot use arabics as notation...
testGetEL : DL ,, (suc zero) ,, (suc (suc zero)) ≡ 6
testGetEL = refl

SL : List ℕ
SL = 2 ∷ 0 ∷ 2 ∷ 5 ∷ []
SLAtOneIsZero : 0 ∈ SL
SLAtOneIsZero = (suc zero) , refl

testGetIdx : getListIdx SLAtOneIsZero ≡ suc zero
testGetIdx = refl

test∈∈ : 6 ∈∈ DL
test∈∈ = (suc zero , suc (suc zero) , refl) -- 6 occurs at index pair (1, 2).

testFlatLength : flatLength DL ≡ 6
testFlatLength = refl
