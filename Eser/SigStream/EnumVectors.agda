-- Module      : Eser.SigStream.EnumVectors
-- Description : Enumerate ℕ-vectors of same length and same sum.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Vec
open import Data.List.Membership.Propositional
open import Data.List renaming (_∷_ to _∷L_) hiding (sum)
open import Function hiding (_↔_)

open import Eser.Logic

module Eser.SigStream.EnumVectors where

enumVecs : (m w : ℕ) → List (Vec ℕ (suc m))
    -- Drop all remaining weights in only remaining cell.
enumVecs 0 w = Data.List.[ w ∷ [] ]
    -- We are out of budget, fill the rest of the vector with 0s.
enumVecs (suc m) 0 = Data.List.map (0 ∷_) (enumVecs m 0)
enumVecs (suc m) (suc w) = 
    -- Drop one more weight at the current position.
    Data.List.map incrFirst (enumVecs (suc m) w)
    Data.List.++
    -- Don't drop any more weight here, and move to the next position.
    Data.List.map (0 ∷_) (enumVecs m (suc w))
    where
        incrFirst : {m : ℕ} → Vec ℕ (suc m) → Vec ℕ (suc m)
        incrFirst (x ∷ xs) = (suc x) ∷ xs

test = enumVecs 3 3

correctWeights : (m w : ℕ) → {v : Vec ℕ (suc m)} → v ∈ (enumVecs m w) → sum v ≡ w
correctWeights m w {v} v∈L = ?
