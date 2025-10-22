-- Module      : StreamGrid.Alphabet
-- Description : Representation of alphabets of atomic path pieces.
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Philosophically: what is an alphabet?
-- It is a set A with the following properties:
-- 1. It is not empty.
-- 2. We can form lists (strings) over it.
-- 3. It is finite.
-- 4. It is linearly ordered 
--  (hence strings over A are lexicographically ordered).

-- TODO: figure out how to get the module structure correct.
module Alph2 where

-- TODO: probably not all of these are needed.
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Fin
open import Data.Sum
open import Data.Unit
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

Alphabet : Set → Set
data NonEmptySet (A : Set) : Set
FinIterable : Set → Set

Alphabet A = (NonEmptySet A) × (FinIterable A)

data NonEmptySet A where
    witness : A → NonEmptySet A

FinIterable A = Σ[ n ∈ ℕ ] ∀ P → ((Fin n → P) → (A → P))
