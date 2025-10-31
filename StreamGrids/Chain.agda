-- Module      : StreamGrids.Chain
-- Description : Definition of a Chain (strict total linear order)
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Contents of this file:

module StreamGrids.Chain where

-- #TODO: probably not all of these are needed.
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.Empty
open import Data.Fin
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.String
open import Data.Sum
open import Data.Unit
open import Data.Vec
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

-- Strict `<` relations of the form `x_1 < x_2 < x_3 < ...`.
-- AKA 'linear orders'.
Chain 
    : {A : Set} 
    → Rel A 0ℓ 
    → Set
Chain {A} _<_ 
    = (Transitive _<_)
    × (Irreflexive _≡_ _<_)
    × (Total _<_)
    × (Asymmetric _<_)
