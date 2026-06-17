-- Module      : Eser.Filters.Resurface
-- Description : Lift a sub-NFRestr of r of the form `newNF r'` to a NFS of r.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)

open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n)

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_ ; restIsProofIrrel)
open import Eser.Logic

open import Eser.Filters.Base
open import Eser.Filters.Properties 

module Eser.Filters.Resurface

-- #TODO: cleanup imports
