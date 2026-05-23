-- Module      : Eser.README
-- Description : Façade file giving a roadmap to the library
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- This file gives a roadmap of the Eser library following the structure
-- of the paper.

module Eser.README where

--------------------------------------------------------------------------------
-- §3 Equivalence relations and normal form functions
--------------------------------------------------------------------------------
-- §3 is the submodule `Eser.EqRel`.

-- Definitions of decidable equivalence relations and normal-form functions:
open import Eser.EqRel.Definitions using (NFFun) renaming (DecEquiv to EqRel)

-- Conversions between decidable equivalence relations
-- and normal-form functions, named ρ and ρ⁻¹ in the paper:
open import Eser.EqRel.Conversions using () 
    renaming (RelToFun to ρ ; FunToRel to ρ⁻¹)

-- Theorem 1 is split into two lemmas in the implementation:
open import Eser.EqRel.Correspondences using () renaming ()

