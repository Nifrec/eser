-- Module      : Eser.Filters.allNFRestrReachable
-- Description : Converting a NFFun to extensions-sequence, and inversity proof.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- For every NFRestr there actually a restriction of some normalisation
-- function.
-- This ensures that the datatype `NFRestr` has no garbage instantiations.
-- This fact was important in the design of the _♥_ relation.
--------------------------------------------------------------------------------

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

--open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n ; 1+n≰n
--    ; ≤-irrelevant
--    ; <-irrelevant
--    ; m<1+n⇒m<n∨m≡n
--    ; <-≤-trans
--    ; ≤-<-trans
--    ; m≢1+n+m
--    ; <-trans
--    ; n<1+n
--    ; <⇒≤ 
--    ; m<n⇒m≤1+n 
--    ; ≤⇒≯ 
--    ; m≤n⇒m<n∨m≡n
--    ; n≮n
--    )
--module ≤R = Data.Nat.Properties.≤-Reasoning

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
--open import Eser.Aux using (_↔_ ; _≈_ ; restIsProofIrrel ; Sm≤n→m≤n ; 1+n≮n 
--                           ; doubleSubst 
--                           ; depSubst
--                           ; tri-≡
--                           ; tri-<
--                           )
--open import Eser.Logic

open import Eser.Filters.Base
open import Eser.Filters.Properties 
open import Eser.Filters.Resurface

open import Eser.Filters.Conversions.NFFunToExence
module Eser.Filters.Conversions.NFFunToExenceRedo where



theo-all-NFRestr-reachable
    : {n : ℕ}
    → (r : NFRestr n)
    → Σ[ f ∈  NFFun ](r ≡ restrict f n)
theo-all-NFRestr-reachable {n} r = ?
