-- Module      : Eser.Filters.Congruence.ForSignature
-- Description : Traditional and filter def congruence coincide for signatures.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- This is a sanity check that the ReplaceRespLocal filter 'works as intended'.
--
-- For Signatures, the filter definition of congruence (ReplaceRespLocal)
-- and the 'traditional' definition (IsCongruence) coincide,
-- in the sense that an equivalence relation satisfies the one predicate
-- iff it satisfies the other.
-- We prove this indirectly; we prove that ReplaceRespGlobal coincides
-- with IsCongruence; this suffices,
-- because the logical equivalence of the local and global
-- notions is already proven in the module Filters.Congruence.

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_ ; _≟_ ; _≤?_ )
open import Data.Bool.Properties using (T-≡)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open ≡-Reasoning
open import Relation.Nullary
open import Relation.Binary.Definitions using (Decidable ; DecidableEquality 
    ; tri< ; tri≈ ; tri>)
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_ ; id)
open import Data.Maybe
open import Data.Maybe.Properties using (just-injective)

open import Data.Nat.Properties using (
    ≤-refl 
    ; ≤-trans 
    ; <-trans
    ; n≤1+n 
    ; ≡⇒≡ᵇ
    ; <-irrelevant
    ; n<1+n
    ; n≮0
    ; <-≤-trans
    ; ≤-<-trans
    ; m≤n⇒m<n∨m≡n
    ; n≮n
    ; ≰⇒>
    )

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun ; FunToRel)
open import Eser.Aux using (_↔_ ; _≈_ ; doubleSubst ; irrel-×-closure ; uip
    ; restIsProofIrrel
    )
open import Eser.Logic using 
    (true≢false 
    ; ≡→≡ᵇ 
    ; ≡ᵇ→≡ 
    ; decEqReflection
    ; decEqCoReflection
    ; is-false-to-not-true
    ; not-true-to-is-false
    )
open import Eser.NatTriples

open import Eser.Filters.Base
open import Eser.Filters.Properties
open import Eser.Filters.Resurface
open import Eser.Filters.PointwiseProperties
open import Eser.Filters.Conversions.NFFunToExence
open import Eser.Filters.ReplaceStructs
open import Eser.Filters.ReplaceStructs.ForSignature
open import Eser.Filters.Congruence

module Eser.Filters.Congruence.ForSignature where

            
--------------------------------------------------------------------------------
-- 𝟔. ReplaceResp specialises to IsCongruence for Signatures
--------------------------------------------------------------------------------
open ReplaceResp toReplaceStruct
theo-ReplaceResp-is-IsCongr
    : (R : DecEquiv)
    → ReplaceRespGlobal R ↔ IsCongruence R
theo-ReplaceResp-is-IsCongr R = ?
