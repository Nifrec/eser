-- Module      : Eser.Correspondences
-- Description : Theorems about correspondences between DecRel and NFFun.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

-- The conversions RelToFun and FunToRel form an 
-- isomorphism 'up to proj₁ homotopy'.
open import Level
open import Data.Bool hiding (_≤_ ; _<_)
open import Data.Bool.Properties using (¬-not ; not-¬)
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Vec hiding (restrict)
open import Relation.Nullary -- Needed for with-abstractions on decidable ≡.
open import Function hiding (_↔_)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; ≤-<-trans ; n≤0⇒n≡0 
                                       ; n≤1+n ; m≤n⇒m<n∨m≡n ; ≡ᵇ⇒≡)
open ≡-Reasoning

open import Eser.Logic using (elimCaseLeft ; elimCaseRight)

open import Eser.Aux
open import Eser.EqRel.Definitions
open import Eser.EqRel.Conversions

module Eser.EqRel.Correspondences where

--------------------------------------------------------------------------------
-- Preservation of properties
-- The isomorphism-up-to-proj₁-homotopies preserves localisible properties.
--
-- More precisely:
-- Let P = (Prel, Ploc) be a localisible property,
-- then
-- (1) Prel R            <-> AllRestr (RelToFun R) Ploc
-- (2) Prel (FunToRel) f <-> AllRestr f Ploc
--------------------------------------------------------------------------------
open import Eser.EqRel.LocalisiblePred
open LocalisiblePred

-- (1) This direction is trivial, since it holds by definition
-- of a localisible property.
RelToFunPresvProps
    : (P : LocalisiblePred)
    → (R : EqRel)
    → Prel P R ↔ AllRestr ((proj₁ ∘ RelToFun) R) (Ploc P)
RelToFunPresvProps P R = correspondence P R

applyEqArgs 
    : {A B C : Set}
    → {a a' : A}
    → {b b' : B}
    → (_app_ : A → B → C)
    → (a ≡ a')
    → (b ≡ b')
    → (a app b ≡ a' app b')
applyEqArgs {A} {B} {C} {a} {a'} {b} {b'} _app_ a≡a' b≡b' =
    begin 
    a app b
    ≡⟨ cong (_app b) a≡a' ⟩
    a' app b
    ≡⟨ cong (a' app_) b≡b' ⟩
    a' app b'
    ∎
    
-- If f ≈ g
-- then λn.(restrict n f) ≈ λn.(restrict n g)
-- i.e., they pointwise output the same vectors.
homotRestrictLift
    : {f g : ℕ → ℕ}
    → (f ≈ g)
    → (n : ℕ)
    → (restrict n f) ≡ (restrict n g)
homotRestrictLift {f} {g} f≈g ℕ.zero = refl
homotRestrictLift {f} {g} f≈g (ℕ.suc n) = 
    let fn≡gn = f≈g n
    in
    let restOfVectorsEqual : restrict n f ≡ restrict n g
        restOfVectorsEqual = homotRestrictLift {f} {g} f≈g n
    in
    applyEqArgs _∷_ fn≡gn restOfVectorsEqual


    
-- Lemma for proving (2):
-- if f ≈ g then f locally satisfies a LocProp
-- iff g locally satisfies it.
-- (This is an advantage of local properties: for properties
-- on relations we *cannot* show `R≈S → (Prel R ↔ Prel S)`).
-- First a sub-lemma that proves only the "→" direction.
-- The bigger "↔" follows from symmetry (note ≈ is symmetric).
homotsPreserveAllRestrSat→
    : {f g : ℕ → ℕ}
    → (f ≈ g)
    → (Ploc : LocPred)
    → AllRestr f Ploc → AllRestr g Ploc
homotsPreserveAllRestrSat→ {f} {g} f≈g Ploc AllRestrF n = 
    subst (λ vec → Ploc n vec) (homotRestrictLift f≈g n) (AllRestrF n)

-- Two-direction version of previous lemma.
homotsPreserveAllRestrSat
    : {f g : ℕ → ℕ}
    → (f ≈ g)
    → (Ploc : LocPred)
    → AllRestr f Ploc ↔ AllRestr g Ploc
homotsPreserveAllRestrSat f≈g Ploc = 
    let LtoR = homotsPreserveAllRestrSat→ f≈g Ploc
    in
    let RtoL = homotsPreserveAllRestrSat→ (≈-sym f≈g) Ploc
    in
    (LtoR , RtoL)

FunToRelPresvProps→
    : (P : LocalisiblePred)
    → (f : NFFun)
    → Prel P (FunToRel f) 
    → AllRestr (proj₁ f) (Ploc P)
FunToRelPresvProps→ (localisiblePred Prel Ploc corresp) f PrelR =
    let R : EqRel
        R = FunToRel f
    in
    let H : AllRestr ((proj₁ ∘ RelToFun ∘ FunToRel) f ) Ploc
        H = proj₁ (corresp R) PrelR
    in
    let FRFf≈f = (proj₁ ∘ RelToFun ∘ FunToRel) f ≈ (proj₁ f)
        FRFf≈f = FRFHomot f
    in
    homotsPreserveAllRestrSat→ FRFf≈f Ploc H

FunToRelPresvProps←
    : (P : LocalisiblePred)
    → (f : NFFun)
    → AllRestr (proj₁ f) (Ploc P)
    → Prel P (FunToRel f) 
FunToRelPresvProps← (localisiblePred Prel Ploc corresp) f PlocF =
    -- We cannot apply the definition of a localisible property
    -- because f is not of the shape `RelToFun R`.
    -- However, we can map f first to a relation and then back to a function f',
    -- which is of the right shape, and by FRFHomot still homotopic to f itself.
    let R = FunToRel f
    in
    let f' = proj₁ (RelToFun (FunToRel f))
    in
    let f'≈f : f' ≈ proj₁ f
        f'≈f = FRFHomot f
    in
    let PlocF' : AllRestr f' Ploc
        PlocF' = λ n → subst (λ restr → Ploc n restr)
                    (homotRestrictLift {proj₁ f} {f'} (≈-sym f'≈f) n)
                    (PlocF n)
    in
    proj₂ (corresp R) PlocF'

-- (2) That FunToRel preserves properties is not so trivial.
FunToRelPresvProps
    : (P : LocalisiblePred)
    → (f : NFFun)
    → Prel P (FunToRel f) ↔ AllRestr (proj₁ f) (Ploc P)
FunToRelPresvProps P f = (FunToRelPresvProps→ P f , FunToRelPresvProps← P f)
