-- Module      : Eser.Filters.Conversions.FilterToReco
-- Description : Converting a Filter to a Reco and back, plus inversity proof.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_)

open import Eser.Logic using (∧-elim-right)

open import Eser.Filters.Base
open Reco
open import Eser.Filters.Properties
open import Eser.Filters.Conversions.NFFunToExence
open import Eser.Filters.PointwiseProperties

module Eser.Filters.Conversions.FilterToReco where

--------------------------------------------------------------------------------
-- Correspondence Filters and Recos
--------------------------------------------------------------------------------
-- Remark: (recoToFilter ∘ filterToReco) F outputs a filter
-- that might be strictly stronger than F,
-- because the resulting filter disallows all of Choices r
-- if r contains an earlier choice that F disallows
-- (in implementation: 
-- see the `∧ (h r)` in the definition of h in filterToReco below).
-- This is necessary because the output of filterToReco must be coherent.
--
-- Note that this artefact is not problematic,
-- since it does not influence which normalisation
-- functions are accepted by the predicate that the filter encodes.
-- It just means that we cannot define the bijective correspondence directly as
-- a homotopy between input and output, but instead we define it via acceptance
-- of normalisation functions (and their alternative representation of Exences).

Reco-Exence-sats : Reco → Exence → Set
Reco-Exence-sats (reco P C 0K) (h , H) = (n : ℕ) → P (h n) ≡ true

Reco-NFFun-sats  : Reco → NFFun  → Set
Reco-NFFun-sats P f' = Reco-Exence-sats P (restrict+ f')

filterToReco : Filter → Reco
filterToReco F = reco P C refl
    where
        P : {n : ℕ} → (r : NFRestr n) → Bool
        P {0} empty = true
        P {suc n} (newNF r) = (F r here) ∧ (P r)
        P {suc n} (oldNF r c) = (F r (earlier-new c)) ∧ (P r)

        C   : {n : ℕ}
            → (r : NFRestr n)
            → (s : NFRestr (ℕ.suc n))
            → r ⋖ s
            → P s ≡ true
            → P r ≡ true
        C {zero} empty s r⋖s hs = refl
        C {suc n} r (newNF r) (⋖-newNF r) hs = ∧-elim-right (F r here) (P r) hs
        C {suc n} r (oldNF r c) (⋖-oldNF r c) hs 
            = ∧-elim-right (F r (earlier-new c)) (P r) hs

infixl 4 filterToReco
syntax filterToReco F = ↑ F

recoToFilter : Reco → Filter
recoToFilter (reco P C 0K) {n} r here = P (newNF r)
recoToFilter (reco P C 0K) {n} r (earlier-new c) = P (oldNF r c)

filterToReco-addChoice
    : (F : Filter)
    → {n : ℕ}
    → (r : NFRestr n)
    → (c : Choices r)
    → predicate (↑ F) (addChoice r c) 
      ≡ 
      (F r c) ∧ predicate (↑ F) r
filterToReco-addChoice F {n} r here = refl
filterToReco-addChoice F {n} r (earlier-new c) = refl

recoToFilter-addChoice 
    : (P' : Reco)
    → {n : ℕ}
    → (r : NFRestr n)
    → (c : Choices r)
    → (↓ P') r c ≡ predicate P' (addChoice r c)
recoToFilter-addChoice (reco P C 0K) {n} r here = refl
recoToFilter-addChoice (reco P C 0K) {n} r (earlier-new c) = refl


infixl 4 recoToFilter
syntax recoToFilter P = ↓ P

Filter-to-pred : Filter → Predicate
Filter-to-pred F R = NFFun-sats F (RelToFun R)

Reco-to-pred : Reco → Predicate
Reco-to-pred P R = Reco-NFFun-sats P (RelToFun R)

theo-filter-reco-filter-same-sat
    : (F : Filter)
    → (E : Exence)
    → Exence-sats F E ↔ Exence-sats (↓ ↑ F) E
theo-filter-reco-filter-same-sat F E@(h , H) = (LEFT , RIGHT)
    where
        LEFT : Exence-sats F E → Exence-sats (↓ ↑ F) E
        LEFT sat n = 
            let c = (getChoice (h n) (h (suc n)) (H n)) in
            begin 
                (↓ ↑ F) (h n) (getChoice (h n) (h (suc n)) (H n))
            ≡⟨⟩
            --≡⟨ cong ((↓ ↑ F) (h n)) (sym $ lemma-getChoice-exence n h H) ⟩
                (↓ ↑ F) (h n) c
            ≡⟨ recoToFilter-addChoice (↑ F) (h n) c ⟩
                predicate (↑ F) (addChoice (h n) c)
            --≡⟨ cong (predicate (↑ F)) (c-prop) ⟩
            --    predicate (↑ F) (h (suc n)) -- Rewrite to `addChoice (h n) c`
            ≡⟨ filterToReco-addChoice F (h n) c ⟩ -- addChoice lemma for filterToReco
                F (h n) c ∧ predicate (↑ F) (h n)
            ≡⟨ cong (_∧ (predicate $ ↑ F) (h n)) (sat n)  ⟩
                true ∧ (predicate $ ↑ F) (h n)
            ≡⟨⟩
                predicate (↑ F) (h n)
            ≡⟨ sublemma n refl ⟩
                true
            ∎
            where
                --c : Choices (h n)
                --c = proj₁ $ ⋖-to-addChoice (H n)
                --c-prop : addChoice (h n) c ≡ h (suc n)
                --c-prop = sym $ proj₂ $ ⋖-to-addChoice (H n)
                sublemma : (m : ℕ) → (n ≡ m) → predicate (↑ F) (h n) ≡ true
                sublemma zero refl = 
                    begin 
                        predicate (↑ F) (h n)
                    ≡⟨⟩
                        predicate (↑ F) (h 0)
                    ≡⟨ cong (predicate (↑ F)) (empty-is-unique-zero (h 0))  ⟩
                        predicate (↑ F) (empty)
                    ≡⟨⟩ -- Definition of '↑'
                       true 
                    ∎
                sublemma (suc n') refl = 
                    let (c' , c'-prop) = ⋖-to-addChoice (H n') in
                    begin 
                        predicate (↑ F) (h n)
                    ≡⟨⟩
                        predicate (↑ F) (h (suc n'))
                    ≡⟨ cong (predicate (↑ F)) (c'-prop)  ⟩
                        predicate (↑ F) (addChoice (h n') c')
                    ≡⟨ sym $ recoToFilter-addChoice (↑ F) (h n') c' ⟩
                        (↓ ↑ F) (h n') c'
                    ≡⟨ cong ((↓ ↑ F) (h n')) (lemma-getChoice-exence n' h H ) ⟩
                        (↓ ↑ F) (h n') (getChoice (h n') (h (suc n')) (H n'))
                    ≡⟨ LEFT sat n' ⟩
                       true 
                    ∎
        --LEFT sat n = 
        --    begin 
        --        (↓ ↑ F) (h n) (getChoice (h n) (h (suc n)) (H n))
        --    ≡⟨ cong ((↓ ↑ F) (h n)) (sym $ lemma-getChoice-exence n h H) ⟩
        --        (↓ ↑ F) (h n) c
        --    ≡⟨ recoToFilter-addChoice (↑ F) (h n) c ⟩
        --        predicate (↑ F) (addChoice (h n) c)
        --    --≡⟨ cong (predicate (↑ F)) (c-prop) ⟩
        --    --    predicate (↑ F) (h (suc n)) -- Rewrite to `addChoice (h n) c`
        --    ≡⟨ filterToReco-addChoice F (h n) c ⟩ -- addChoice lemma for filterToReco
        --        F (h n) c ∧ predicate (↑ F) (h n)
        --    ≡⟨ cong (_∧ (predicate $ ↑ F) (h n)) {! subst (λ c → F (h n) c ≡ true) (sat n) !}  ⟩
        --        true ∧ (predicate $ ↑ F) (h n)
        --    ≡⟨⟩
        --        predicate (↑ F) (h n)
        --    ≡⟨ sublemma n refl ⟩
        --        true
        --    ∎
        --    where
        --        c : Choices (h n)
        --        c = proj₁ $ ⋖-to-addChoice (H n)
        --        c-prop : addChoice (h n) c ≡ h (suc n)
        --        c-prop = sym $ proj₂ $ ⋖-to-addChoice (H n)
        --        sublemma : (m : ℕ) → (n ≡ m) → predicate (↑ F) (h n) ≡ true
        --        sublemma zero refl = 
        --            begin 
        --                predicate (↑ F) (h n)
        --            ≡⟨⟩
        --                predicate (↑ F) (h 0)
        --            ≡⟨ cong (predicate (↑ F)) (empty-is-unique-zero (h 0))  ⟩
        --                predicate (↑ F) (empty)
        --            ≡⟨⟩ -- Definition of '↑'
        --               true 
        --            ∎
        --        sublemma (suc n') refl = 
        --            let (c' , c'-prop) = ⋖-to-addChoice (H n') in
        --            begin 
        --                predicate (↑ F) (h n)
        --            ≡⟨⟩
        --                predicate (↑ F) (h (suc n'))
        --            ≡⟨ cong (predicate (↑ F)) (c'-prop)  ⟩
        --                predicate (↑ F) (addChoice (h n') c')
        --            ≡⟨ sym $ recoToFilter-addChoice (↑ F) (h n') c' ⟩
        --                (↓ ↑ F) (h n') c'
        --            ≡⟨ cong ((↓ ↑ F) (h n')) (lemma-getChoice-exence n' h H ) ⟩
        --                (↓ ↑ F) (h n') (getChoice (h n') (h (suc n')) (H n'))
        --            ≡⟨ LEFT sat n' ⟩
        --               true 
        --            ∎
                    
            

        RIGHT : Exence-sats (↓ ↑ F) E → Exence-sats F E
        RIGHT sat = ?
        

theo-filter-reco-filter-same-sat-NFFun
    : (F : Filter)
    → (f' : NFFun)
    → NFFun-sats F f' ↔ NFFun-sats (↓ ↑ F) f'
theo-filter-reco-filter-same-sat-NFFun F f' = ?
    
theo-reco-filter-reco-same-sat
    : (P : Reco)
    → (E : Exence) 
    → Reco-Exence-sats P E ↔ Reco-Exence-sats (↑ ↓ P) E
theo-reco-filter-reco-same-sat P (h , H) = ?

theo-reco-filter-reco-same-sat-NFFun
    : (P : Reco)
    → (f' : NFFun)
    → Reco-NFFun-sats P f' ↔ Reco-NFFun-sats (↑ ↓ P) f'
theo-reco-filter-reco-same-sat-NFFun P f' = ?

--------------------------------------------------------------------------------
-- Auxiliary concepts used by proof of theo-filter-reco-correspondence
--------------------------------------------------------------------------------

-- G is stronger than F if G disallows any choice that F disallows.
-- G might disallow also choices that F allows.
stronger : Filter → Filter → Set
stronger F G = 
    {n : ℕ} 
    → (r : NFRestr n) 
    → (c : Choices r) 
    → F r c ≡ false 
    → G r c ≡ false

lemma-↓↑-stronger : (F : Filter) → stronger (↓ ↑ F) F
lemma-↓↑-stronger = ?

