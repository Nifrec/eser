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
open import Data.Nat.Properties using (n<1+n)

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_)

open import Eser.Logic using (∧-elim-right ; true≢false ; ∧-left-implies-right)

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

--------------------------------------------------------------------------------
-- StrongerThan-relation on filters
--------------------------------------------------------------------------------
-- Auxiliary concepts used by correspondence theorems.
-- G is stronger than F if G disallows any choice that F disallows.
-- G might disallow also choices that F allows.
_StrongerThan_ : Filter → Filter → Set
_StrongerThan_ G F = 
    {n : ℕ} 
    → (r : NFRestr n) 
    → (c : Choices r) 
    → F r c ≡ false 
    → G r c ≡ false

-- If G is stronger than F, but G does Allow c In r,
-- then F does Allow c In r as well.
-- In other words, G => F.
stronger-to-implication
    : {F G : Filter}
    → {n : ℕ}
    → (r : NFRestr n)
    → (c : Choices r)
    → G StrongerThan F
    → G Allows c In r
    → F Allows c In r
stronger-to-implication {F} {G} {n} r c G>F G-allows 
    = stronger-to-implication-cases (F r c) refl
    where
        stronger-to-implication-cases 
            : (b : Bool) 
            → (F r c ≡ b) 
            → F Allows c In r
        stronger-to-implication-cases false p = ⊥-elim $ true≢false true≡false
            where
                G-disallows : G r c ≡ false
                G-disallows = G>F r c p
                true≡false : true ≡ false
                true≡false = trans (sym G-allows) G-disallows
        stronger-to-implication-cases true p = p
        

lemma-↓↑-stronger : (F : Filter) → (↓ ↑ F) StrongerThan F
lemma-↓↑-stronger F {n} r c F-disallows =
    begin 
        (↓ ↑ F) r c
    ≡⟨ recoToFilter-addChoice (↑ F) r c ⟩
        predicate (↑ F) (addChoice r c)
    ≡⟨ filterToReco-addChoice F r c ⟩
        F r c ∧ predicate (↑ F) r
    ≡⟨ cong (_∧ predicate (↑ F) r) F-disallows ⟩
        false ∧ predicate (↑ F) r
    ≡⟨⟩
        false
    ∎

--------------------------------------------------------------------------------
-- Correspondence theorems.
--------------------------------------------------------------------------------

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
                (↓ ↑ F) (h n) c
            ≡⟨ recoToFilter-addChoice (↑ F) (h n) c ⟩
                predicate (↑ F) (addChoice (h n) c)
            ≡⟨ filterToReco-addChoice F (h n) c ⟩
                F (h n) c ∧ predicate (↑ F) (h n)
            ≡⟨ cong (_∧ (predicate $ ↑ F) (h n)) (sat n)  ⟩
                true ∧ (predicate $ ↑ F) (h n)
            ≡⟨⟩
                predicate (↑ F) (h n)
            ≡⟨ sublemma n refl ⟩
                true
            ∎
            where
                sublemma : (m : ℕ) → (n ≡ m) → predicate (↑ F) (h n) ≡ true
                sublemma zero refl = 
                    begin 
                        predicate (↑ F) (h n)
                    ≡⟨⟩
                        predicate (↑ F) (h 0)
                    ≡⟨ cong (predicate (↑ F)) (empty-is-unique-zero (h 0)) ⟩
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

        RIGHT : Exence-sats (↓ ↑ F) E → Exence-sats F E
        RIGHT sat n = stronger-to-implication (h n) c ↓↑F>F (sat n)
            where
                c : Choices (h n)
                c = getChoiceFromExence (h , H) n
                ↓↑F>F : (↓ ↑ F) StrongerThan F
                ↓↑F>F = lemma-↓↑-stronger F

theo-filter-reco-filter-same-sat-NFFun
    : (F : Filter)
    → (f' : NFFun)
    → NFFun-sats F f' ↔ NFFun-sats (↓ ↑ F) f'
theo-filter-reco-filter-same-sat-NFFun F f' = ?

-- filterToReco is a retraction of recoToFilter
-- (up to function extensionality and first projections;
-- second projections are pointwise proof-irrelevant anyway).
-- (It is NOT an inverse though, see lemma-↓↑-stronger for a counterargument to
-- that).
lemma-reco-filter-reco-retract
    : (P : Reco)
    → {n : ℕ}
    → (r : NFRestr n)
    → predicate (↑ ↓ P) r ≡ predicate P r
-- Case 1 : all Recos map 'empty' to 'true'.
lemma-reco-filter-reco-retract P {zero} empty = 
    begin 
        predicate (↑ ↓ P) empty
    ≡⟨ empty-is-ok (↑ ↓ P) ⟩
        true
    ≡⟨ sym $ empty-is-ok P ⟩
        predicate P empty
    ∎
lemma-reco-filter-reco-retract P {suc n} r = 
    begin 
        predicate (↑ ↓ P) r
    -- Since r : NFRestr (suc n), there must exist a smaller NFRestr n
    -- of which r is an extension, i.e., r = addChoice r' c.
    ≡⟨ cong (predicate (↑ ↓ P)) c-prop ⟩
        predicate (↑ ↓ P) (addChoice r' c)
    ≡⟨ filterToReco-addChoice (↓ P) r' c ⟩
        (↓ P) r' c ∧ predicate (↑ ↓ P) r'
    ≡⟨ cong (_∧ predicate (↑ ↓ P) r') (recoToFilter-addChoice P r' c) ⟩
        predicate P (addChoice r' c) ∧ predicate (↑ ↓ P) r'
    -- Now make a recursive call on the RHS.
    ≡⟨ cong (predicate P (addChoice r' c) ∧_ )
            $ lemma-reco-filter-reco-retract P {n} r' ⟩
        predicate P (addChoice r' c) ∧ predicate P r'
    -- Because P is coherent, the LHS implies the RHS.
    ≡⟨ ∧-left-implies-right 
        (predicate P (addChoice r' c)) 
        (predicate P r') 
        (coherence P r' (addChoice r' c) (⋖-addChoice c)) ⟩
        predicate P (addChoice r' c)
    ≡⟨ cong (predicate P) (sym $ c-prop) ⟩
        predicate P r
    ∎
    where
        r' : NFRestr n
        r' = trim r (n<1+n n)
        c : Choices r'
        c = proj₁ $ getLastChoice r
        c-prop : r ≡ addChoice r' c
        c-prop = proj₂ $ getLastChoice r

-- This is now an easy corollary of the previous lemma:    
theo-reco-filter-reco-same-sat
    : (P : Reco)
    → (E : Exence) 
    → Reco-Exence-sats P E ↔ Reco-Exence-sats (↑ ↓ P) E
theo-reco-filter-reco-same-sat P E@(h , H) = (LEFT , RIGHT)
    where
        LEFT : Reco-Exence-sats P E → Reco-Exence-sats (↑ ↓ P) E
        LEFT sat n = 
            begin 
                predicate (↑ ↓ P) (h n)
            ≡⟨ lemma-reco-filter-reco-retract P {n} (h n) ⟩
                predicate P (h n)
            ≡⟨ sat n ⟩
                true
            ∎
            
        RIGHT : Reco-Exence-sats (↑ ↓ P) E → Reco-Exence-sats P E
        RIGHT sat n =
            begin 
                predicate P (h n)
            ≡⟨ sym $ lemma-reco-filter-reco-retract P {n} (h n) ⟩
                predicate (↑ ↓ P) (h n)
            ≡⟨ sat n ⟩
                true
            ∎

theo-reco-filter-reco-same-sat-NFFun
    : (P : Reco)
    → (f' : NFFun)
    → Reco-NFFun-sats P f' ↔ Reco-NFFun-sats (↑ ↓ P) f'
theo-reco-filter-reco-same-sat-NFFun P f' = (LEFT , RIGHT)
    where
        LEFT : Reco-NFFun-sats P f' → Reco-NFFun-sats (↑ ↓ P) f'
        LEFT = ?
        RIGHT = ?

