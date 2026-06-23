-- Module      : Eser.Filters.Properties
-- Description : Properties of and functions on definitions in Filter.Base.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}

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
open import Eser.Aux using (_↔_ ; _≈_ ; restIsProofIrrel)

open import Eser.Filters.Base

module Eser.Filters.Properties where

--------------------------------------------------------------------------------
-- A NFRestr can be trimmed to a sub-NFRestr.
--------------------------------------------------------------------------------
-- See also below for correctness proof.
 
-- Trim a NFRestr n to a NFRestr m by simply forgetting the last few choices,
-- given that m < n.
trim-NFRestr
    : {n : ℕ}
    → (r : NFRestr n)
    → {m : ℕ}
    → m < n
    → NFRestr m

trim-NFRestr-cases
    : {n' : ℕ}
    → (r : NFRestr (suc n'))
    → {m : ℕ}
    → (m < n') ⊎ (m ≡ n')
    → NFRestr m

trim-NFRestr {suc n'} r {m} m<n = 
    trim-NFRestr-cases {n'} r {m} (m<1+n⇒m<n∨m≡n m<n)

trim-NFRestr-cases {n'} (newNF r') {m} (inj₁ m<n') = 
    trim-NFRestr {n'} r' {m} m<n'
trim-NFRestr-cases {n'} (oldNF r' c) {m} (inj₁ m<n') =
    trim-NFRestr {n'} r' {m} m<n'
trim-NFRestr-cases {n'} (newNF r') {n'} (inj₂ refl) = r'
trim-NFRestr-cases {n'} (oldNF r' c) {n'} (inj₂ refl) = r'

-- Correctness: the trimmed version is actually a sub-NFRestr of the input.
-- That it has the right length already holds at type level.
trim-NFRestr-correctness
    : {n : ℕ}
    → (r : NFRestr n)
    → {m : ℕ}
    → (m<n : m < n)
    → (trim-NFRestr r m<n) ⋖+ r
trim-NFRestr-correctness {suc n'} r {m} m<n = 
    cases {n'} r {m} m<n (m<1+n⇒m<n∨m≡n m<n) refl
    module TrimNFRestrCorrectness where
        cases
            : {n' : ℕ}
            → (r : NFRestr (suc n'))
            → {m : ℕ}
            → (p : m < suc n')
            → (p₀ : (m < n') ⊎ (m ≡ n'))
            → (p₁ : m<1+n⇒m<n∨m≡n p ≡ p₀)
            → (trim-NFRestr r p) ⋖+ r
        cases {n'} (newNF r') {m} m<n (inj₁ m<n') p₁ = 
            subst (_⋖+ newNF r') (sym H) (⋖+-multistep-newNF IH)
            where
                IH : trim-NFRestr r' m<n' ⋖+ r'
                IH = trim-NFRestr-correctness r' m<n'
                H : trim-NFRestr (newNF r') m<n ≡ trim-NFRestr r' m<n'
                H =
                    begin 
                        trim-NFRestr {suc n'} (newNF r') m<n   
                    ≡⟨⟩
                        trim-NFRestr-cases (newNF r') (m<1+n⇒m<n∨m≡n m<n)
                    ≡⟨ cong (λ x → trim-NFRestr-cases (newNF r') x) p₁ ⟩
                        trim-NFRestr-cases (newNF r') (inj₁ m<n')
                    ≡⟨⟩
                        trim-NFRestr r' m<n'
                    ∎
        cases {n'} (oldNF r' c) {m} m<n (inj₁ m<n') p₁ =
            subst (_⋖+ oldNF r' c) (sym H) (⋖+-multistep-oldNF c IH)
            where
                IH : trim-NFRestr r' m<n' ⋖+ r'
                IH = trim-NFRestr-correctness r' m<n'
                H : trim-NFRestr (oldNF r' c) m<n ≡ trim-NFRestr r' m<n'
                H =
                    begin 
                        trim-NFRestr {suc n'} (oldNF r' c) m<n   
                    ≡⟨⟩
                        trim-NFRestr-cases (oldNF r' c) (m<1+n⇒m<n∨m≡n m<n)
                    ≡⟨ cong (λ x → trim-NFRestr-cases (oldNF r' c) x) p₁ ⟩
                        trim-NFRestr-cases (oldNF r' c) (inj₁ m<n')
                    ≡⟨⟩
                        trim-NFRestr r' m<n'
                    ∎
        -- Next two cases use the same proof,
        -- except for changing `newNF r'` by `oldNF r c`.
        cases {n'} (newNF r') {n'} m<n (inj₂ refl) p₁ = 
            subst ( _⋖+ newNF r') (sym H) (⋖+-onestep (⋖-newNF r'))
            where
                H : trim-NFRestr (newNF r') m<n ≡ r'
                H =
                    begin 
                        trim-NFRestr {suc n'} (newNF r') {n'} m<n   
                    ≡⟨⟩
                        trim-NFRestr-cases {n'} (newNF r') {n'} 
                                           (m<1+n⇒m<n∨m≡n m<n)
                    ≡⟨ cong (λ x → trim-NFRestr-cases {n'} (newNF r') x) 
                             p₁ ⟩
                        trim-NFRestr-cases {n'} (newNF r') {n'} (inj₂ refl)
                    ≡⟨⟩
                        r'
                    ∎
        cases {n'} (oldNF r' c) {n'} m<n (inj₂ refl) p₁ =
            subst ( _⋖+ oldNF r' c) (sym H) (⋖+-onestep (⋖-oldNF r' c))
            where
                H : trim-NFRestr (oldNF r' c) m<n ≡ r'
                H =
                    begin 
                        trim-NFRestr {suc n'} (oldNF r' c) {n'} m<n   
                    ≡⟨⟩
                        trim-NFRestr-cases {n'} (oldNF r' c) {n'} 
                                           (m<1+n⇒m<n∨m≡n m<n)
                    ≡⟨ cong (λ x → trim-NFRestr-cases {n'} (oldNF r' c) x) 
                             p₁ ⟩
                        trim-NFRestr-cases {n'} (oldNF r' c) {n'} (inj₂ refl)
                    ≡⟨⟩
                        r'
                    ∎


--------------------------------------------------------------------------------
-- Properties of the _⋖_ relation.
--------------------------------------------------------------------------------

⋖-cases 
    : {n : ℕ} 
    → {r : NFRestr n} 
    → {s : NFRestr (ℕ.suc n)}
    → r ⋖ s
    → (s ≡ newNF r) ⊎ Σ[ c ∈ NFS r ](s ≡ oldNF r c)
⋖-cases {n} {r} {s} (⋖-newNF r) = inj₁ refl
⋖-cases {n} {r} {s} (⋖-oldNF r c) = inj₂ (c , refl)

⋖-irrel 
    : {n : ℕ} 
    → (r : NFRestr n) 
    → (s : NFRestr (ℕ.suc n))
    → Relation.Nullary.Irrelevant (r ⋖ s )
⋖-irrel {n} r (newNF s) (⋖-newNF r) (⋖-newNF r) = refl
⋖-irrel {n} r (oldNF r c) (⋖-oldNF r x) (⋖-oldNF r c) = refl

⋖-left-unique
    : {n : ℕ} 
    → {r r' : NFRestr n} 
    → {s : NFRestr (ℕ.suc n)}
    → r ⋖ s
    → r' ⋖ s
    → r ≡ r'
⋖-left-unique {n} {r} {r'} {s} (⋖-newNF r) (⋖-newNF r) = refl
⋖-left-unique {n} {r} {r'} {s} (⋖-oldNF r c) (⋖-oldNF r c) = refl

⋖-left-corollary-newNF
    : {n : ℕ} 
    → {r r' : NFRestr n} 
    → {s s' : NFRestr (ℕ.suc n)}
    → r ⋖ s
    → s ≡ s'
    → s' ≡ newNF r'
    → r ≡ r'
⋖-left-corollary-newNF {n} {r} {r'} {s} {s'} r⋖s refl refl = 
    ⋖-left-unique r⋖s (⋖-newNF r')
    
⋖-left-corollary-oldNF
    : {n : ℕ} 
    → {r r' : NFRestr n} 
    → {s s' : NFRestr (ℕ.suc n)}
    → r ⋖ s
    → s ≡ s'
    → (c : NFS r')
    → s' ≡ oldNF r' c
    → r ≡ r'
⋖-left-corollary-oldNF {n} {r} {r'} {s} {s'} r⋖s refl c refl = 
    ⋖-left-unique r⋖s (⋖-oldNF r' c)

--------------------------------------------------------------------------------
-- Properties of getChoice
--------------------------------------------------------------------------------


lemma-getChoice-subst
    : {n : ℕ}
    → (r r' : NFRestr n)
    → (s s' : NFRestr (ℕ.suc n))
    → (p : r ⋖ s)
    → (p' : r' ⋖ s')
    → r ≡ r'
    → s ≡ s'
    → choiceToℕ (getChoice r s p) ≡ choiceToℕ (getChoice r' s' p')
lemma-getChoice-subst r r s s p p' refl refl = 
    cong (λ p → choiceToℕ (getChoice r s p)) (⋖-irrel r s p p')
