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
open import Data.Nat.Properties using (m<1+n⇒m<n∨m≡n ; n<1+n ; <-irrefl 
                                      ; m≤n⇒m<n∨m≡n)

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_ ; restIsProofIrrel ; n<1+n-lemma )

open import Eser.Filters.Base

module Eser.Filters.Properties where

--------------------------------------------------------------------------------
-- A NFRestr can be trimmed to a sub-NFRestr.
--------------------------------------------------------------------------------
-- Contents:
-- 1. Definition of trim.
-- 2. correctness proof of trim.
-- 3. Variant of `trim` with m≤n i.o. m<n.
-- 4. getLastChoice.
 
-- Trim a NFRestr n to a NFRestr m by simply forgetting the last few choices,
-- given that m < n.
trim
    : {n : ℕ}
    → (r : NFRestr n)
    → {m : ℕ}
    → m < n
    → NFRestr m

trim-cases
    : {n' : ℕ}
    → (r : NFRestr (suc n'))
    → {m : ℕ}
    → (m < n') ⊎ (m ≡ n')
    → NFRestr m

trim {suc n'} r {m} m<n = 
    trim-cases {n'} r {m} (m<1+n⇒m<n∨m≡n m<n)

trim-cases {n'} (newNF r') {m} (inj₁ m<n') = 
    trim {n'} r' {m} m<n'
trim-cases {n'} (oldNF r' c) {m} (inj₁ m<n') =
    trim {n'} r' {m} m<n'
trim-cases {n'} (newNF r') {n'} (inj₂ refl) = r'
trim-cases {n'} (oldNF r' c) {n'} (inj₂ refl) = r'

-- Correctness: the trimmed version is actually a sub-NFRestr of the input.
-- That it has the right length already holds at type level.
trim-correctness
    : {n : ℕ}
    → (r : NFRestr n)
    → {m : ℕ}
    → (m<n : m < n)
    → (trim r m<n) ⋖+ r
trim-correctness {suc n'} r {m} m<n = 
    cases {n'} r {m} m<n (m<1+n⇒m<n∨m≡n m<n) refl
    module TrimNFRestrCorrectness where
        cases
            : {n' : ℕ}
            → (r : NFRestr (suc n'))
            → {m : ℕ}
            → (p : m < suc n')
            → (p₀ : (m < n') ⊎ (m ≡ n'))
            → (p₁ : m<1+n⇒m<n∨m≡n p ≡ p₀)
            → (trim r p) ⋖+ r
        cases {n'} (newNF r') {m} m<n (inj₁ m<n') p₁ = 
            subst (_⋖+ newNF r') (sym H) (⋖+-multistep-newNF IH)
            where
                IH : trim r' m<n' ⋖+ r'
                IH = trim-correctness r' m<n'
                H : trim (newNF r') m<n ≡ trim r' m<n'
                H =
                    begin 
                        trim {suc n'} (newNF r') m<n   
                    ≡⟨⟩
                        trim-cases (newNF r') (m<1+n⇒m<n∨m≡n m<n)
                    ≡⟨ cong (λ x → trim-cases (newNF r') x) p₁ ⟩
                        trim-cases (newNF r') (inj₁ m<n')
                    ≡⟨⟩
                        trim r' m<n'
                    ∎
        cases {n'} (oldNF r' c) {m} m<n (inj₁ m<n') p₁ =
            subst (_⋖+ oldNF r' c) (sym H) (⋖+-multistep-oldNF c IH)
            where
                IH : trim r' m<n' ⋖+ r'
                IH = trim-correctness r' m<n'
                H : trim (oldNF r' c) m<n ≡ trim r' m<n'
                H =
                    begin 
                        trim {suc n'} (oldNF r' c) m<n   
                    ≡⟨⟩
                        trim-cases (oldNF r' c) (m<1+n⇒m<n∨m≡n m<n)
                    ≡⟨ cong (λ x → trim-cases (oldNF r' c) x) p₁ ⟩
                        trim-cases (oldNF r' c) (inj₁ m<n')
                    ≡⟨⟩
                        trim r' m<n'
                    ∎
        -- Next two cases use the same proof,
        -- except for changing `newNF r'` by `oldNF r c`.
        cases {n'} (newNF r') {n'} m<n (inj₂ refl) p₁ = 
            subst ( _⋖+ newNF r') (sym H) (⋖+-onestep (⋖-newNF r'))
            where
                H : trim (newNF r') m<n ≡ r'
                H =
                    begin 
                        trim {suc n'} (newNF r') {n'} m<n   
                    ≡⟨⟩
                        trim-cases {n'} (newNF r') {n'} 
                                           (m<1+n⇒m<n∨m≡n m<n)
                    ≡⟨ cong (λ x → trim-cases {n'} (newNF r') x) 
                             p₁ ⟩
                        trim-cases {n'} (newNF r') {n'} (inj₂ refl)
                    ≡⟨⟩
                        r'
                    ∎
        cases {n'} (oldNF r' c) {n'} m<n (inj₂ refl) p₁ =
            subst ( _⋖+ oldNF r' c) (sym H) (⋖+-onestep (⋖-oldNF r' c))
            where
                H : trim (oldNF r' c) m<n ≡ r'
                H =
                    begin 
                        trim {suc n'} (oldNF r' c) {n'} m<n   
                    ≡⟨⟩
                        trim-cases {n'} (oldNF r' c) {n'} 
                                           (m<1+n⇒m<n∨m≡n m<n)
                    ≡⟨ cong (λ x → trim-cases {n'} (oldNF r' c) x) 
                             p₁ ⟩
                        trim-cases {n'} (oldNF r' c) {n'} (inj₂ refl)
                    ≡⟨⟩
                        r'
                    ∎

-- Variant of `trim` that also allows the option to trimming to m ≡ n,
-- in which case it just acts as the identity.
trim' 
    : {n : ℕ}
    → (r : NFRestr n)
    → {m : ℕ}
    → m ≤ n
    → NFRestr m
trim'-cases 
    : {n : ℕ}
    → (r : NFRestr n)
    → {m : ℕ}
    → m < n ⊎ m ≡ n
    → NFRestr m

trim' r m≤n = trim'-cases r (m≤n⇒m<n∨m≡n m≤n)
trim'-cases r (inj₁ m<n) = trim r m<n
trim'-cases {n} r {n} (inj₂ refl) = r

getLastChoice
    : {n' : ℕ}
    → (r : NFRestr (suc n'))
    → Σ[ c ∈ Choices (trim r (n<1+n n')) ] r ≡ addChoice (trim r (n<1+n n')) c
getLastChoice {n'} (newNF r') = ans
    where
        H : trim {suc n'} (newNF r') {n'} (n<1+n n') ≡ r'
        H =
            begin 
                trim (newNF r') (n<1+n n')
            ≡⟨⟩
                trim-cases (newNF r') (m<1+n⇒m<n∨m≡n (n<1+n n'))
            ≡⟨ cong (trim-cases {n'} (newNF r') {n'}) (n<1+n-lemma n') ⟩
                trim-cases (newNF r') (inj₂ refl)
            ≡⟨⟩
                r'
            ∎

        K : newNF r' ≡ addChoice r' here
        K = refl

        pre-ans : Σ[ c ∈ Choices r' ] newNF r' ≡ addChoice r' c
        pre-ans = (here , K)

        P : NFRestr n' → Set
        P x = Σ[ c ∈ Choices x ] newNF r' ≡ addChoice x c
        
        ans : P (trim (newNF r') (n<1+n n'))
        ans = subst P (sym H) pre-ans 

-- Same proof as other case, except all `newNF r'` are replaced by `oldNF r' c`.
getLastChoice {n'} (oldNF r' c) = ans
    where
        H : trim {suc n'} (oldNF r' c) {n'} (n<1+n n') ≡ r'
        H =
            begin 
                trim (oldNF r' c) (n<1+n n')
            ≡⟨⟩
                trim-cases (oldNF r' c) (m<1+n⇒m<n∨m≡n (n<1+n n'))
            ≡⟨ cong (trim-cases {n'} (oldNF r' c) {n'}) (n<1+n-lemma n') ⟩
                trim-cases (oldNF r' c) (inj₂ refl)
            ≡⟨⟩
                r'
            ∎

        K : oldNF r' c ≡ addChoice r' (earlier-new c)
        K = refl

        pre-ans : Σ[ k ∈ Choices r' ] oldNF r' c ≡ addChoice r' k
        pre-ans = (earlier-new c , K)

        P : NFRestr n' → Set
        P x = Σ[ k ∈ Choices x ] oldNF r' c ≡ addChoice x k
        
        ans : P (trim (oldNF r' c) (n<1+n n'))
        ans = subst P (sym H) pre-ans 

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
