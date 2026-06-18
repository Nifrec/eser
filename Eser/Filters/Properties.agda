-- Module      : Eser.Filters.Properties
-- Description : Properties of basic definitions
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
