-- Module      : Eser.Filters.Resurface
-- Description : Dig up an earlier used normal-form-choice and reuse it.
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

open import Eser.Filters.Base
open import Eser.Filters.Properties 

module Eser.Filters.Resurface where

-- Dig up an earlier assigned normal form and reuse it as the normal form
-- of n.
-- Idea: if m is assigned normal form m* in r, then m* ≤ m and m* is a NF of r.
-- So we can also assign n the normal form of m*, and extend r with it.
-- This does not require any prior knowledge of sub-NFRestrs of r
-- (unlike the other 'resurface' varieties in this file).
resurface 
    : {n : ℕ}
    → (r : NFRestr n)
    → {m : ℕ}
    → m < n
    → Choices r
resurface {suc n'} r {m} m<n = resurface-cases {n'} r {m} (m<1+n⇒m<n∨m≡n m<n)
    module ResurfaceImpl where
        open import Data.Nat.Properties using (m<1+n⇒m<n∨m≡n)
        resurface-cases
            : {n' : ℕ}
            → (r : NFRestr (suc n'))
            → {m : ℕ}
            → (m < n') ⊎ (m ≡ n')
            → Choices r
        resurface-cases {n'} r {m} (inj₁ m<n') = ?
        resurface-cases {n'} r {n'} (inj₂ refl) = ?
        
-- Given that a sub-NFRestr of r of the form `newNF r'`,
-- construct the choice of r that points to this normal form.
resurface-nf
    : {n m : ℕ}
    → (r' : NFRestr n)
    → (r : NFRestr m)
    → (newNF r') ⋖+= r
    → Σ[ c ∈ Choices r ] (choiceToℕ {m} {r} c) ≡ n

resurface-nf-⋖+-case
    : {n m : ℕ}
    → (r' : NFRestr n)
    → (r : NFRestr m)
    → (newNF r') ⋖+ r
    → Σ[ x ∈ NFS r ] (NFSToℕ {m} {r} x) ≡ n

resurface-nf {n} {suc n} r' (newNF r') (inj₁ (refl , refl)) 
    = (earlier-new here , refl)
    --^ Note that this works because Choices (newNF r') ≗ NFS (newNF (newNF r'))
    -- so `earlier-new here` points to the deepest newNF.
resurface-nf {n} {suc n} r' (oldNF r c) (inj₁ (refl , ()))
resurface-nf {n} {m} r' r (inj₂ newNFr'⋖+r) = 
    let (c , p) = resurface-nf-⋖+-case {n} {m} r' r newNFr'⋖+r
    in (earlier-new c , p)
    
resurface-nf-⋖+-case {n} {suc (suc n)} r' r (⋖+-onestep (⋖-newNF (newNF r'))) = 
    (earlier-new {suc n} {newNF r'} (here {n} {r'}) , p)
        where
            -- p is just `refl`, but this documents why:
            p : NFSToℕ (earlier-new {suc n} {newNF r'} (here {n} {r'})) ≡ n
            p = begin 
                    NFSToℕ (earlier-new {suc n} {newNF r'} (here {n} {r'}))
                ≡⟨⟩
                    NFSToℕ (here {n} {r'})
                ≡⟨⟩
                    n
                ∎
resurface-nf-⋖+-case {n} {m} r' r (⋖+-onestep (⋖-oldNF (newNF r') c)) = 
    (earlier-old {suc n} {newNF r'} {c} here , refl)
    -- ^ See previous case why refl works here.

resurface-nf-⋖+-case {n} {suc m} r' (newNF s) 
    (⋖+-multistep-newNF {suc n} {m} {newNF r'} {s} nr'⋖+s) = (x' , p)
        where
            rec : Σ[ x ∈ NFS s ] (NFSToℕ x) ≡ n
            rec = resurface-nf-⋖+-case {n} {m} r' s nr'⋖+s
            x' : NFS (newNF s)
            x' = earlier-new (proj₁ rec)
            p : NFSToℕ x' ≡ n
            p = proj₂ rec
-- Analogous to previous case:
resurface-nf-⋖+-case {n} {suc m} r' (oldNF s c) 
    (⋖+-multistep-oldNF {suc n} {m} {newNF r'} {s} c nr'⋖+s) = (x' , p)
        where
            rec : Σ[ x ∈ NFS s ] (NFSToℕ x) ≡ n
            rec = resurface-nf-⋖+-case {n} {m} r' s nr'⋖+s
            x' : NFS (oldNF s c)
            x' = earlier-old {c = c} (proj₁ rec)
            p : NFSToℕ x' ≡ n
            p = proj₂ rec
