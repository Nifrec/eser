-- Module      : Eser.Filters.Resurface
-- Description : Lift a sub-NFRestr of r of the form `newNF r'` to a NFS of r.
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
--open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n)

--open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
--open import Eser.EqRel.Conversions using (RelToFun)
--open import Eser.Aux using (_↔_ ; _≈_ ; restIsProofIrrel)
--open import Eser.Logic

open import Eser.Filters.Base
open import Eser.Filters.Properties 

module Eser.Filters.Resurface where

-- Given that a sub-NFRestr of r of the form `newNF r'`,
-- construct the choice of r that points to this normal form.
resurface-nf
    : {n m : ℕ}
    → (r' : NFRestr n)
    → (r : NFRestr m)
    → (newNF r') ⋖+= r
    → Σ[ c ∈ Choices r ] (choiceToℕ {m} {r} c) ≡ (suc n)

resurface-nf-⋖+-case
    : {n m : ℕ}
    → (r' : NFRestr n)
    → (r : NFRestr m)
    → (newNF r') ⋖+ r
    → Σ[ x ∈ NFS r ] (NFSToℕ {m} {r} x) ≡ (suc n)

resurface-nf {n} {suc n} r' (newNF r') (inj₁ (refl , refl)) = (here , refl)
resurface-nf {n} {suc n} r' (oldNF r c) (inj₁ (refl , ()))
resurface-nf {n} {m} r' r (inj₂ newNFr'⋖+r) = 
    let (c , p) = resurface-nf-⋖+-case {n} {m} r' r newNFr'⋖+r
    in (earlier-new c , p)
    
resurface-nf-⋖+-case {n} {suc (suc n)} r' r (⋖+-onestep (⋖-newNF (newNF r'))) = 
    (earlier-new {suc n} {newNF r'} (here {n} {r'}) , p)
        where
            p : NFSToℕ (earlier-new {suc n} {newNF r'} (here {n} {r'})) ≡ suc n
            p = begin 
                    NFSToℕ (earlier-new {suc n} {newNF r'} (here {n} {r'}))
                ≡⟨⟩
                    NFSToℕ (here {n} {r'})
                ≡⟨ ? ⟩
                    suc n
                ∎
            
resurface-nf-⋖+-case {n} {m} r' r (⋖+-onestep (⋖-oldNF (newNF r') c)) = {! !}
resurface-nf-⋖+-case {n} {m} r' r (⋖+-multistep-newNF H) = {! !}
resurface-nf-⋖+-case {n} {m} r' r (⋖+-multistep-oldNF c H) = {! !}
