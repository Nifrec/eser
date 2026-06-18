-- Module      : Eser.Filters.Resurface
-- Description : Lift a sub-NFRestr of r of the form `newNF r'` to a NFS of r.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
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
