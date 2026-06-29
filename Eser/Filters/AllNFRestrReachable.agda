-- Module      : Eser.Filters.allNFRestrReachable
-- Description : Converting a NFFun to extensions-sequence, and inversity proof.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- For every NFRestr there actually a restriction of some normalisation
-- function.
-- This ensures that the datatype `NFRestr` has no garbage instantiations.
-- This fact was important in the design of the _♥_ relation.
--
-- Proof idea: every `r : NFRestr n` can be extended into an Exence (h , H)
-- as follows: 
-- For input m, let h m return:
-- * trim' r m<n if m < n
-- * r if m ≡ n
-- * r extended with x ≔ m ∸ n times `newNF` if m > n
-- Then `combine (h , H)` (using `combine` from Conversions.NFFunToExence)
-- gives the desired NFFun.
--------------------------------------------------------------------------------

open import Data.Nat
--open import Data.Bool hiding (_<_ ; _≤_ ; _≤?_ )
open import Data.Empty
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)

open import Data.Nat.Properties using 
    ( _≤?_ 
    ; m+[n∸m]≡n
    ; <⇒≤
    ; +-comm
    )
--open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n ; 1+n≰n
--    ; ≤-irrelevant
--    ; <-irrelevant
--    ; m<1+n⇒m<n∨m≡n
--    ; <-≤-trans
--    ; ≤-<-trans
--    ; m≢1+n+m
--    ; <-trans
--    ; n<1+n
--    ; <⇒≤ 
--    ; m<n⇒m≤1+n 
--    ; ≤⇒≯ 
--    ; m≤n⇒m<n∨m≡n
--    ; n≮n
--    )
--module ≤R = Data.Nat.Properties.≤-Reasoning

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using ( tri-≡
                           ; tri-<
                           )
--open import Eser.Logic

open import Eser.Filters.Base
open import Eser.Filters.Properties 
open import Eser.Filters.Resurface

open import Eser.Filters.Conversions.NFFunToExence
module Eser.Filters.AllNFRestrReachable where

theo-all-NFRestr-reachable
    : {n : ℕ}
    → (r : NFRestr n)
    → Σ[ f ∈  NFFun ](r ≡ restrict f n)

-- Given a NFRestr n, extend it to a NFRestr (x + n)
-- by stacking the `newNF` constructor x times on top of it.
extendWithNewNFs
    : {n : ℕ}
    → NFRestr n
    → (x : ℕ)
    → NFRestr (x + n)
extendWithNewNFs r zero = r
extendWithNewNFs r (suc x) = newNF (extendWithNewNFs r x)

NFRestrToExence
    : {n : ℕ}
    → (r : NFRestr n)
    → Σ[ h ∈ NFRestrFam ] Σ[ H ∈ ((n : ℕ) → h n ⋖ h (suc n)) ] h n ≡ r
NFRestrToExence {n} r = (h , H , eq)
    where
        --h : (m : ℕ) → NFRestr m
        --h-cases : (m : ℕ) → Dec (m ≤ n) → NFRestr m
        
        --h m = h-cases m (m ≤? n)

        --h-cases m (yes m≤n) = trim' r m≤n
        --h-cases m (no m≰n) = extendWithNewNFs r (m ∸ n)

        h : (m : ℕ) → NFRestr m
        h-cases : (m : ℕ) → Tri (m < n) (m ≡ n) (m > n) → NFRestr m
        
        h m = h-cases m (<-cmp m n)

        h-cases m (tri< m<n x₀ x₁)  = trim r m<n
        h-cases n (tri≈ x₀ refl x₁) = r
        h-cases m (tri> x₀ x₁ m>n)  = subst NFRestr (x+n≡m) (extendWithNewNFs r x)
            where
                x : ℕ
                x = m ∸ n
                x+n≡m : x + n ≡ m
                x+n≡m = 
                    begin 
                        x + n
                    ≡⟨⟩
                        (m ∸ n) + n
                    ≡⟨ +-comm (m ∸ n) n ⟩
                        n + (m ∸ n)
                    -- Note: in `m+[n∸m]≡n` the names m & n are swapped.
                    ≡⟨ m+[n∸m]≡n (<⇒≤ m>n) ⟩
                        m
                    ∎

        eq : h n ≡ r
        eq = let (x₀ , x₁ , p) = (tri-≡ n n refl) in
            begin 
                h n
            ≡⟨⟩
                h-cases n (<-cmp n n)
            ≡⟨ cong (h-cases n) p ⟩ 
                h-cases n (tri≈ x₀ refl x₁)
            ≡⟨⟩
                r
            ∎
            

        H : (m : ℕ) → h m ⋖ h (suc m)

        H-cases
            : (m : ℕ)
            → (p : Tri (m < n) (m ≡ n) (m > n))
            → (p₁ : <-cmp m n ≡ p)
            → h m ⋖ h (suc m)

        H m = H-cases m (<-cmp m n) refl

        H-cases m (tri< m<n x₀ x₁) p₁ = ?
        H-cases m (tri≈ x₀ m≡n x₁) p₁ = ?
        H-cases m (tri> x₀ x₁ m>n) p₁ = ?


theo-all-NFRestr-reachable {n} r = ?
