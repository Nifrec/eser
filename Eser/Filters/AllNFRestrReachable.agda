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
    ; n<1+n
    ; <-trans
    )
--open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n ; 1+n≰n
--    ; ≤-irrelevant
--    ; <-irrelevant
--    ; m<1+n⇒m<n∨m≡n
--    ; <-≤-trans
--    ; ≤-<-trans
--    ; m≢1+n+m
--    ; <-trans
--    ; <⇒≤ 
--    ; m<n⇒m≤1+n 
--    ; ≤⇒≯ 
--    ; m≤n⇒m<n∨m≡n
--    ; n≮n
--    )
--module ≤R = Data.Nat.Properties.≤-Reasoning

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using 
    ( tri-≡
    ; tri-<
    ; tri->
    ; doubleSubst
    ; Sn∸n≡1
    ; depSubst
    ; uip
    ; 1+n≮n
    ; m<n<1+m→⊥
    )
open import Eser.Stdlib using (∸-suc)
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
        h-m>n-lemma
            : {n m x y : ℕ}
            --→ (p : n < m)
            → (r : NFRestr n)
            → (u : (m ∸ n) ≡ x)
            → (v : (m ∸ n) + n ≡ y)
            → (w : x + n ≡ y)
            → subst NFRestr v (extendWithNewNFs r (m ∸ n))
                ≡ subst NFRestr w (extendWithNewNFs r x)
        h-m>n-lemma r refl refl refl = refl


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

        H-cases-m<n
            : (m : ℕ)
            → (p : m < n)
            → (x₀ : m ≢ n)
            → (x₁ : m ≯ n)
            → (p₁ : <-cmp m n ≡ tri< p x₀ x₁)
            → (q : Tri (suc m < n) (suc m ≡ n) (suc m > n))
            → (q₁ : <-cmp (suc m) n ≡ q)
            → h m ⋖ h (suc m)
        H-cases-m<n m p x₀ x₁ p₁ (tri< 1+m<n y₀ y₁)  q₁ = ans
            where
                eq-m : h m ≡ trim r p
                eq-m = 
                    begin 
                        h m
                    ≡⟨⟩
                        h-cases m (<-cmp m n)
                    ≡⟨ cong (h-cases m) p₁ ⟩
                        h-cases m (tri< p x₀ x₁)
                    ≡⟨⟩
                        trim r p
                    ∎
                eq-1+m : h (suc m) ≡ trim r 1+m<n
                eq-1+m =
                    begin 
                        h (suc m)
                    ≡⟨⟩
                        h-cases (suc m) (<-cmp (suc m) n)
                    ≡⟨ cong (h-cases (suc m)) q₁ ⟩
                        h-cases (suc m) (tri< 1+m<n y₀ y₁)
                    ≡⟨⟩
                        trim r 1+m<n
                    ∎
                trimmed-⋖ : trim r p ⋖ trim r 1+m<n
                trimmed-⋖ = lemma-trim-⋖ r p 1+m<n

                ans : h m ⋖ h (suc m)
                ans = doubleSubst _⋖_ (sym eq-m) (sym eq-1+m) trimmed-⋖

        H-cases-m<n m p x₀ x₁ p₁ (tri≈ y₀ 1+m≡n y₁) q₁ = ? 
        H-cases-m<n m p x₀ x₁ p₁ (tri> y₀ y₁ 1+m>n) q₁ =
            ⊥-elim $ m<n<1+m→⊥ p 1+m>n

        {-# WARNING_ON_USAGE H-cases-m<n "Don't fortget to prove lemma-trim-⋖" #-}
        
        H-cases m (tri< m<n x₀ x₁) p₁ = 
            H-cases-m<n m m<n x₀ x₁ p₁ (<-cmp (suc m) n) refl
        H-cases n (tri≈ x₀ refl x₁) p₁ = ?
            where
                LHS : h n ≡ r
                LHS = 
                    let (x₀ , x₁ , prf) = tri-≡ n n refl
                    in
                    begin 
                        h n
                    ≡⟨⟩
                        h-cases n (<-cmp n n)
                    ≡⟨ cong (h-cases n) prf ⟩
                        h-cases n (tri≈ x₀ refl x₁)
                    ≡⟨⟩
                        r
                    ∎

                RHS : h (suc n) ≡ newNF r
                RHS = 
                    let (x₀ , x₁ , prf) = tri-> (suc n) n q in
                    begin 
                        h (suc n)
                    ≡⟨⟩
                        h-cases (suc n) (<-cmp (suc n) n)
                    ≡⟨ cong (h-cases (suc n) ) prf ⟩
                        h-cases (suc n) (tri> x₀ x₁ q)
                    ≡⟨⟩
                        subst NFRestr (x+n≡1+n) 
                              (extendWithNewNFs r ((suc n) ∸ n))
                    ≡⟨ h-m>n-lemma {n} {suc n} {1} {suc n} 
                                   r (Sn∸n≡1 n) x+n≡1+n refl ⟩
                        subst NFRestr refl (extendWithNewNFs r 1)
                    ≡⟨⟩
                        extendWithNewNFs r 1
                    ≡⟨⟩
                        newNF (extendWithNewNFs r 0)
                    ≡⟨⟩
                        newNF r
                    ∎
                    where
                        q : n < suc n
                        q = n<1+n n
                       
                        x : ℕ
                        x = suc n ∸ n
                        x+n≡1+n : x + n ≡ suc n
                        x+n≡1+n = 
                            begin 
                                x + n
                            ≡⟨⟩
                                (suc n ∸ n) + n
                            ≡⟨ +-comm (suc n ∸ n) n ⟩
                                n + (suc n ∸ n)
                            -- Note: in `m+[n∸m]≡n` the names m & n are swapped.
                            ≡⟨ m+[n∸m]≡n (<⇒≤ q) ⟩
                                suc n
                            ∎
        H-cases m (tri> x₀ x₁ m>n) p₁ = K₂
            where
                E = extendWithNewNFs
                a : ℕ
                a = m ∸ n + n
                b : ℕ
                b = m
                v : a ≡ b
                v = 
                    begin 
                        (m ∸ n) + n
                    ≡⟨ +-comm (m ∸ n) n ⟩
                        n + (m ∸ n)
                    ≡⟨ m+[n∸m]≡n (<⇒≤ m>n) ⟩
                        m
                    ∎
                w : suc a ≡ suc b
                w = cong suc v

                1+m>n : suc m > n
                1+m>n = <-trans m>n (n<1+n m) 
                
                u : (suc m ∸ n) + n ≡ suc m
                u = 
                    begin 
                        ((suc m) ∸ n) + n
                    ≡⟨ +-comm ((suc m) ∸ n) n ⟩
                        n + ((suc m) ∸ n)
                    ≡⟨ m+[n∸m]≡n (<⇒≤ 1+m>n) ⟩
                        suc m
                    ∎

                LHS : h m ≡ subst NFRestr v (E r (m ∸ n))
                LHS = 
                    let (x₀ , x₁ , prf) = tri-> m n m>n in
                    begin 
                        h m
                    ≡⟨⟩
                        h-cases m (<-cmp m n)
                    ≡⟨ cong (h-cases m) prf ⟩
                        h-cases m (tri> x₀ x₁ m>n)
                    ≡⟨⟩
                        subst NFRestr v (E r (m ∸ n))
                    ∎
                    

                RHS : h (suc m) ≡ subst NFRestr w (E r (suc (m ∸ n)))
                RHS =
                    let (x₀ , x₁ , prf) = tri-> (suc m) n 1+m>n in
                    let F = λ (i , j) → subst NFRestr j (E r i) in
                    begin 
                        h (suc m)
                    ≡⟨⟩
                        h-cases (suc m) (<-cmp (suc m) n)
                    ≡⟨ cong (h-cases (suc m)) prf ⟩
                        h-cases (suc m) (tri> x₀ x₁ 1+m>n)
                    ≡⟨⟩
                        subst NFRestr u (E r ((suc m) ∸ n))
                    ≡⟨⟩
                        F (suc m ∸ n , u)
                    ≡⟨ cong F $ depSubst ((suc m) ∸ n) (suc (m ∸ n)) (∸-suc 1+m>n) u ⟩
                        F (suc (m ∸ n) , subst (λ z → z + n ≡ suc m) (∸-suc 1+m>n) u)
                    ≡⟨ cong (λ u → F (suc (m ∸ n) , u)) 
                       (uip (subst (λ z → z + n ≡ suc m) (∸-suc 1+m>n) u) w)
                     ⟩
                        F (suc (m ∸ n) , w)
                    ≡⟨⟩
                        subst NFRestr w (E r (suc (m ∸ n)))
                    ∎

                K₀ : E r (m ∸ n) ⋖ E r (suc (m ∸ n))
                K₀ = ⋖-newNF (E r (m ∸ n))
                K₁ : subst NFRestr v (E r (m ∸ n)) 
                     ⋖ 
                     subst NFRestr w (E r (suc (m ∸ n)))
                K₁ = lemma-⋖-subst v w K₀
                K₂ : h m ⋖ h (suc m)
                K₂ = doubleSubst _⋖_ (sym LHS) (sym RHS) K₁



theo-all-NFRestr-reachable {n} r = ?
