-- Module      : Eser.Filters.Conversions.NFFunToExence
-- Description : Converting a NFFun to extensions-sequence, and inversity proof.
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

open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n)

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_ ; restIsProofIrrel)

open import Eser.Filters.Base
open import Eser.Filters.Properties 

module Eser.Filters.Conversions.NFFunToExence where

-- Restrict a normalisation function into an Exence --
-- a sequence of NFRestrs that extend each other.
restrict+ : NFFun → Exence
restrict+ f = (? , ?)

-- Restrict a normalisation function into a NFRestr
restrict : NFFun → (n : ℕ) → NFRestr n
restrict = proj₁ ∘ restrict+

-- Given r ⋖ s, extract the choice that extends r into s.
getChoice 
    : {n : ℕ}
    → (r : NFRestr n)
    → (s : NFRestr (ℕ.suc n))
    → r ⋖ s
    → Choices r
getChoice r (newNF r) (⋖-newNF r) = here
getChoice r (oldNF r c) (⋖-oldNF r c) = earlier-new c

-- Given a sequence of extensions, extract the choice that
-- extends h n to h (1+n).
getChoiceFromExence : (hH : Exence) → (n : ℕ) → Choices ((proj₁ hH) n)
getChoiceFromExence (h , H) n = getChoice (h n) (h $ ℕ.suc n) (H n)

NFSToℕ 
    : {n : ℕ}
    → {r : NFRestr n}
    → NFS r
    → ℕ
-- Case 1: the input NFRestr chose the normal form of n to be itself.
NFSToℕ {suc n} {newNF r} here = n 
-- Case 2 & 3: the input normal form is a normal form of a sub-restriction
-- of r. So recurse on this sub-restriction.
NFSToℕ {suc n} {newNF r} (earlier-new x) = NFSToℕ {n} {r} x
NFSToℕ {suc n} {oldNF r c} (earlier-old x) = NFSToℕ {n} {r} x

choiceToℕ 
    : {n : ℕ}
    → {r : NFRestr n}
    → Choices r
    → ℕ
-- A choice of r is a NF of newNF r, by definition of `Choices`.
choiceToℕ {n} {r} c = NFSToℕ {ℕ.suc n} {newNF r} c 

NFSToℕ-≤ 
    : {n : ℕ}
    → {r : NFRestr n}
    → (x : NFS r)
    → NFSToℕ x < n
NFSToℕ-≤ {suc n} {newNF r} here = s≤s ≤-refl
NFSToℕ-≤ {suc n} {newNF r} (earlier-new x) = s≤s (≤-trans (n≤1+n (NFSToℕ x)) y)
    where 
        y : NFSToℕ x < n
        y = NFSToℕ-≤ {n} {r} x
NFSToℕ-≤ {suc n} {oldNF r c} (earlier-old x) = s≤s (≤-trans (n≤1+n (NFSToℕ x)) y)
    where 
        y : NFSToℕ x < n
        y = NFSToℕ-≤ {n} {r} x

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

combine : Exence → NFFun
combine (h , H) = (f , f-leq , f-fix)
    where
        
        f : ℕ → ℕ
        f = choiceToℕ ∘ (getChoiceFromExence (h , H))

        f-leq : (n : ℕ) → f n ≤ n
        f-leq n = s≤s⁻¹ $ NFSToℕ-≤ (getChoiceFromExence (h , H) n)

        lemma-1
            : {n : ℕ}
            → (h : NFRestrFam)
            → (H : (n : ℕ) → (h n ⋖ h (ℕ.suc n)))
            → (r : NFRestr n)
            → r ≡ h n
            → (c : NFS r)
            → (m : ℕ)
            → m ≡ choiceToℕ (earlier-new c)
            → choiceToℕ (getChoice (h m) (h (ℕ.suc m)) (H m)) ≡ m
        lemma-1 {suc n} h H (newNF r) p here m refl = 
            begin 
                choiceToℕ (getChoice (h m) (h (ℕ.suc m)) (H m))
            ≡⟨⟩ 
                choiceToℕ (getChoice (h n) (h (ℕ.suc n)) (H n))
             ≡⟨ lemma-getChoice-subst (h n) r (h (ℕ.suc n)) (newNF r) (H n) 
                                      (⋖-newNF r) hn≡r (sym p) ⟩
                choiceToℕ (getChoice r (newNF r) (⋖-newNF r))
            ≡⟨⟩ 
                choiceToℕ {m} {r} here
            ≡⟨⟩
                m
            ∎
            where
                hn≡r : h n ≡ r
                hn≡r = ⋖-left-corollary-newNF {n} {h n} {r} {h (ℕ.suc n)} {newNF r} 
                                        (H n) (sym p) refl 
        -- The next two cases, where c is not `here` but an earlier NF, are
        -- very similar.
        lemma-1 {suc n} h H (newNF r) p (earlier-new c) m refl = 
            lemma-1 {n} h H r r≡hn c (choiceToℕ (earlier-new c)) refl
            where
                r≡hn : r ≡ h n
                r≡hn = sym $ ⋖-left-corollary-newNF {n} {h n} {r} {h (ℕ.suc n)} 
                                        {newNF r} (H n) (sym p) refl 
        lemma-1 {suc n} h H (oldNF r c') p (earlier-old c) m refl = 
            lemma-1 {n} h H r r≡hn c (choiceToℕ (earlier-new c)) refl
            where
                r≡hn : r ≡ h n
                r≡hn = sym $ ⋖-left-corollary-oldNF {n} {h n} {r} {h (ℕ.suc n)} 
                                        {oldNF r c'} (H n) (sym p) c' refl 

        lemma'
            : {n : ℕ}
            → {r : NFRestr n}
            → {s : NFRestr (ℕ.suc n)}
            → (H : r ⋖ s)
            → here ≡ getChoice r s H
            → s ≡ newNF r
        lemma' {n} {r} {newNF r} (⋖-newNF r) refl = refl
        lemma' {n} {r} {oldNF r x} (⋖-oldNF r c) ()

        lemma-2 
            : {n : ℕ}
            → (h : NFRestrFam)
            → (H : (n : ℕ) → (h n ⋖ h (ℕ.suc n)))
            → h (ℕ.suc n) ≡ newNF (h n)
            → choiceToℕ (getChoice (h n) (h (ℕ.suc n)) (H n)) ≡ n
        lemma-2 {n} h H p = 
            begin 
                choiceToℕ (getChoice (h n) (h (ℕ.suc n)) (H n)) 
            ≡⟨ lemma-getChoice-subst (h n) (h n) (h (ℕ.suc n)) 
                                     (newNF (h n)) (H n) (⋖-newNF (h n)) refl p ⟩
                choiceToℕ (getChoice (h n) (newNF (h n)) (⋖-newNF (h n))) 
            ≡⟨⟩
                choiceToℕ {n} {h n} here
            ≡⟨⟩
                n
            ∎
            

        lemma
            : (h : NFRestrFam)
            → (H : (n : ℕ) → h n ⋖ h ( ℕ.suc n))
            → (n : ℕ)
            → (x : Choices (h n))
            → (p : x ≡ getChoice (h n) (h (ℕ.suc n)) (H n))
            → (m : ℕ)
            → NFSToℕ x ≡ m
            → choiceToℕ (getChoice (h m) (h (ℕ.suc m)) (H m)) ≡ m
        -- #TODO: this still proves the old goal
        -- "→ h (ℕ.suc m) ≡ newNF (h m)"
        -- Change to lemma-2.
        lemma h H n here p m refl = lemma-2 {n} h H (lemma' (H n) p)
        lemma h H (suc n) (earlier-new x) p m refl = 
            lemma-1 {ℕ.suc n} h H (h (ℕ.suc n)) refl x (choiceToℕ (earlier-new x)) refl

        f-fix : (n : ℕ) → f (f n) ≡ f n
        f-fix n = 
            begin 
                f (f n)
            ≡⟨⟩
                choiceToℕ (getChoice (h m) (h (ℕ.suc m)) (H m))
            ≡⟨ lemma h H n x refl (NFSToℕ (earlier-new x)) refl ⟩
                m
            ≡⟨⟩
                f n
            ∎
            where
                m : ℕ
                m = f n
                x : Choices (h n)
                x = getChoice (h n) (h (ℕ.suc n)) (H n)

        


--------------------------------------------------------------------------------
-- Properties of the conversions
--------------------------------------------------------------------------------
-- 1. Every NFRestr is actually 'reachable', i.e., actually a restriction
--  of some NFFun.
-- 2. combine & restrict+ form a pair of inverses
--  (up to function extensionality and first projections).

-- Important is to show that for every NFRestr there actually is a normalisation
-- function whose restriction is represents.
theo-all-NFRestr-reachable
    : {n : ℕ}
    → (r : NFRestr n)
    → Σ[ f ∈  NFFun ](r ≡ restrict f n)
theo-all-NFRestr-reachable {n} r = ?

theo-restrict-combine
    : (f : NFFun)
    →  (proj₁ ∘ combine ∘ restrict+) f ≈ proj₁ f
theo-restrict-combine f = ?

theo-combine-restrict
    : (H : Exence)
    → (proj₁ ∘ restrict+ ∘ combine) H ≈ proj₁ H
theo-combine-restrict H = ?
