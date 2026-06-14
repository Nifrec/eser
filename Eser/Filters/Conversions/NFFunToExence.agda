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
open import Relation.Binary.Definitions
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
open import Eser.Logic

open import Eser.Filters.Base
open import Eser.Filters.Properties 

module Eser.Filters.Conversions.NFFunToExence where

--------------------------------------------------------------------------------
-- Main functions
--------------------------------------------------------------------------------
-- Implementations and proofs of the theorems can be found further below.

-- Restrict a normalisation function into an Exence --
-- a sequence of NFRestrs that extend each other.
restrict+ : NFFun → Exence

-- Combine an extension sequence into a NFFun.
combine : Exence → NFFun


-- Restrict a normalisation function into a NFRestr
restrict : NFFun → (n : ℕ) → NFRestr n

--------------------------------------------------------------------------------
-- Main theorems
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

theo-restrict-combine
    : (f : NFFun)
    →  (proj₁ ∘ combine ∘ restrict+) f ≈ proj₁ f

theo-combine-restrict
    : (H : Exence)
    → (proj₁ ∘ restrict+ ∘ combine) H ≈ proj₁ H

--------------------------------------------------------------------------------
-- Implementation of `combine`
--------------------------------------------------------------------------------
-- This requires quite a few auxiliary functions and lemmas.


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

-- `combine : Exence → NFFun` maps an exence not only to a function f
-- but also to the proofs f-leq and f-fix that f is a NFFun,
-- and those proofs had better be in a opaque block to reduce RAM usage.
-- This module just makes this easier to organise.
module CombineData 
    (h : (n : ℕ) → NFRestr n)
    (H : (n : ℕ) → h n ⋖ h (ℕ.suc n))
    where
    f : ℕ → ℕ
    f = choiceToℕ ∘ (getChoiceFromExence (h , H))

    opaque
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
            lemma-1 {ℕ.suc n} h H (h (ℕ.suc n)) refl x 
                    (choiceToℕ (earlier-new x)) refl

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

combine (h , H) = (f , f-leq , f-fix)
    where open CombineData h H

--------------------------------------------------------------------------------
-- Implementation of `restrict+`
--------------------------------------------------------------------------------

module RestrictImplementation (f' : NFFun) where
    open import Data.Nat.Properties using (≤-refl ; <⇒≤ ; m<n⇒m≤1+n ; ≤⇒≯ ; m≤n⇒m<n∨m≡n)

    f : ℕ → ℕ
    f = proj₁ f'
    f-leq : (n : ℕ) → f n ≤ n
    f-leq = proj₁ $ proj₂ f'

    -- Implementation notes:
    -- (1) h', H' and K' are computed in 𝐦𝐮𝐭𝐮𝐚𝐥 𝐢𝐧𝐝𝐮𝐜𝐭𝐢𝐨𝐧;
    --  h' encodes the actual NFRestrFam, H' the proof of being
    --  an Exence, and K' the proof that it encodes f.
    --
    -- (2) In H' and K', the argument p could have been computed from q, 
    -- (ℕ-inequalities are proof irrelevant anyway);
    -- but giving p is more convenient, 
    -- otherwise one probably needs to substitute
    -- the actually used p anyway...

    h' : (n : ℕ) → (m : ℕ) → m ≤ n → NFRestr m
    H' : (n : ℕ) 
        → (m : ℕ) 
        → (p : m ≤ n)       
        → (q : ℕ.suc m ≤ n) 
        → h' n m p ⋖ h' n (ℕ.suc m) q
    K' : (n : ℕ) 
        → (m : ℕ) 
        → (p : m ≤ n) 
        → (q : ℕ.suc m ≤ n) 
        → choiceToℕ (getChoice (h' n m p) (h' n (ℕ.suc m) q) (H' n m p q))
            ≡ f m
    
    -- h' can output a `NFRestr m` for different values of n.
    -- But these should all be the same!
    -- (For H' and K' there is no need to prove this, since their
    -- final types are proof-irrelevant anyway).
    h'-coh 
        : (n : ℕ) 
        → (m : ℕ) 
        → (p : m ≤ n) 
        → (q : m ≤ ℕ.suc n) 
        → h' n m p ≡ h' (ℕ.suc n) m q 

    h' 0 0 z≤z = empty
    h' n@(ℕ.suc n') m m≤1+n with m≤n⇒m<n∨m≡n m≤1+n
    ... | inj₁ m<1+n = h' n' m (s≤s⁻¹ m<1+n)
    ... | inj₂ m≡1+n with (<-cmp (f n') n')
    ... | tri< fn<n  _   _   = ?
    --... | tri≈ _    fn≡n _   = subst NFRestr (sym m≡1+n) $ newNF (h' n n' (n≤1+n n'))
    ... | tri≈ _    fn≡n _   = {!  !}
        --^ #TODO: use the commented out substitution on pre-2.
        -- #TODO: in the naming, sometimes I use n and n', sometimes I use 1+n and n.
        -- This is confusing.
        where
            pre : NFRestr (suc n')
            pre = newNF (h' n' n' (≤-refl))
            pre-2 : pre ≡ newNF (h' n n' (n≤1+n n'))
            pre-2 = cong newNF (h'-coh n' n' (≤-refl {n'}) (n≤1+n n'))

    ... | tri> _    _   n'<fn' = ⊥-elim $ ≤⇒≯ (f-leq n') n'<fn'

    -- Extracting actual functions h, H and K without the 'm ≤ n' indirection.
    -- The idea is straightforward: just pointwise pick the output
    -- using m ≔ n and reflexivity of ≤. 
    -- Only a lot of verbose substitutions are needed 
    -- to make the types work out...
        
    h : (n : ℕ) → NFRestr n
    h n = h' n n (≤-refl {n})

    H : (n : ℕ) → h n ⋖ h (ℕ.suc n)
    H n = subst (λ x → x ⋖ h' (suc n) (suc n) ≤-refl) 
                (sym $ h'-coh n n (≤-refl) (n≤1+n n))
                (H' (suc n) n (n≤1+n n) (≤-refl {suc n}))

    K   : (n : ℕ)
        → (choiceToℕ (getChoice (h n) (h (ℕ.suc n)) (H n))) ≡ f n
    K n = subst (λ (x , y) → choiceToℕ (getChoice x (h (suc n)) y) ≡ f n )
            (restIsProofIrrel (λ x → ⋖-irrel x (h (ℕ.suc n))) H₁ H₂ pre-eq)
            raw
        where
            pre-eq : h' (ℕ.suc n) n (n≤1+n n) ≡ h n
            pre-eq = sym $ h'-coh n n (≤-refl) (n≤1+n n)
            H₁ : (h' (suc n) n (n≤1+n n)) ⋖ (h (suc n))
            H₁ = H' (suc n) n (n≤1+n n) ≤-refl
            H₂ :  (h n) ⋖ (h (suc n))
            H₂ = H n
            raw : choiceToℕ(getChoice (h' (suc n) n (n≤1+n n)) (h (suc n))
                (H' (suc n) n (n≤1+n n) ≤-refl))
                ≡ f n 
            raw = K' (ℕ.suc n) n (n≤1+n n) (≤-refl {ℕ.suc n})
        

restrict+ f' = (h , H)
    where open RestrictImplementation f'

-- Extend a family B of dependent types from indices in {0, ..., n-1} 
-- to {0, ..., n} by providing B n.
dep-extend
    : (n : ℕ)
    → (B : ℕ → Set)
    → ((m : ℕ) → m < n → B m)
    → B n
    → ((m : ℕ) → m < ℕ.suc n → B m)
dep-extend n B Fam Bn m m<1+n with m Data.Nat.≟ n
... | (yes m≡n) = subst B (sym m≡n) Bn
... | (no m≢n) = Fam m m<n
    where
        open import Data.Nat.Properties using (m<1+n⇒m<n∨m≡n)
        m<n : m < n
        m<n = elimCaseRight (m<1+n⇒m<n∨m≡n m<1+n) m≢n

{-# WARNING_ON_USAGE dep-extend "Move dep-extend to correct file" #-}

restrict = proj₁ ∘ restrict+

        


--------------------------------------------------------------------------------
-- Proofs of the theorems
--------------------------------------------------------------------------------
theo-all-NFRestr-reachable {n} r = ?

theo-restrict-combine f = ?

theo-combine-restrict H = ?
