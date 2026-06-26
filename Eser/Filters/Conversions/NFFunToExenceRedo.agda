-- Module      : Eser.Filters.Conversions.NFFunToExence
-- Description : Converting a NFFun to extensions-sequence, and inversity proof.
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

open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n ; 1+n≰n
    ; ≤-irrelevant
    ; m<1+n⇒m<n∨m≡n
    ; <-≤-trans
    ; m≢1+n+m
    ; <-trans
    ; n<1+n
    ; <⇒≤ 
    ; m<n⇒m≤1+n 
    ; ≤⇒≯ 
    ; m≤n⇒m<n∨m≡n
    ; n≮n
    )

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_ ; restIsProofIrrel ; Sm≤n→m≤n ; 1+n≮n 
                           ; doubleSubst 
                           ; depSubst
                           ; tri-≡
                           )
open import Eser.Logic

open import Eser.Filters.Base
open import Eser.Filters.Properties 
open import Eser.Filters.Resurface

module Eser.Filters.Conversions.NFFunToExenceRedo where

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

theo-combine∘restrict+
    : (f : NFFun)
    →  (proj₁ ∘ combine ∘ restrict+) f ≈ proj₁ f

theo-restrict+∘combine
    : (H : Exence)
    → (proj₁ ∘ restrict+ ∘ combine) H ≈ proj₁ H

--------------------------------------------------------------------------------
-- Implementation of `combine`
--------------------------------------------------------------------------------
-- This requires quite a few auxiliary functions and lemmas.
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
             ≡⟨ lemma-choiceToℕ∘getChoice (h n) r (h (ℕ.suc n)) (newNF r) (H n) 
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
            ≡⟨ lemma-choiceToℕ∘getChoice (h n) (h n) (h (ℕ.suc n)) 
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

extension-must-be-newNF
    : {n : ℕ}
    → {r : NFRestr n}
    → {s : NFRestr (suc n)}
    → (H : r ⋖ s)
    → (c : Choices r)
    → c ≡ getChoice r s H
    → n ≡ choiceToℕ (getChoice r s H)
    → getChoice r s H ≡ here × s ≡ newNF r
extension-must-be-newNF {n} {r} {newNF r} (⋖-newNF r) c refl refl = (refl , refl)
extension-must-be-newNF {n} {r} {s} (⋖-oldNF r c) (earlier-new c) refl p = ans
    where
        n<n : n < n
        n<n = subst (λ x → x < n) (sym p) (NFSToℕ-≤ {n} {r} c)
        ans = ⊥-elim (1+n≰n n<n)

-- Given a finite sequence of pointwise extensions,
-- earlier NFRestrs in the sequence are ⋖+ related to later NFRestrs.
connect-⋖-to-⋖+
    : {n : ℕ}
    → (h : (m : ℕ) → m ≤ n → NFRestr m)
    → (H : (m : ℕ) → (p : m ≤ n) → (q : suc m ≤ n) → h m p ⋖ h (suc m) q)
    → (m l : ℕ) → m < l → (p : m ≤ n) → (q : l ≤ n) → h m p ⋖+ h l q
connect-⋖-to-⋖+ {n} h H m (suc l) m<1+l p q with m<1+n⇒m<n∨m≡n m<1+l
... | inj₁ m<l = ⋖+-multistep-anychoice rec (H l q' q)
    where
        q' : l ≤ n
        q' = Sm≤n→m≤n q
        rec : h m p ⋖+ h l q'
        rec = connect-⋖-to-⋖+ {n} h H m l m<l p q'
... | inj₂ refl = ⋖+-onestep (H m p q)

subst-idx-in-NFRestr
    : {a b n' : ℕ}
    → (f : (m : ℕ) → m ≤ n' → NFRestr m)
    → (s : NFRestr a)
    → (z : a ≡ b)
    → (p : a ≤ n')
    → (q : b ≤ n')
    → s ≡ f a p
    → s ≡ subst NFRestr (sym z) (f b q)
subst-idx-in-NFRestr {a} {b} {n'} f s refl p q s≡fap =
    begin 
        s
    ≡⟨ s≡fap ⟩
        f a p
    ≡⟨⟩ -- By J rule we assume a ≗ b
        f b p
    ≡⟨ cong (f b) $ ≤-irrelevant p q ⟩ -- proof irrelevance
        f b q
    ≡⟨⟩
        subst NFRestr refl (f b q)
    ∎
    
module RestrictImplementation (f' : NFFun) where

    f : ℕ → ℕ
    f = proj₁ f'
    f-leq : (n : ℕ) → f n ≤ n
    f-leq = proj₁ $ proj₂ f'
    f-fix : (n : ℕ) → f (f n) ≡ f n
    f-fix = proj₂ $ proj₂ f'
        
    -- Implementation note: via mutual induction we define:
    -- * h : sequence of choices compiled into an NFRestrFam.
    --  (so h n records the choices of equivalence class
    --  for {0, 1, 2, ..., n-1}).
    -- * L : individual choices that make up the extensions in h.
    -- * N : proof that h is indeed a sequence of extensions.
    -- * H : proof that h froms an Exence. 
    h : (n : ℕ) → NFRestr n
    L : (n : ℕ) → Choices (h n)
    N : (n m : ℕ) → (m < n) → h m ⋖+ h n
    H : (n : ℕ) → h n ⋖ h (ℕ.suc n)

    L-cases 
        : (n : ℕ) 
        → Tri (f n < n) (f n ≡ n) (n < f n)
        → Choices (h n)

    N-cases
        : (n n' m : ℕ)
        → (n ≡ suc n')
        → (m < n') ⊎ (m ≡ n')
        → h m ⋖+ h n

    h zero = empty
    h (suc n) = addChoice (h n) (L n)

    L n = L-cases n (<-cmp (f n) n)
    L-cases n (tri≈ _ fn≡n _) = here
    L-cases n (tri> _ _ n<fn) = ⊥-elim $ ≤⇒≯ (f-leq n) n<fn
    L-cases n@(suc n') (tri< fn<n _ _) = 
        earlier-new $ resurface {n} (h n) {f n} fn<n

    N 0 m () 
    N n@(suc n') m m<n = N-cases n n' m refl (m<1+n⇒m<n∨m≡n m<n)
    N-cases n@(suc n') n' m refl (inj₁ m<n') = 
        ⋖+-multistep-anychoice hm⋖+hn' hn'⋖hn
        where
            hm⋖+hn' : h m ⋖+ h n'
            hm⋖+hn' = N n' m m<n'

            hn'⋖hn : h n' ⋖ h n
            hn'⋖hn = ⋖-addChoice {n'} {h n'} (L n')
    N-cases n@(suc n') n' n' refl (inj₂ refl) = ⋖+-onestep hn'⋖hn
        where
            hn'⋖hn : h n' ⋖ h n
            hn'⋖hn = ⋖-addChoice {n'} {h n'} (L n')

    H n = ⋖-addChoice {n} {h n} (L n)

    lemma-L-recovers-choice
        : (n : ℕ)
        → L n ≡ getChoice (h n) (h (suc n)) (H n)

    lemma-L-recovers-choice n = ? 
        -- Use getChoice-addChoice lemma!

restrict+ f' = (h , H)
    where open RestrictImplementation f'

restrict = proj₁ ∘ restrict+

--------------------------------------------------------------------------------
-- Proofs of the theorems
--------------------------------------------------------------------------------
module LemmaL (f' : NFFun) where
    open RestrictImplementation f'
    open import Data.Nat.Induction
    open import Data.Maybe

    lemma-L
        : (n : ℕ)
        → choiceToℕ (L n) ≡ f n
    lemma-L-<-rec
        : (n : ℕ)
        → ({m : ℕ} → (m < n) → (choiceToℕ (L m) ≡ f m))
        → choiceToℕ (L n) ≡ f n

    lemma-L-<-rec-cases
        : (n : ℕ)
        → ({m : ℕ} → (m < n) → (choiceToℕ (L m) ≡ f m))
        → (t₀ : Tri (f n < n) (f n ≡ n) (n < f n))
        → (t₁ : <-cmp (f n) n ≡ t₀) 
        → choiceToℕ (L n) ≡ f n

    lemma-L = <-rec (λ n → choiceToℕ (L n) ≡ f n) lemma-L-<-rec

    lemma-L-<-rec n rec = lemma-L-<-rec-cases n rec (<-cmp (f n) n) refl

    lemma-L-<-rec-cases n rec (tri> _ _ n<fn) t₁ = ⊥-elim $ ≤⇒≯ (f-leq n) n<fn
    lemma-L-<-rec-cases n rec (tri≈ v₀ fn≡n v₁) t₁ = 
        begin 
            choiceToℕ (L n)
        ≡⟨⟩
            choiceToℕ (L-cases n (<-cmp (f n) n))
        ≡⟨ cong (λ x → choiceToℕ (L-cases n x)) t₁ ⟩
            choiceToℕ (L-cases n (tri≈ v₀ fn≡n v₁))
        ≡⟨⟩
            choiceToℕ {n} {h n} here
        ≡⟨⟩
            n
        ≡⟨ sym fn≡n ⟩
            f n
        ∎
    lemma-L-<-rec-cases n@(suc n') rec (tri< fn<n v₀ v₁) t₁ =
        begin 
            choiceToℕ (L n)
        ≡⟨⟩
            choiceToℕ (L-cases n (<-cmp (f n) n))
        ≡⟨ cong (λ x → choiceToℕ (L-cases n x)) t₁ ⟩
            choiceToℕ (L-cases n (tri< fn<n v₀ v₁))
        ≡⟨⟩
            choiceToℕ (earlier-new $ resurface {n} (h n) {f n} fn<n)
        ≡⟨ just-injective lemma ⟩
            choiceToℕ (L (f n))
        ≡⟨ rec (fn<n) ⟩
            f (f n)
        ≡⟨ f-fix n ⟩
            f n
        ∎
        where
            open import Data.Maybe.Properties using (just-injective)
            1+fn≤n : suc (f n) ≤ n
            1+fn≤n = fn<n

            lemma : 
                just (choiceToℕ (earlier-new $ resurface {n} (h n) {f n} fn<n))
                ≡ 
                just (choiceToℕ (L (f n)))
            lemma =
                begin 
                    just (choiceToℕ (earlier-new $ resurface {n} (h n) {f n} fn<n))
                ≡⟨⟩
                    just (NFSToℕ (earlier-new $ resurface {n} (h n) {f n} fn<n))
                ≡⟨⟩
                    just (NFSToℕ (resurface {n} (h n) {f n} fn<n))
                ≡⟨ resurface-correctness (h n) fn<n 1+fn≤n ⟩
                    NFRestrToℕ (trim' (h n) 1+fn≤n)
                ≡⟨ cong NFRestrToℕ $ lemma-trim'-exence h H n (f n) 1+fn≤n  ⟩
                    NFRestrToℕ (h (suc (f n)))
                ≡⟨⟩
                    NFRestrToℕ (addChoice (h (f n)) (L (f n)))
                ≡⟨ lemma-NFRestrToℕ-addChoice {f n} (h (f n)) (L (f n)) ⟩
                    just (choiceToℕ (L (f n)))
                ∎

theo-all-NFRestr-reachable {n} r = ?

theo-combine∘restrict+ f' n = 
    begin 
        proj₁ (combine (restrict+ f')) n
    ≡⟨⟩ -- Unfold definitions:
        choiceToℕ (getChoice (h n) (h (suc n)) (H n))
    ≡⟨⟩
        choiceToℕ (getChoice (h n) (addChoice (h n) (L n)) (H n))
    ≡⟨ cong choiceToℕ $ lemma-getChoice-addChoice {n} (h n) (L n) (H n) ⟩
        choiceToℕ (L n)  
    ≡⟨ lemma-L n ⟩
        f n
    ∎
    where
        open RestrictImplementation f'
        open LemmaL f'
        -- This import gives the following:
        -- f : ℕ → ℕ
        -- f-leq : (n : ℕ) → f n ≤ n
        -- f-fix : (n : ℕ) → f (f n) ≡ f n
        -- f' ≡ (f , f-leq , f-fix)
        -- h : (n : ℕ) → NFRestr n
        -- h = proj₁ (restrict+ f')
        -- H : (n : ℕ) → h n ⋖ h (suc n)
        -- H = proj₂ (restrict+ f')
        -- L : (n : ℕ) → Choices (h n)
        -- N : (n m : ℕ) → (m < n) → h m ⋖+ h n

module ResCo 
    (h : (n : ℕ) → NFRestr n) 
    (H : (n : ℕ) → h n ⋖ h (suc n)) 
    where
    open RestrictImplementation (combine (h , H)) renaming (h to h' ; H to H')

    C : (n : ℕ) → Choices (h n)
    C n = proj₁ (⋖-to-addChoice (H n))

    main-lemma
        : (n : ℕ)
        → (w : h' n ≡ h n)
        → (c : Choices (h n))
        → (c ≡ proj₁ ( ⋖-to-addChoice (H n)))
        → _≡_ {A = Σ[ r ∈ NFRestr n ] Choices r} (h' n , L n) (h n , c)
    main-lemma n w c@here c-prop = 
        begin 
            (h' n , L n)
        ≡⟨⟩
            (h' n , L-cases n (<-cmp (f n) n))
        ≡⟨ cong (λ x → (h' n , L-cases n x)) <-cmp-outp ⟩
            (h' n , L-cases n (tri≈ x₀ fn≡n x₁))
        ≡⟨⟩
            (h' n , here {n} {h' n})
        ≡⟨ tuples-eq (h' n) (h n) w ⟩
            (h n , here {n} {h n})
        ∎
        where
            eq : h (suc n) ≡ addChoice (h n) c
            eq = subst (λ x → h (suc n) ≡ addChoice (h n) x) 
                       (sym c-prop)
                       (proj₂ $ ⋖-to-addChoice (H n))

            X : h n ⋖ addChoice (h n) c
            X = subst (h n ⋖_) eq (H n)

            X-prop : (h (suc n) , H n) ≡ (addChoice (h n) c , X)
            X-prop = depSubst (h (suc n)) (addChoice (h n) c) eq (H n) 

            fn≡n : f n ≡ n
            fn≡n =
                begin 
                    f n
                ≡⟨⟩
                    choiceToℕ (getChoice (h n) (h (suc n)) (H n))
                ≡⟨ cong (λ (x , y) → choiceToℕ (getChoice (h n) x y)) X-prop ⟩
                    choiceToℕ (getChoice (h n) (addChoice (h n) c) X)
                ≡⟨ cong choiceToℕ (lemma-getChoice-addChoice (h n) c X) ⟩
                    choiceToℕ {n} {h n} c
                ≡⟨⟩
                    choiceToℕ {n} {h n} here
                ≡⟨⟩
                    n
                ∎

            x₀ : f n ≮ n
            x₀ = proj₁ (tri-≡ (f n) n fn≡n)
            x₁ : n ≮ f n
            x₁ = proj₁ $ proj₂ (tri-≡ (f n) n fn≡n)
            <-cmp-outp : <-cmp (f n) n ≡ tri≈ x₀ fn≡n x₁
            <-cmp-outp = proj₂ $ proj₂ $ tri-≡ (f n) n (fn≡n)
        
            tuples-eq
                : (r r' : NFRestr n)
                → r ≡ r'
                → (r , here {n} {r}) ≡ (r' , here {n} {r'})
            tuples-eq r r' refl = refl

    main-lemma n w (earlier-new c) c-prop = {! !}



theo-restrict+∘combine (h , H) zero = 
    begin 
        (proj₁ ∘ restrict+ ∘ combine) (h , H) zero
    ≡⟨⟩
        empty
    ≡⟨ sym $ empty-is-unique-zero (h zero) ⟩
        h zero
    ∎
theo-restrict+∘combine (h , H) (suc n') = ?
    --begin 
    --    (proj₁ ∘ restrict+ ∘ combine) (h , H) (suc n')
    --≡⟨⟩
    --    addChoice (h' n') (L n')
    --≡⟨ cong (λ (r , c) → addChoice {n'} r c) 
    --   $ depSubst (h' n') (h n') IH (L n') 
    -- ⟩
    --    addChoice (h n') (subst Choices IH (L n'))
    --≡⟨ cong (λ x → addChoice (h n') (subst Choices IH x)) 
    --        $ lemma-L-recovers-choice n' ⟩
    --    addChoice (h n') (subst Choices IH $ getChoice (h' n') (h' (suc n')) (H' n'))
    --≡⟨ cong (addChoice (h n')) 
    --        $ sym 
    --        $ lemma-getChoice-subst {n'} (h n') (h' n') 
    --                                (h (suc n')) (h' (suc n')) (H n') (H' n') IH ? ⟩
    --    addChoice (h n') (getChoice (h n') (h (suc n')) (H n'))
    --≡⟨ cong (λ (y , x) → addChoice (h n') (getChoice (h n') y x)) c-prop-X ⟩
    --    addChoice (h n') (getChoice (h n') (addChoice (h n') c) X)
    --≡⟨ cong (addChoice (h n')) $ lemma-getChoice-addChoice (h n') c X ⟩
    --    addChoice (h n') c
    --≡⟨ sym c-prop ⟩
    --    h (suc n')
    --∎
    --where
    --    open RestrictImplementation (combine (h , H))
    --        renaming (h to h' ; H to H')
    --    IH : h' n' ≡ h n'
    --    IH = theo-restrict+∘combine (h , H) n'
    --    c : Choices (h n')
    --    c = proj₁ $ ⋖-to-addChoice (H n')
    --    c-prop : h (suc n') ≡ addChoice (h n') c
    --    c-prop = proj₂ $ ⋖-to-addChoice (H n')
    --    X : h n' ⋖ addChoice (h n') c
    --    X = ⋖-addChoice c
    --    c-prop-X : (h (suc n') , H n') ≡ (addChoice (h n') c , X)
    --    c-prop-X = restIsProofIrrel (⋖-irrel (h n')) (H n') X c-prop 
    
