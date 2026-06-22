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

open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n ; 1+n≰n
    ; ≤-irrelevant
    ; m<1+n⇒m<n∨m≡n
    ; <-≤-trans
    ; m≢1+n+m
    )

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_ ; restIsProofIrrel ; Sm≤n→m≤n ; 1+n≮n )
open import Eser.Logic

open import Eser.Filters.Base
open import Eser.Filters.Properties 
open import Eser.Filters.Resurface

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
    open import Data.Nat.Properties 
        using (≤-refl ; <⇒≤ ; m<n⇒m≤1+n ; ≤⇒≯ ; m≤n⇒m<n∨m≡n)

    f : ℕ → ℕ
    f = proj₁ f'
    f-leq : (n : ℕ) → f n ≤ n
    f-leq = proj₁ $ proj₂ f'
    f-fix : (n : ℕ) → f (f n) ≡ f n
    f-fix = proj₂ $ proj₂ f'

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

    -- The proofs of h', H', K' and h'-coh follow the same case distinctions.
    h'-cases 
        : (n' : ℕ) 
        → (m : ℕ) 
        → (m < suc n' ⊎ m ≡ suc n') 
        → Tri (f n' < n') (f n' ≡ n') (n' < f n')
        → NFRestr m

    h'-m≡n-case-get-choice
        : (n' m : ℕ)
        → m ≡ suc n'
        → Tri (f n' < n') (f n' ≡ n') (n' < f n')
        → Choices (h' n' n' ≤-refl)

    H'-cases 
        : (n' : ℕ) 
        → (m : ℕ) 
        → (p : m ≤ suc n')
        → (q : suc m ≤ suc n')
        → (p₀ : m < suc n' ⊎ m ≡ suc n') 
        → (p₁ : p₀ ≡ m≤n⇒m<n∨m≡n p)
        → (q₀ : suc m < suc n' ⊎ suc m ≡ suc n')
        → (q₁ : q₀ ≡ m≤n⇒m<n∨m≡n q)
        → (t₀ : Tri (f n' < n') (f n' ≡ n') (n' < f n'))
        → (t₁ : t₀ ≡ <-cmp (f n') n')
        → h' (suc n') m p ⋖ h' (suc n') (ℕ.suc m) q


    h' 0 0 z≤z = empty
    h' n@(ℕ.suc n') m m≤n = h'-cases n' m (m≤n⇒m<n∨m≡n m≤n) (<-cmp (f n') n')

    -- Case 1.1: m < n. Use a recursive call.
    h'-cases n' m  (inj₁ m<n) _ = h' n' m (s≤s⁻¹ m<n)

    -- Case 2: m ≡ n ≡ 1+n', 
    -- so no possible recursive call will give a NFRestr (1+n');
    -- we need to build a new one.
    -- An NFRestr of length (1+n') is obtained by taking a NFRestr n'
    -- and adding a choice for the normal form for n'.
    -- Make a case distinction: either n' is a fixpoint of f (a new normal form)
    -- or not (then f assigns n' an earlier normal form).
    
    -- Case 2.1: the normal form of n' is a smaller number.
    h'-cases n' m (inj₂ m≡n) tri
        = subst NFRestr (sym m≡n) $ 
            addChoice (h' n' n' (≤-refl)) (h'-m≡n-case-get-choice n' m m≡n tri)
            
    h'-m≡n-case-get-choice n' m refl (tri< fn'<n'  _   _) = c-surface
        where
            -- 0. Let d ≔ f n', be a fixpoint of f smaller than n'.
            -- 1. Show `h' n' 1+d fn'<n'` is (newNF h' n' 1+d fn'<n'),
            --  i.e., show that d was chosen to be a new equiv class.
            -- 2. Now resurface the choice of «making d a new class»
            --  from (h' n' d) to (h' n' n').
            -- 3. Return (h' n' n') extended with that choice.
            d : ℕ
            d = f n'

            fd≡d : f d ≡ d
            fd≡d = f-fix n'

            p : d ≤ n'
            p = <⇒≤ fn'<n'

            q : (ℕ.suc d) ≤ n'
            q = fn'<n'

            r' : NFRestr d
            r' = h' n' d p

            c : Choices r'
            c = getChoice r' (h' n' (ℕ.suc d) q) (H' n' d p q)

            H₀ : choiceToℕ c ≡ d
            H₀ = trans (K' n' d p q) fd≡d

            H₁ : h' n' (ℕ.suc d) fn'<n' ≡ newNF r'
            H₁ = proj₂ (extension-must-be-newNF (H' n' d p q) c refl (sym H₀))

            rec : NFRestr n'
            rec = h' n' n' (≤-refl)

            newNFr'⋖+=rec : newNF r' ⋖+= rec
            newNFr'⋖+=rec with (<-cmp (suc d) n')
            ... | tri< 1+d<n' _ _ = 
                inj₂ $ subst (λ x → x ⋖+ rec) H₁ 
                     $ connect-⋖-to-⋖+ {n'} (h' n') (H' n') (suc d) n' 
                                       1+d<n' q ≤-refl
            ... | tri≈ _ 1+d≡n' _ = inj₁ (sym 1+d≡n' , 
                subst-idx-in-NFRestr {suc d} {n'} {n'}
                (h' n') (newNF r') 1+d≡n'
                q (≤-refl) (sym H₁)
                )
            ... | tri> _ _ n'<1+d = ⊥-elim $ ≤⇒≯ fn'<n' n'<1+d

            c-surface : Choices rec
            c-surface = proj₁ $ resurface-nf {d} {n'} r' rec newNFr'⋖+=rec

    -- Case 2.2: n' should be a new normal form. 
    h'-m≡n-case-get-choice n' m refl (tri≈ _  fn'≡n' _) = here {n'} {h' n' n' ≤-refl}

    -- Case 2.3: f n' > n'. This contradicts `f-leq : f x ≤ x for all x`.
    h'-m≡n-case-get-choice n' m refl (tri> _  _ n'<fn') 
        = ⊥-elim $ ≤⇒≯ (f-leq n') n'<fn'

    -- The implementation of H mimicks all the cases.
    H' 0 0 z≤z ()
    H' n@(suc n') m p q = H'-cases n' m p q (m≤n⇒m<n∨m≡n p) refl 
                                            (m≤n⇒m<n∨m≡n q) refl 
                                            (<-cmp (f n') n') refl
    H'-cases n' m p q (inj₁ m<n) p₁ (inj₁ 1+m<n) q₁ t₀ t₁ = {! !}
    H'-cases n' n' p q (inj₁ m<n) p₁ (inj₂ refl) q₁ (tri< fn'<n a b) t₁ = ans
        where
            LHS : h' (suc n') n' p ≡ h' n' n' ≤-refl
            LHS =
                begin 
                    h' (suc n') n' p
                ≡⟨⟩
                    h'-cases n' n' (m≤n⇒m<n∨m≡n p) (<-cmp (f n') n')
                ≡⟨ cong (λ x → h'-cases n' n' x (<-cmp (f n') n')) (sym p₁) ⟩
                    h'-cases n' n' (inj₁ m<n) (<-cmp (f n') n')
                ≡⟨ cong (λ x → h'-cases n' n' (inj₁ m<n) x) (sym t₁) ⟩
                    h'-cases n' n' (inj₁ m<n) (tri< fn'<n a b)
                ≡⟨⟩
                    h' n' n' (s≤s⁻¹ m<n)
                ≡⟨ cong (h' n' n') (≤-irrelevant (s≤s⁻¹ m<n) ≤-refl) ⟩
                    h' n' n' ≤-refl
                ∎

            c : Choices (h' n' n' ≤-refl)
            -- #TODO: refactor def of h' to use a fun "getC"
            -- Then the second next hole below should hold by refl :)
            c = ? 

            RHS : h' (suc n') (suc n') q ≡ addChoice (h' n' n' ≤-refl) c
            RHS = 
                begin 
                    h' (suc n') (suc n') q 
                ≡⟨⟩
                    h'-cases n' (suc n') (m≤n⇒m<n∨m≡n q) (<-cmp (f n') n')
                    -- #TODO: subst q₁ and t₁
                ≡⟨ cong (λ x → h'-cases n' (suc n') x (<-cmp (f n') n')) (sym q₁) ⟩
                    h'-cases n' (suc n') (inj₂ refl) (<-cmp (f n') n')
                ≡⟨ cong (λ x → h'-cases n' (suc n') (inj₂ refl) x) (sym t₁) ⟩
                    h'-cases n' (suc n') (inj₂ refl) (tri< fn'<n a b)
                ≡⟨ ? ⟩
                    -- We matched m≡n to refl, so the subst dissapears :)
                    subst NFRestr refl (addChoice (h' n' n' ≤-refl) c)
                ≡⟨⟩
                    addChoice (h' n' n' ≤-refl) c
                ∎
                
                
            ans : h' (suc n') n' p ⋖ h' (suc n') (suc n') q
            ans = ?
    H'-cases n' n' p q (inj₁ m<n) p₁ (inj₂ refl) q₁ (tri≈ _ fn'≡n' _) t₁ = {! !}
    H'-cases n' n' p q (inj₁ m<n) p₁ (inj₂ refl) q₁ (tri> _ _ n'<fn') t₁ = 
        ⊥-elim $ ≤⇒≯ (f-leq n') n'<fn'
    H'-cases n' m p q (inj₂ m≡n) p₁ (inj₁ 1+m<n) q₁ t₀ t₁ = 
        ⊥-elim $ 1+n≮n n 1+n<n
        where
            n : ℕ
            n = suc n'
            1+n<n : suc n < n
            1+n<n = subst (λ x  → suc x < n) m≡n 1+m<n
    H'-cases n' m p q (inj₂ m≡n) p₁ (inj₂ 1+m≡n) q₁ t₀ t₁ =
        ⊥-elim $ m≢1+n+m m {n = 0} (trans m≡n (sym 1+m≡n))

    --K' 0 0 z≤z q = ?
    --K' n@(suc n') m m≤n q with m≤n⇒m<n∨m≡n m≤n
    --... | inj₁ m<n = ?
    --... | inj₂ m≡n with (<-cmp (f n') n')
    --... | tri< fn'<n'  _   _   = ?
    --... | tri≈ _    fn'≡n' _   = ?
    --... | tri> _    _   n'<fn' = ⊥-elim $ ≤⇒≯ (f-leq n') n'<fn'

    h'-coh 0 0 z≤z q = ?
    h'-coh n@(suc n') m m≤n q with m≤n⇒m<n∨m≡n m≤n
    ... | inj₁ m<n = ?
    ... | inj₂ m≡n with (<-cmp (f n') n')
    ... | tri< fn'<n'  _   _   = ?
    ... | tri≈ _    fn'≡n' _   = ?
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
