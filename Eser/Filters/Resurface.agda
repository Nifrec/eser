-- Module      : Eser.Filters.Resurface
-- Description : Dig up an earlier used normal-form-choice and reuse it.
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
open import Data.Nat.Properties using (m<1+n⇒m<n∨m≡n ; m≤n⇒m<n∨m≡n ; n≮n
    ; ≤-irrelevant)
open import Data.Maybe

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
    → NFS r
resurface-cases
    : {n' : ℕ}
    → (r : NFRestr (suc n'))
    → {m : ℕ}
    → (m < n') ⊎ (m ≡ n')
    → NFS r

resurface {suc n'} r {m} m<n = resurface-cases {n'} r {m} (m<1+n⇒m<n∨m≡n m<n)

-- First two cases: the target choice was not the previous chocie,
-- dig deeper using recursion.
resurface-cases {n'} (newNF r') {m} (inj₁ m<n') = 
    earlier-new (resurface {n'} r' {m} m<n')
resurface-cases {n'} (oldNF r' c) {m} (inj₁ m<n') = 
    earlier-old (resurface {n'} r' {m} m<n')
-- Next two cases: we want to repeat the previous choice.
-- First one: the previous choice was 'here' : r' |-> newNF r'.
resurface-cases {n'} (newNF r') {n'} (inj₂ refl) = here
-- Second one: the previous choice was 'c' : r' |-> oldNF r' c.
resurface-cases {n'} (oldNF r' c) {n'} (inj₂ refl) = earlier-old c

-- Proof that the output of resurface actually encodes the same normal form as
-- encoded in the dug-up choice.
-- I.e., that resurface doesn't contain a typo or a off-by-1 error.
--
-- Note about the types:
-- * We want to resurface the choice of m. This requires looking
--  in a NFRestr (suc m). Since m < n, it holds suc m ≤ n,
--  so r always has a sub-NFRestr of size suc m.
-- * NFRestrToℕ maps the NF encoded in the last choice to ℕ,
--  so to map a choice of m to ℕ the input should be a NFRestr (suc m).
-- * `resurface m<n` finds the choice of a NFRestr m that was
--  used to create the NFRestr (suc m).
-- * This explains the asymmetry with the LHS using m<n and the RHS using 1+m≤n.
resurface-correctness
    : {n : ℕ}
    → (r : NFRestr n)
    → {m : ℕ}
    → (m<n : m < n)
    → (1+m≤n : suc m ≤ n)
    → just (NFSToℕ (resurface r m<n)) ≡ NFRestrToℕ {suc m} (trim' r 1+m≤n)
resurface-correctness {suc n'} r {m} p q = 
    resurf-corr-cases r p (m<1+n⇒m<n∨m≡n p) refl q (m≤n⇒m<n∨m≡n q) refl
    where
        resurf-corr-cases
            : {n' : ℕ}
            → (r : NFRestr (suc n'))
            → {m : ℕ}
            → (p : m < suc n')
            → (p₀ : m < n' ⊎ m ≡ n')
            → (p₁ : m<1+n⇒m<n∨m≡n p ≡ p₀)
            → (q : suc m ≤ suc n')
            → (q₀ : suc m < suc n' ⊎ suc m ≡ suc n')
            → (q₁ : q₀ ≡ m≤n⇒m<n∨m≡n q)
            → just (NFSToℕ (resurface r p)) ≡ NFRestrToℕ {suc m} (trim' r q)
        
        resurf-corr-cases {n'@(suc n'')} r@(newNF r') {m} p (inj₁ m<n') 
            p₁ q (inj₁ 1+m<n) q₁ = 
            begin 
                just (NFSToℕ (resurface r p))
            ≡⟨⟩
                (just ∘ NFSToℕ) (resurface-cases r (m<1+n⇒m<n∨m≡n p))
            ≡⟨ cong ((just ∘ NFSToℕ) ∘ (resurface-cases r)) p₁ ⟩
                (just ∘ NFSToℕ) (resurface-cases r (inj₁ m<n'))
            ≡⟨⟩
                (just ∘ NFSToℕ ∘ earlier-new) (resurface r' m<n')
            ≡⟨⟩ -- Definition NFSToℕ on `earlier-new`.
                (just ∘ NFSToℕ) (resurface r' m<n')
            ≡⟨ resurface-correctness {n'} r' {m} m<n' m<n' ⟩
               NFRestrToℕ {suc m} (trim' r' m<n' ) 
            ≡⟨⟩ -- Definition `trim'`.
               NFRestrToℕ {suc m} (trim'-cases r' (m≤n⇒m<n∨m≡n m<n') ) 
            ≡⟨ cong NFRestrToℕ $ lemma (m≤n⇒m<n∨m≡n m<n') refl ⟩
               NFRestrToℕ (trim r q') 
            ≡⟨⟩
                NFRestrToℕ (trim'-cases r (inj₁ q'))
            ≡⟨ cong (λ x → NFRestrToℕ (trim'-cases r x )) q₁ ⟩
                NFRestrToℕ (trim'-cases r (m≤n⇒m<n∨m≡n q))
            ≡⟨⟩
               NFRestrToℕ (trim' r q) 
            ∎
            where
                q' : suc m < suc n'
                q' = 1+m<n

                -- The next two sublemmas tell that,
                -- if given a witness of one of the two options of m<n ⊎ m≡n,
                -- then m<1+n⇒m<n∨m≡n always outputs that witness.
                sublemma-<
                    : (w : suc m < n')
                    → (m<1+n⇒m<n∨m≡n q') ≡ inj₁ w
                sublemma-< w with m<1+n⇒m<n∨m≡n q'
                ... | inj₁ w' = cong inj₁ (≤-irrelevant w' w)
                ... | inj₂ refl = ⊥-elim $ n≮n n' w
                sublemma-≡
                    : (w : suc m ≡ n')
                    → (m<1+n⇒m<n∨m≡n q') ≡ inj₂ w
                sublemma-≡ refl with m<1+n⇒m<n∨m≡n q'
                ... | inj₁ m<n' = ⊥-elim $ n≮n n' m<n'
                ... | inj₂ refl = refl

                lemma 
                    : (z₀ : suc m < n' ⊎ suc m ≡ n') 
                    → (z₁ : (m≤n⇒m<n∨m≡n m<n') ≡ z₀) 
                    → trim'-cases r' (m≤n⇒m<n∨m≡n m<n') ≡ trim r q'
                lemma (inj₁ 1+m<n') z₁ = 
                    begin 
                        trim'-cases r' (m≤n⇒m<n∨m≡n m<n') 
                    ≡⟨ cong (trim'-cases r') z₁ ⟩
                        trim'-cases r' (inj₁ 1+m<n')
                    ≡⟨⟩
                        trim r' 1+m<n'
                    ≡⟨⟩
                        trim-cases (newNF r') (inj₁ 1+m<n')
                    ≡⟨ cong (trim-cases (newNF r')) $ sym $ sublemma-< 1+m<n' ⟩
                        trim-cases (newNF r') (m<1+n⇒m<n∨m≡n q')
                    ≡⟨⟩
                        trim (newNF r') q'
                    ≡⟨⟩
                        trim r q'
                    ∎
                    
                lemma (inj₂ 1+m≡n'@refl) z₁ =
                    begin 
                        trim'-cases r' (m≤n⇒m<n∨m≡n m<n') 
                    ≡⟨ cong (trim'-cases r') z₁ ⟩
                        trim'-cases r' (inj₂ 1+m≡n')
                    ≡⟨⟩
                        r'
                    ≡⟨⟩
                        trim-cases (newNF r') (inj₂ 1+m≡n')
                    ≡⟨ cong (trim-cases (newNF r')) $ sym $ sublemma-≡ 1+m≡n' ⟩
                        trim-cases (newNF r') (m<1+n⇒m<n∨m≡n q')
                    ≡⟨⟩
                        trim (newNF r') q'
                    ≡⟨⟩
                        trim r q'
                    ∎
        -- Same as previous case but with `oldNF r' c` i.o. `newNF r'`
        -- and `earlier-old` i.o. `earlier-new`.
        resurf-corr-cases {n'@(suc n'')} r@(oldNF r' c) {m} p (inj₁ m<n') 
            p₁ q (inj₁ 1+m<n) q₁ =
            begin 
                just (NFSToℕ (resurface r p))
            ≡⟨⟩
                (just ∘ NFSToℕ) (resurface-cases r (m<1+n⇒m<n∨m≡n p))
            ≡⟨ cong ((just ∘ NFSToℕ) ∘ (resurface-cases r)) p₁ ⟩
                (just ∘ NFSToℕ) (resurface-cases r (inj₁ m<n'))
            ≡⟨⟩
                (just ∘ NFSToℕ) (earlier-old {c = c} (resurface r' m<n'))
            ≡⟨⟩ -- Definition NFSToℕ on `earlier-old`.
                (just ∘ NFSToℕ) (resurface r' m<n')
            ≡⟨ resurface-correctness {n'} r' {m} m<n' m<n' ⟩
               NFRestrToℕ {suc m} (trim' r' m<n' ) 
            ≡⟨⟩ -- Definition `trim'`.
               NFRestrToℕ {suc m} (trim'-cases r' (m≤n⇒m<n∨m≡n m<n') ) 
            ≡⟨ cong NFRestrToℕ $ lemma (m≤n⇒m<n∨m≡n m<n') refl ⟩
               NFRestrToℕ (trim r q') 
            ≡⟨⟩
                NFRestrToℕ (trim'-cases r (inj₁ q'))
            ≡⟨ cong (λ x → NFRestrToℕ (trim'-cases r x )) q₁ ⟩
                NFRestrToℕ (trim'-cases r (m≤n⇒m<n∨m≡n q))
            ≡⟨⟩
               NFRestrToℕ (trim' r q) 
            ∎
            where
                q' : suc m < suc n'
                q' = 1+m<n

                -- The next two sublemmas tell that,
                -- if given a witness of one of the two options of m<n ⊎ m≡n,
                -- then m<1+n⇒m<n∨m≡n always outputs that witness.
                sublemma-<
                    : (w : suc m < n')
                    → (m<1+n⇒m<n∨m≡n q') ≡ inj₁ w
                sublemma-< w with m<1+n⇒m<n∨m≡n q'
                ... | inj₁ w' = cong inj₁ (≤-irrelevant w' w)
                ... | inj₂ refl = ⊥-elim $ n≮n n' w
                sublemma-≡
                    : (w : suc m ≡ n')
                    → (m<1+n⇒m<n∨m≡n q') ≡ inj₂ w
                sublemma-≡ refl with m<1+n⇒m<n∨m≡n q'
                ... | inj₁ m<n' = ⊥-elim $ n≮n n' m<n'
                ... | inj₂ refl = refl

                lemma 
                    : (z₀ : suc m < n' ⊎ suc m ≡ n') 
                    → (z₁ : (m≤n⇒m<n∨m≡n m<n') ≡ z₀) 
                    → trim'-cases r' (m≤n⇒m<n∨m≡n m<n') ≡ trim r q'
                lemma (inj₁ 1+m<n') z₁ = 
                    begin 
                        trim'-cases r' (m≤n⇒m<n∨m≡n m<n') 
                    ≡⟨ cong (trim'-cases r') z₁ ⟩
                        trim'-cases r' (inj₁ 1+m<n')
                    ≡⟨⟩
                        trim r' 1+m<n'
                    ≡⟨⟩
                        trim-cases (oldNF r' c) (inj₁ 1+m<n')
                    ≡⟨ cong (trim-cases (oldNF r' c)) $ sym $ sublemma-< 1+m<n' ⟩
                        trim-cases (oldNF r' c) (m<1+n⇒m<n∨m≡n q')
                    ≡⟨⟩
                        trim (oldNF r' c) q'
                    ≡⟨⟩
                        trim r q'
                    ∎
                    
                lemma (inj₂ 1+m≡n'@refl) z₁ =
                    begin 
                        trim'-cases r' (m≤n⇒m<n∨m≡n m<n') 
                    ≡⟨ cong (trim'-cases r') z₁ ⟩
                        trim'-cases r' (inj₂ 1+m≡n')
                    ≡⟨⟩
                        r'
                    ≡⟨⟩
                        trim-cases (oldNF r' c) (inj₂ 1+m≡n')
                    ≡⟨ cong (trim-cases (oldNF r' c)) $ sym $ sublemma-≡ 1+m≡n' ⟩
                        trim-cases (oldNF r' c) (m<1+n⇒m<n∨m≡n q')
                    ≡⟨⟩
                        trim (oldNF r' c) q'
                    ≡⟨⟩
                        trim r q'
                    ∎
            
        resurf-corr-cases {n'} r {m} p (inj₂ refl) p₁ q (inj₁ 1+m<n) q₁ = 
            -- We have suc n' ≡ suc m < n ≡ suc n'. A contradiction.
            ⊥-elim $ n≮n (suc n') 1+m<n

        resurf-corr-cases {n'} r {n'} p (inj₁ m<n') p₁ q (inj₂ refl) q₁ =
            -- We have n' ≡ m < n'. A contradiction.
            ⊥-elim $ n≮n n' m<n'

        resurf-corr-cases {n'} r@(newNF r') {n'} p (inj₂ refl) p₁ q 
                          (inj₂ refl) q₁ = 
            begin 
                just (NFSToℕ (resurface r p))
            ≡⟨⟩
                (just ∘ NFSToℕ) (resurface-cases r (m<1+n⇒m<n∨m≡n p))
            ≡⟨ cong ((just ∘ NFSToℕ) ∘ (resurface-cases r)) p₁ ⟩
                (just ∘ NFSToℕ) (resurface-cases r (inj₂ refl))
            ≡⟨⟩
                (just ∘ NFSToℕ) (resurface-cases (newNF r') (inj₂ refl))
            ≡⟨⟩
                just (NFSToℕ {suc n'} (here {n'} {r'} ))
            ≡⟨⟩
                just n' 
            ≡⟨⟩
                NFRestrToℕ r
            ≡⟨⟩
                NFRestrToℕ (trim'-cases r (inj₂ refl))
            ≡⟨ cong (λ x → NFRestrToℕ (trim'-cases r x)) q₁ ⟩
                NFRestrToℕ (trim'-cases r (m≤n⇒m<n∨m≡n q))
            ≡⟨⟩
                NFRestrToℕ (trim' r q)
            ∎
        -- Symmetric with previous case up 
        -- to changing `newNF r'` to `oldNF r' c`.
        resurf-corr-cases {n'} r@(oldNF r' c) {n'} p (inj₂ refl) p₁ q 
                          (inj₂ refl) q₁ =
            begin 
                just (NFSToℕ (resurface r p))
            ≡⟨⟩
                (just ∘ NFSToℕ) (resurface-cases r (m<1+n⇒m<n∨m≡n p))
            ≡⟨ cong ((just ∘ NFSToℕ) ∘ (resurface-cases r)) p₁ ⟩
                (just ∘ NFSToℕ) (resurface-cases r (inj₂ refl))
            ≡⟨⟩
                (just ∘ NFSToℕ) (resurface-cases (oldNF r' c) (inj₂ refl))
            ≡⟨⟩
                just (NFSToℕ {suc n'} (earlier-old {n'} {r'} {c} c))
            ≡⟨⟩
                just (NFSToℕ {n'} {r'} c)
            ≡⟨⟩
                NFRestrToℕ r
            ≡⟨⟩
                NFRestrToℕ (trim'-cases r (inj₂ refl))
            ≡⟨ cong (λ x → NFRestrToℕ (trim'-cases r x)) q₁ ⟩
                NFRestrToℕ (trim'-cases r (m≤n⇒m<n∨m≡n q))
            ≡⟨⟩
                NFRestrToℕ (trim' r q)
            ∎
        
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
