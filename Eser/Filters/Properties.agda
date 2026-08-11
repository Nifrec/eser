-- Module      : Eser.Filters.Properties
-- Description : Properties of and functions on definitions in Filter.Base.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)
open import Data.Nat.Properties using 
    (m<1+n⇒m<n∨m≡n 
    ; n<1+n 
    ; <-irrefl 
    ; m≤n⇒m<n∨m≡n
    ; <-trans
    ; n≮n
    ; <-irrelevant
    ; suc-injective
    ; ≤-refl
    ; ≤-trans
    ; n≤1+n
    )

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_ ; restIsProofIrrel ; n<1+n-lemma 
    ; doubleSubst
    ; m<1+n⇒m<n∨m≡n-when-≡
    ; m<1+n⇒m<n∨m≡n-when-<
    )
open import Data.Maybe

open import Eser.Filters.Base

module Eser.Filters.Properties where

--------------------------------------------------------------------------------
-- Basic properties of NFRestr
--------------------------------------------------------------------------------
empty-is-unique-zero
    : (r : NFRestr zero)
    → r ≡ empty
empty-is-unique-zero empty = refl

-- The only possible equivalence class for 0 is 0 itself.
empty-has-one-choice
    : (c : Choices empty)
    → c ≡ here {0} {empty}
empty-has-one-choice here = refl

lemma-NFRestr-subst
    : {a b : ℕ}
    → (r : NFRestr a)
    → (p p' : a ≡ b)
    → subst NFRestr p r ≡ subst NFRestr p' r
lemma-NFRestr-subst r refl refl = refl

-- The normal forms of a NFRestr n enjoy decidable equality,
-- since they are defined as a rather simple inductive type,
-- and are equal iff they are syntactically equal.
_≡?_ : {n : ℕ} → {r : NFRestr n} → DecidableEquality (NFS r)
here ≡? here =  true because ofʸ refl
here ≡? earlier-new c' = false because ofⁿ λ { () }
earlier-new c ≡? here = false because ofⁿ λ { () }
earlier-new c ≡? earlier-new c' with c ≡? c'
... | (yes c≡c') = true because ofʸ (cong earlier-new c≡c')
... | (no c≢c') 
    = false because ofⁿ λ { eq → c≢c' $ earlier-new-injective eq }
    where
        earlier-new-injective 
            : {n : ℕ} 
            → {r : NFRestr n} 
            → {c c' : NFS r}
            → earlier-new c ≡ earlier-new c'
            → c ≡ c'
        earlier-new-injective refl = refl
_≡?_ {suc n} {oldNF r k} (earlier-old c) (earlier-old c') with c ≡? c'
... | (yes c≡c') = true because ofʸ (cong earlier-old c≡c')
... | (no c≢c') 
    = false because ofⁿ 
        λ { eq → c≢c' $ earlier-old-injective {n} {r} {c}{c'}{k} eq }
    where
        earlier-old-injective 
            : {n : ℕ} 
            → {r : NFRestr n} 
            → {c c' k : NFS r}
            → earlier-old {n} {r} {k} c ≡ earlier-old {n} {r} {k} c'
            → c ≡ c'
        earlier-old-injective refl = refl

--------------------------------------------------------------------------------
-- Properties of NFSToℕ
--------------------------------------------------------------------------------
NFSToℕ-earlier-smaller-than-here
    : {n : ℕ}
    → (r : NFRestr n)
    → (c : NFS r)
    → NFSToℕ {suc n} {newNF r} (earlier-new c) < NFSToℕ {suc n} {newNF r} here
-- This works because 
--      NFSToℕ {suc n} {newNF r} (earlier-new c) 
--    ≗ NFSToℕ {n} {r} c 
--    < n 
--    ≗ NFSToℕ {suc n} {newNF r} here
NFSToℕ-earlier-smaller-than-here r c = NFSToℕ-< c
    
NFSToℕ-injective
    : {n : ℕ}
    → {r : NFRestr n}
    → (c c' : NFS r)
    → NFSToℕ c ≡ NFSToℕ c'
    → c ≡ c'
NFSToℕ-injective {n} {newNF r} here here refl = refl
NFSToℕ-injective {n} {newNF r} here (earlier-new c') eq-in-ℕ = 
    ⊥-elim $ n≮n (NFSToℕ c')
        (subst (λ x → NFSToℕ c' < x) eq-in-ℕ
               (NFSToℕ-earlier-smaller-than-here r c'))
NFSToℕ-injective {n} {newNF r} (earlier-new c) here eq-in-ℕ =
    ⊥-elim $ n≮n (NFSToℕ c)
        (subst (λ x → NFSToℕ c < x) (sym eq-in-ℕ)
               (NFSToℕ-earlier-smaller-than-here r c))
NFSToℕ-injective {n} {newNF r} (earlier-new c) (earlier-new c') eq-in-ℕ = 
    cong earlier-new $ NFSToℕ-injective c c' eq-in-ℕ
NFSToℕ-injective {n} {oldNF r x} (earlier-old c) (earlier-old c') eq-in-ℕ =
    cong earlier-old $ NFSToℕ-injective c c' eq-in-ℕ

choiceToℕ-injective
    : {n : ℕ}
    → {r : NFRestr n}
    → (c c' : Choices r)
    → choiceToℕ c ≡ choiceToℕ c'
    → c ≡ c'
choiceToℕ-injective {n} {r} c c' eq = NFSToℕ-injective c c' eq
--------------------------------------------------------------------------------
-- Properties of the _⋖_ relation.
--------------------------------------------------------------------------------

⋖-cases 
    : {n : ℕ} 
    → {r : NFRestr n} 
    → {s : NFRestr (ℕ.suc n)}
    → r ⋖ s
    → (s ≡ newNF r) ⊎ Σ[ c ∈ NFS r ](s ≡ oldNF r c)
⋖-cases {n} {r} {s} (⋖-newNF r) = inj₁ refl
⋖-cases {n} {r} {s} (⋖-oldNF r c) = inj₂ (c , refl)

⋖-irrel 
    : {n : ℕ} 
    → (r : NFRestr n) 
    → (s : NFRestr (ℕ.suc n))
    → Relation.Nullary.Irrelevant (r ⋖ s )
⋖-irrel {n} r (newNF s) (⋖-newNF r) (⋖-newNF r) = refl
⋖-irrel {n} r (oldNF r c) (⋖-oldNF r x) (⋖-oldNF r c) = refl

⋖-left-unique
    : {n : ℕ} 
    → {r r' : NFRestr n} 
    → {s : NFRestr (ℕ.suc n)}
    → r ⋖ s
    → r' ⋖ s
    → r ≡ r'
⋖-left-unique {n} {r} {r'} {s} (⋖-newNF r) (⋖-newNF r) = refl
⋖-left-unique {n} {r} {r'} {s} (⋖-oldNF r c) (⋖-oldNF r c) = refl

⋖-left-corollary-newNF
    : {n : ℕ} 
    → {r r' : NFRestr n} 
    → {s s' : NFRestr (ℕ.suc n)}
    → r ⋖ s
    → s ≡ s'
    → s' ≡ newNF r'
    → r ≡ r'
⋖-left-corollary-newNF {n} {r} {r'} {s} {s'} r⋖s refl refl = 
    ⋖-left-unique r⋖s (⋖-newNF r')
    
⋖-left-corollary-oldNF
    : {n : ℕ} 
    → {r r' : NFRestr n} 
    → {s s' : NFRestr (ℕ.suc n)}
    → r ⋖ s
    → s ≡ s'
    → (c : NFS r')
    → s' ≡ oldNF r' c
    → r ≡ r'
⋖-left-corollary-oldNF {n} {r} {r'} {s} {s'} r⋖s refl c refl = 
    ⋖-left-unique r⋖s (⋖-oldNF r' c)

lemma-⋖-subst
    : {a b : ℕ}
    → (v : a ≡ b)
    → (w : suc a ≡ suc b)
    → {r : NFRestr a}
    → {s : NFRestr (suc a)}
    → r ⋖ s
    → (subst NFRestr v r) ⋖ (subst NFRestr w s)
lemma-⋖-subst refl refl r⋖s = r⋖s

lemma-⋖+-not-smaller-idx
    : {n m : ℕ}
    → {r : NFRestr n}
    → {s : NFRestr m}
    → m ≤ n
    → r ⋖+ s
    → ⊥
lemma-⋖+-not-smaller-idx {n} {suc n} {r} {newNF r} m≤n (⋖+-onestep (⋖-newNF r)) 
    = n≮n n m≤n
lemma-⋖+-not-smaller-idx {n} {suc n} {r} {oldNF r c} m≤n (⋖+-onestep (⋖-oldNF r c)) 
    = n≮n n m≤n
lemma-⋖+-not-smaller-idx {suc n} {suc m} {r} {newNF s} 
    (s≤s m≤n) (⋖+-multistep-newNF p) = 
    lemma-⋖+-not-smaller-idx (≤-trans m≤n (n≤1+n n)) p
lemma-⋖+-not-smaller-idx {suc n} {suc m} {r} {oldNF s c} 
    (s≤s m≤n ) (⋖+-multistep-oldNF c p) =
    lemma-⋖+-not-smaller-idx (≤-trans m≤n (n≤1+n n)) p

-- If r ⋖+ s but r : NFRestr n and s : NFRestr (suc n)
-- then it must be that r ⋖ s directly as well.
lemma-⋖+-to-⋖
    : {n : ℕ}
    → {r : NFRestr n}
    → {s : NFRestr (suc n)}
    → r ⋖+ s
    → r ⋖ s
lemma-⋖+-to-⋖ {n} {r} {s} (⋖+-onestep r⋖s) = r⋖s
lemma-⋖+-to-⋖ {n} {r} {newNF s} (⋖+-multistep-newNF r⋖+s) =
    ⊥-elim $ lemma-⋖+-not-smaller-idx (≤-refl {n}) r⋖+s 
lemma-⋖+-to-⋖ {n} {r} {oldNF s c} (⋖+-multistep-oldNF c r⋖+s) =
    ⊥-elim $ lemma-⋖+-not-smaller-idx (≤-refl {n}) r⋖+s 

--------------------------------------------------------------------------------
-- A NFRestr can be trimmed to a sub-NFRestr.
--------------------------------------------------------------------------------
-- Contents:
-- 1. Definition of trim.
-- 2. correctness proof of trim.
-- 3. Variant of `trim` with m≤n i.o. m<n.
-- 4. getLastChoice.
-- 5. ... and many lemmas about these things ...
 
-- Trim a NFRestr n to a NFRestr m by simply forgetting the last few choices,
-- given that m < n.
trim
    : {n : ℕ}
    → (r : NFRestr n)
    → {m : ℕ}
    → m < n
    → NFRestr m

trim-cases
    : {n' : ℕ}
    → (r : NFRestr (suc n'))
    → {m : ℕ}
    → (m < n') ⊎ (m ≡ n')
    → NFRestr m

trim {suc n'} r {m} m<n = 
    trim-cases {n'} r {m} (m<1+n⇒m<n∨m≡n m<n)

trim-cases {n'} (newNF r') {m} (inj₁ m<n') = 
    trim {n'} r' {m} m<n'
trim-cases {n'} (oldNF r' c) {m} (inj₁ m<n') =
    trim {n'} r' {m} m<n'
trim-cases {n'} (newNF r') {n'} (inj₂ refl) = r'
trim-cases {n'} (oldNF r' c) {n'} (inj₂ refl) = r'

-- Correctness: the trimmed version is actually a sub-NFRestr of the input.
-- That it has the right length already holds at type level.
trim-correctness
    : {n : ℕ}
    → (r : NFRestr n)
    → {m : ℕ}
    → (m<n : m < n)
    → (trim r m<n) ⋖+ r
trim-correctness {suc n'} r {m} m<n = 
    cases {n'} r {m} m<n (m<1+n⇒m<n∨m≡n m<n) refl
    module TrimNFRestrCorrectness where
        cases
            : {n' : ℕ}
            → (r : NFRestr (suc n'))
            → {m : ℕ}
            → (p : m < suc n')
            → (p₀ : (m < n') ⊎ (m ≡ n'))
            → (p₁ : m<1+n⇒m<n∨m≡n p ≡ p₀)
            → (trim r p) ⋖+ r
        cases {n'} (newNF r') {m} m<n (inj₁ m<n') p₁ = 
            subst (_⋖+ newNF r') (sym H) (⋖+-multistep-newNF IH)
            where
                IH : trim r' m<n' ⋖+ r'
                IH = trim-correctness r' m<n'
                H : trim (newNF r') m<n ≡ trim r' m<n'
                H =
                    begin 
                        trim {suc n'} (newNF r') m<n   
                    ≡⟨⟩
                        trim-cases (newNF r') (m<1+n⇒m<n∨m≡n m<n)
                    ≡⟨ cong (λ x → trim-cases (newNF r') x) p₁ ⟩
                        trim-cases (newNF r') (inj₁ m<n')
                    ≡⟨⟩
                        trim r' m<n'
                    ∎
        cases {n'} (oldNF r' c) {m} m<n (inj₁ m<n') p₁ =
            subst (_⋖+ oldNF r' c) (sym H) (⋖+-multistep-oldNF c IH)
            where
                IH : trim r' m<n' ⋖+ r'
                IH = trim-correctness r' m<n'
                H : trim (oldNF r' c) m<n ≡ trim r' m<n'
                H =
                    begin 
                        trim {suc n'} (oldNF r' c) m<n   
                    ≡⟨⟩
                        trim-cases (oldNF r' c) (m<1+n⇒m<n∨m≡n m<n)
                    ≡⟨ cong (λ x → trim-cases (oldNF r' c) x) p₁ ⟩
                        trim-cases (oldNF r' c) (inj₁ m<n')
                    ≡⟨⟩
                        trim r' m<n'
                    ∎
        -- Next two cases use the same proof,
        -- except for changing `newNF r'` by `oldNF r c`.
        cases {n'} (newNF r') {n'} m<n (inj₂ refl) p₁ = 
            subst ( _⋖+ newNF r') (sym H) (⋖+-onestep (⋖-newNF r'))
            where
                H : trim (newNF r') m<n ≡ r'
                H =
                    begin 
                        trim {suc n'} (newNF r') {n'} m<n   
                    ≡⟨⟩
                        trim-cases {n'} (newNF r') {n'} 
                                           (m<1+n⇒m<n∨m≡n m<n)
                    ≡⟨ cong (λ x → trim-cases {n'} (newNF r') x) 
                             p₁ ⟩
                        trim-cases {n'} (newNF r') {n'} (inj₂ refl)
                    ≡⟨⟩
                        r'
                    ∎
        cases {n'} (oldNF r' c) {n'} m<n (inj₂ refl) p₁ =
            subst ( _⋖+ oldNF r' c) (sym H) (⋖+-onestep (⋖-oldNF r' c))
            where
                H : trim (oldNF r' c) m<n ≡ r'
                H =
                    begin 
                        trim {suc n'} (oldNF r' c) {n'} m<n   
                    ≡⟨⟩
                        trim-cases {n'} (oldNF r' c) {n'} 
                                           (m<1+n⇒m<n∨m≡n m<n)
                    ≡⟨ cong (λ x → trim-cases {n'} (oldNF r' c) x) 
                             p₁ ⟩
                        trim-cases {n'} (oldNF r' c) {n'} (inj₂ refl)
                    ≡⟨⟩
                        r'
                    ∎

-- Variant of `trim` that also allows the option to trimming to m ≡ n,
-- in which case it just acts as the identity.
trim' 
    : {n : ℕ}
    → (r : NFRestr n)
    → {m : ℕ}
    → m ≤ n
    → NFRestr m
trim'-cases 
    : {n : ℕ}
    → (r : NFRestr n)
    → {m : ℕ}
    → m < n ⊎ m ≡ n
    → NFRestr m

trim' r m≤n = trim'-cases r (m≤n⇒m<n∨m≡n m≤n)
trim'-cases r (inj₁ m<n) = trim r m<n
trim'-cases {n} r {n} (inj₂ refl) = r

getLastChoice
    : {n' : ℕ}
    → (r : NFRestr (suc n'))
    → Σ[ c ∈ Choices (trim r (n<1+n n')) ] r ≡ addChoice (trim r (n<1+n n')) c
getLastChoice {n'} (newNF r') = ans
    where
        H : trim {suc n'} (newNF r') {n'} (n<1+n n') ≡ r'
        H =
            begin 
                trim (newNF r') (n<1+n n')
            ≡⟨⟩
                trim-cases (newNF r') (m<1+n⇒m<n∨m≡n (n<1+n n'))
            ≡⟨ cong (trim-cases {n'} (newNF r') {n'}) (n<1+n-lemma n') ⟩
                trim-cases (newNF r') (inj₂ refl)
            ≡⟨⟩
                r'
            ∎

        K : newNF r' ≡ addChoice r' here
        K = refl

        pre-ans : Σ[ c ∈ Choices r' ] newNF r' ≡ addChoice r' c
        pre-ans = (here , K)

        P : NFRestr n' → Set
        P x = Σ[ c ∈ Choices x ] newNF r' ≡ addChoice x c
        
        ans : P (trim (newNF r') (n<1+n n'))
        ans = subst P (sym H) pre-ans 

-- Same proof as other case, except all `newNF r'` are replaced by `oldNF r' c`.
getLastChoice {n'} (oldNF r' c) = ans
    where
        H : trim {suc n'} (oldNF r' c) {n'} (n<1+n n') ≡ r'
        H =
            begin 
                trim (oldNF r' c) (n<1+n n')
            ≡⟨⟩
                trim-cases (oldNF r' c) (m<1+n⇒m<n∨m≡n (n<1+n n'))
            ≡⟨ cong (trim-cases {n'} (oldNF r' c) {n'}) (n<1+n-lemma n') ⟩
                trim-cases (oldNF r' c) (inj₂ refl)
            ≡⟨⟩
                r'
            ∎

        K : oldNF r' c ≡ addChoice r' (earlier-new c)
        K = refl

        pre-ans : Σ[ k ∈ Choices r' ] oldNF r' c ≡ addChoice r' k
        pre-ans = (earlier-new c , K)

        P : NFRestr n' → Set
        P x = Σ[ k ∈ Choices x ] oldNF r' c ≡ addChoice x k
        
        ans : P (trim (oldNF r' c) (n<1+n n'))
        ans = subst P (sym H) pre-ans 

lemma-trim-addChoice-inj₁
    : (n m : ℕ)
    → (r : NFRestr n)
    → (c : Choices r)
    → (p : m < n)
    → trim-cases (addChoice r c) (inj₁ p) ≡ trim r p
lemma-trim-addChoice-inj₁ n m r here p = refl
lemma-trim-addChoice-inj₁ n m r (earlier-new c) p = refl

lemma-trim-addChoice-inj₂
    : (n : ℕ)
    → (r : NFRestr n)
    → (c : Choices r)
    → trim-cases (addChoice r c) (inj₂ refl) ≡ r
lemma-trim-addChoice-inj₂ n r here = refl
lemma-trim-addChoice-inj₂ n r (earlier-new c) = refl

-- Trim will always trim away the `addChoice` from 
-- a NFRestr of the form addChoice r c,
-- but this might be the only thing it trims away.
lemma-trim-addChoice
    : (n m : ℕ)
    → (r : NFRestr n)
    → (c : Choices r)
    → (p : m < suc n)
    → (q : m ≤ n)
    → trim (addChoice r c) p ≡ trim' r q
lemma-trim-addChoice n m r c p q =
    lemma-trim-addChoice-cases n m r c p (m<1+n⇒m<n∨m≡n p) refl q (m≤n⇒m<n∨m≡n q) refl
    where
        lemma-trim-addChoice-cases
            : (n m : ℕ)
            → (r : NFRestr n)
            → (c : Choices r)
            → (p : m < suc n)
            → (p₀ : m < n ⊎ m ≡ n)
            → (p₁ : (m<1+n⇒m<n∨m≡n p) ≡ p₀)
            → (q : m ≤ n)
            → (q₀ : m < n ⊎ m ≡ n)
            → (q₁ : (m≤n⇒m<n∨m≡n q) ≡ q₀)
            → trim (addChoice r c) p ≡ trim' r q
        lemma-trim-addChoice-cases n n r c p (inj₁ m<n) p₁ q (inj₂ refl) q₁ =
            ⊥-elim $ n≮n n m<n
        lemma-trim-addChoice-cases n n r c p (inj₂ refl) p₁ q (inj₁ m<n) q₁ = 
            ⊥-elim $ n≮n n m<n
        lemma-trim-addChoice-cases n m r c p (inj₁ m<n) p₁ q (inj₁ m<<n) q₁ = 
            begin 
                trim (addChoice r c) p
            ≡⟨⟩
                trim-cases (addChoice r c) (m<1+n⇒m<n∨m≡n p)
            ≡⟨ cong (trim-cases (addChoice r c)) p₁ ⟩
                trim-cases (addChoice r c) (inj₁ m<n)
            ≡⟨ lemma-trim-addChoice-inj₁ n m r c m<n ⟩
                trim r m<n
            ≡⟨ cong (trim r) (<-irrelevant m<n m<<n) ⟩
                trim r m<<n
            ≡⟨⟩
                trim'-cases r (inj₁ m<<n)
            ≡⟨ cong (trim'-cases r) (sym q₁) ⟩
                trim'-cases r (m≤n⇒m<n∨m≡n q)
            ≡⟨⟩
                trim' r q
            ∎
            
        lemma-trim-addChoice-cases n n r c p (inj₂ refl) p₁ q (inj₂ refl) q₁ =
            begin 
                trim (addChoice r c) p
            ≡⟨⟩
                trim-cases (addChoice r c) (m<1+n⇒m<n∨m≡n p)
            ≡⟨ cong (trim-cases (addChoice r c)) p₁ ⟩
                trim-cases (addChoice r c) (inj₂ refl)
            ≡⟨ lemma-trim-addChoice-inj₂ n r c ⟩
                r
            ≡⟨⟩
                trim'-cases r (inj₂ refl)
            ≡⟨ cong (trim'-cases r) (sym q₁) ⟩
                trim'-cases r (m≤n⇒m<n∨m≡n q)
            ≡⟨⟩
                trim' r q
            ∎

-- Trimming an Exence is the same as evaluating an Excence on a smaller input.
lemma-trim'-exence
    : (h : (n : ℕ) → NFRestr n)
    → (H : (n : ℕ) → h n ⋖ h (suc n))
    → (n m : ℕ)
    → (p : suc m ≤ n)
    → trim' (h n) p ≡ h (suc m)
lemma-trim'-exence h H n m p = 
    lemma-trim'-exence-cases h H n m p (m≤n⇒m<n∨m≡n p) refl
    where
        lemma-trim'-exence-cases 
            : (h : (n : ℕ) → NFRestr n)
            → (H : (n : ℕ) → h n ⋖ h (suc n))
            → (n m : ℕ)
            → (p : suc m ≤ n)
            → (p₀ : suc m < n ⊎ suc m ≡ n)
            → (p₁ : (m≤n⇒m<n∨m≡n p) ≡ p₀)
            → trim' (h n) p ≡ h (suc m)
        lemma-trim'-exence-cases h H n@(suc n') m p (inj₁ 1+m<n) p₁ = 
            begin 
                trim' (h n) p
            ≡⟨⟩
                trim'-cases (h n) (m≤n⇒m<n∨m≡n p)  
            ≡⟨ cong (trim'-cases (h n)) p₁ ⟩
                trim'-cases (h n) (inj₁ 1+m<n)
            ≡⟨⟩
                trim (h n) 1+m<n
            ≡⟨⟩
                trim (h (suc n')) 1+m<n
            ≡⟨ cong ( λ x → trim x 1+m<n)  c-prop ⟩
                trim (addChoice (h n') c) 1+m<n
            ≡⟨ lemma-trim-addChoice n' (suc m) (h n') c 1+m<n p' ⟩
                trim' (h n') p'
            ≡⟨ lemma-trim'-exence h H n' m p'  ⟩
                h (suc m)  
            ∎
            where
                p' : suc m ≤ n'
                p' = s≤s⁻¹ 1+m<n
                c : Choices (h n')
                c = proj₁ $ ⋖-to-addChoice (H n')
                c-prop : h (suc n') ≡ addChoice (h n') c
                c-prop = proj₂ $ ⋖-to-addChoice (H n')
            
        lemma-trim'-exence-cases h H n@(suc n') m p (inj₂ refl) p₁ =
            begin 
                trim' (h n) p
            ≡⟨⟩
                trim'-cases (h n) (m≤n⇒m<n∨m≡n p)  
            ≡⟨ cong (trim'-cases (h n)) p₁ ⟩
                trim'-cases (h n) (inj₂ refl)
            ≡⟨⟩
                h n
            ≡⟨⟩
                h (suc m)
            ∎

lemma-trim-⋖
    : {n m : ℕ}
    → (r : NFRestr n)
    → (p : m < n)
    → (q : suc m < n)
    → trim r p ⋖ trim r q
lemma-trim-⋖-cases
    : (n' m : ℕ)
    → (r : NFRestr (suc n'))
    → (r' : NFRestr n')
    → (c : Choices r')
    → r ≡ addChoice r' c
    → (p : m < suc n')
    → (q : suc m < suc n')
    → (v : suc m < n' ⊎ suc m ≡ n')
    → trim r p ⋖ trim r q
    
lemma-trim-⋖ {suc n'} {m} r@(newNF r') p q = 
    lemma-trim-⋖-cases n' m r r' here refl p q (m<1+n⇒m<n∨m≡n q)
lemma-trim-⋖ {suc n'} {m} r@(oldNF r' c) p q =
    lemma-trim-⋖-cases n' m r r' (earlier-new c) refl p q (m<1+n⇒m<n∨m≡n q)

lemma-trim-⋖-cases n' m r r' c K p q (inj₁ 1+m<n') 
    = doubleSubst _⋖_ (sym LHS) (sym RHS) rec
    where
        m<n' : m < n'
        m<n' = <-trans (n<1+n m) 1+m<n'

        LHS : trim r p ≡ trim r' m<n'
        LHS = 
            let p₁ :  m<1+n⇒m<n∨m≡n p ≡ inj₁ m<n'
                p₁ = m<1+n⇒m<n∨m≡n-when-< m n' p m<n'
            in
            begin 
                trim r p
            ≡⟨⟩
                trim-cases r (m<1+n⇒m<n∨m≡n p)
            ≡⟨ cong (trim-cases r) p₁ ⟩
                trim-cases r (inj₁ m<n')
            ≡⟨ cong (λ r → trim-cases r (inj₁ m<n')) K ⟩
                trim-cases (addChoice r' c) (inj₁ m<n')
            ≡⟨ lemma-trim-addChoice-inj₁ n' m r' c m<n' ⟩
                trim r' m<n'
            ∎
            
        -- Similar proof as LHS but with `suc m` instead of `m`.
        RHS : trim r q ≡ trim r' 1+m<n'
        RHS =
            let q₁ :  m<1+n⇒m<n∨m≡n q ≡ inj₁ 1+m<n'
                q₁ = m<1+n⇒m<n∨m≡n-when-< (suc m) n' q 1+m<n'
            in
            begin 
                trim r q
            ≡⟨⟩
                trim-cases r (m<1+n⇒m<n∨m≡n q)
            ≡⟨ cong (trim-cases r) q₁ ⟩
                trim-cases r (inj₁ 1+m<n')
            ≡⟨ cong (λ r → trim-cases r (inj₁ 1+m<n')) K ⟩
                trim-cases (addChoice r' c) (inj₁ 1+m<n')
            ≡⟨ lemma-trim-addChoice-inj₁ n' (suc m) r' c 1+m<n' ⟩
                trim r' 1+m<n'
            ∎

        -- We have r' : NFRestr n', 
        -- and n' is structurally smaller than (suc n'),
        -- so recurse on n' and r'.
        rec : trim r' m<n' ⋖ trim r' 1+m<n'
        rec = lemma-trim-⋖ {n'} {m} r' m<n' 1+m<n'

lemma-trim-⋖-cases n' m r r' c K p q (inj₂ 1+m≡n'@refl)
    = doubleSubst _⋖_ (sym LHS) (sym RHS) Z
    where
        m<n' : m < n'
        m<n' = n<1+n m -- That suc m ≗ n holds by reflexivity.

        -- #TWEAK: same proof as the LHS in the previous case,
        -- instance of copy-paste that might be refactorable.
        LHS : trim r p ≡ trim r' m<n'
        LHS =
            let p₁ :  m<1+n⇒m<n∨m≡n p ≡ inj₁ m<n'
                p₁ = m<1+n⇒m<n∨m≡n-when-< m n' p m<n'
            in
            begin 
                trim r p
            ≡⟨⟩
                trim-cases r (m<1+n⇒m<n∨m≡n p)
            ≡⟨ cong (trim-cases r) p₁ ⟩
                trim-cases r (inj₁ m<n')
            ≡⟨ cong (λ r → trim-cases r (inj₁ m<n')) K ⟩
                trim-cases (addChoice r' c) (inj₁ m<n')
            ≡⟨ lemma-trim-addChoice-inj₁ n' m r' c m<n' ⟩
                trim r' m<n'
            ∎

        RHS : trim r q ≡ r'
        RHS = 
            let q₁ :  m<1+n⇒m<n∨m≡n q ≡ inj₂ refl
                q₁ = m<1+n⇒m<n∨m≡n-when-≡ (suc m) n' q refl
            in
            begin 
                trim r q
            ≡⟨⟩
                trim-cases r (m<1+n⇒m<n∨m≡n q)
            ≡⟨ cong (trim-cases r) q₁ ⟩
                trim-cases r (inj₂ refl)
            ≡⟨ cong (λ r → trim-cases r (inj₂ refl)) K ⟩
                trim-cases (addChoice r' c) (inj₂ refl)
            ≡⟨ lemma-trim-addChoice-inj₂ n' r' c ⟩
                r'
            ∎

        Z : trim r' m<n' ⋖ r'
        Z = lemma-⋖+-to-⋖ $ trim-correctness r' m<n'

--------------------------------------------------------------------------------
-- Properties of getChoice
--------------------------------------------------------------------------------

lemma-getChoice-addChoice
    : {n : ℕ}
    → (r : NFRestr n)
    → (c : Choices r)
    → (p : r ⋖ addChoice r c)
    → getChoice r (addChoice r c) p ≡ c
lemma-getChoice-addChoice {n} r here (⋖-newNF r) = refl
lemma-getChoice-addChoice {n} r (earlier-new c) (⋖-oldNF r c) = refl

lemma-choiceToℕ∘getChoice
    : {n : ℕ}
    → (r r' : NFRestr n)
    → (s s' : NFRestr (ℕ.suc n))
    → (p : r ⋖ s)
    → (p' : r' ⋖ s')
    → r ≡ r'
    → s ≡ s'
    → choiceToℕ (getChoice r s p) ≡ choiceToℕ (getChoice r' s' p')
lemma-choiceToℕ∘getChoice r r s s p p' refl refl = 
    cong (λ p → choiceToℕ (getChoice r s p)) (⋖-irrel r s p p')

lemma-getChoice-subst
    : {n : ℕ}
    → (r r' : NFRestr n)
    → (s s' : NFRestr (ℕ.suc n))
    → (p : r ⋖ s)
    → (p' : r' ⋖ s')
    → (Hr : r' ≡ r)
    → s' ≡ s
    → getChoice r s p ≡ subst Choices Hr (getChoice r' s' p')
lemma-getChoice-subst {n} r r s s p p' refl refl = 
    cong (getChoice r s ) (⋖-irrel r s p p')

-- The abstraction over c instead of replacing
-- c by `proj₁ $ ⋖-to-addChoice (H n)` is primality done for readability.
lemma-⋖-addChoice-exence
    : {n : ℕ}
    → (h : (n : ℕ) → NFRestr n)
    → (H : (n : ℕ) → h n ⋖ h (suc n))
    → (c : Choices (h n))
    → c ≡ (proj₁ $ ⋖-to-addChoice (H n))
    → (addChoice (h n) c , ⋖-addChoice c) ≡ (h (suc n) , H n)
lemma-⋖-addChoice-exence {n} h H c refl = 
    restIsProofIrrel (⋖-irrel (h n)) (⋖-addChoice c) (H n) c-prop
    where
        c-prop : addChoice (h n) c ≡ h (suc n)
        c-prop = sym $ proj₂ $ ⋖-to-addChoice (H n)
        

lemma-getChoice-exence-alt
    : {n : ℕ}
    → (h : (n : ℕ) → NFRestr n)
    → (H : (n : ℕ) → h n ⋖ h (suc n))
    → (c : Choices (h n))
    → c ≡ (proj₁ $ ⋖-to-addChoice (H n))
    → c ≡ getChoice (h n) (h (suc n)) (H n)
lemma-getChoice-exence-alt {n} h H c refl = 
    begin
        c
    ≡⟨ sym $ lemma-getChoice-addChoice (h n) c (⋖-addChoice c) ⟩
        getChoice (h n) (addChoice (h n) c) (⋖-addChoice c)
    ≡⟨⟩
        (λ (x , y) → getChoice (h n) x y) 
        (addChoice (h n) c , ⋖-addChoice c)
    ≡⟨ cong (λ (x , y) → getChoice (h n) x y) 
        (lemma-⋖-addChoice-exence h H c refl)
    ⟩
        (λ (x , y) → getChoice (h n) x y) (h (suc n) , H n)
    ≡⟨⟩
        getChoice (h n) (h (suc n)) (H n)
    ∎

-- Same lemma as above, but without abstraction over c.
lemma-getChoice-exence
    : (n : ℕ)
    → (h : (n : ℕ) → NFRestr n)
    → (H : (n : ℕ) → h n ⋖ h (suc n))
    → (proj₁ $ ⋖-to-addChoice (H n)) ≡ getChoice (h n) (h (suc n)) (H n)
lemma-getChoice-exence n h H = lemma-getChoice-exence-alt h H c refl
    where
        c = proj₁ $ ⋖-to-addChoice (H n)
    
--------------------------------------------------------------------------------
-- Properties of NFRestrToℕ
--------------------------------------------------------------------------------
lemma-NFRestrToℕ-addChoice
    : {n : ℕ}
    → (r : NFRestr n)
    → (c : Choices r)
    → NFRestrToℕ (addChoice r c) ≡ just (choiceToℕ c)
lemma-NFRestrToℕ-addChoice {n} r here = refl
lemma-NFRestrToℕ-addChoice {n} (newNF r) (earlier-new c) = refl
lemma-NFRestrToℕ-addChoice {n} (oldNF r x) (earlier-new (earlier-old c)) = refl

