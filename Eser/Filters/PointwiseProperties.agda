-- Module      : Eser.Filters.PointwiseProperties
-- Description : Pointwise defined properties of Filters and NFRestrFams.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_ ; restIsProofIrrel ; pair-eq)

open import Eser.Filters.Base
open import Eser.Filters.Conversions.NFFunToExence
open import Eser.Filters.Properties

module Eser.Filters.PointwiseProperties where

--------------------------------------------------------------------------------
-- Predicates whether an NFFun satisfies a Filter/Reco
--------------------------------------------------------------------------------

Exence-sats : Filter → Exence → Set
Exence-sats F (h , H) = (n : ℕ) → F Allows (getChoiceFromExence (h , H) n) In h n

NFFun-sats : Filter → NFFun → Set
NFFun-sats F f' = Exence-sats F (restrict+ f')

-- All sub-restrictions of a restriction satisfy a filter.
data AllRestr-sat (F : Filter) : {n : ℕ} → NFRestr n → Set where
    allsat-empty : AllRestr-sat F empty
    allsat-newNF 
        : {n : ℕ} 
        → (r : NFRestr n) 
        → AllRestr-sat F r
        → F Allows here In r
        → AllRestr-sat F (newNF r)
    allsat-oldNF 
        : {n : ℕ} 
        → (r : NFRestr n) 
        → (c : NFS r)
        → AllRestr-sat F r
        → F Allows (earlier-new c) In r
        → AllRestr-sat F (oldNF r c)

-- Derived constructor that mutiplexes over the previous two constructors.
allsat-addChoice
    : {F : Filter}
    → {n : ℕ} 
    → (r : NFRestr n) 
    → (c : Choices r)
    → AllRestr-sat F r
    → F Allows c In r
    → AllRestr-sat F (addChoice r c)
allsat-addChoice {F} {n} r here sat allowed 
    = allsat-newNF r sat allowed
allsat-addChoice {F} {n} r (earlier-new c) sat allowed 
    = allsat-oldNF r c sat allowed


-- Alternative but logically equivalent definition of Exence-sat.
Exence-sats-alt : Filter → Exence → Set
Exence-sats-alt F (h , H) = (n : ℕ) → AllRestr-sat F (h n)

lemma-allrestr-sat-addchoice
    : {F : Filter}
    → {n : ℕ}
    → (r : NFRestr n)
    → (c : Choices r)
    → AllRestr-sat F (addChoice r c)
    → F Allows c In r
lemma-allrestr-sat-addchoice {F} {n} r here (allsat-newNF r sat x) = x
lemma-allrestr-sat-addchoice {F} {n} r 
                             (earlier-new c) (allsat-oldNF r c sat x) = x

Exence-sats-to-alt
    : {F : Filter}
    → {E : Exence}
    → Exence-sats F E
    → Exence-sats-alt F E
Exence-sats-to-alt {F} {h , H} sat zero = 
    subst (AllRestr-sat F) (sym $ empty-is-unique-zero (h 0)) allsat-empty
Exence-sats-to-alt {F} {h , H} sat (suc n) = 
    subst (AllRestr-sat F) (sym c-prop) ans'
    where
        IH : AllRestr-sat F (h n)
        IH = Exence-sats-to-alt sat n

        c : Choices (h n)
        c = proj₁ $ ⋖-to-addChoice (H n)
        c-prop : h (suc n) ≡ addChoice (h n) c
        c-prop = proj₂ $ ⋖-to-addChoice (H n)
        c-eq : getChoice (h n) (h (suc n)) (H n) ≡ c
        c-eq = sym $ lemma-getChoice-exence n h H
        c-allowed : F Allows c In (h n)
        c-allowed = subst (λ x → FilterAllows F (h n) x) c-eq (sat n)

        ans' : AllRestr-sat F (addChoice (h n) c)
        ans' = allsat-addChoice (h n) c IH c-allowed

Exence-sats-from-alt
    : {F : Filter}
    → {E : Exence}
    → Exence-sats-alt F E
    → Exence-sats F E
Exence-sats-from-alt {F} {(h , H)} sat n = ans
    where
        K₀ : AllRestr-sat F (h (suc n))
        K₀ = sat (suc n)
        c : Choices (h n)
        c = proj₁ $ ⋖-to-addChoice (H n)
        c-prop : h (suc n) ≡ addChoice (h n) c
        c-prop = proj₂ $ ⋖-to-addChoice (H n)
        K₁ : AllRestr-sat F (addChoice (h n) c)
        K₁ = subst (AllRestr-sat F) c-prop K₀
        eq : (addChoice (h n) c , ⋖-addChoice c) ≡ (h (suc n) , H n)
        eq = lemma-⋖-addChoice-exence h H c refl
        K₂ : c ≡ getChoice (h n) (h (suc n)) (H n)
        K₂ = lemma-getChoice-exence n h H
        c-allowed : F Allows c In (h n)
        c-allowed = lemma-allrestr-sat-addchoice (h n) c K₁
        ans : F Allows (getChoice (h n) (h (suc n)) (H n)) In (h n)
        ans = subst (λ x → F Allows x In (h n)) K₂ c-allowed

--------------------------------------------------------------------------------
-- Conversions preserve satisfiablity
--------------------------------------------------------------------------------
-- Let f' be an NFFun and E be an Exence and F be a Filter.
-- Then:
-- (1) f' satisfies F => (restrict+ f') satisfies F
-- (2) E  satisfies F => (combine E) satisfies F
--
-- (1) is trivial since the definition of the premise is exactly the conclusion.
-- (2) uses that restrict+ ∘ combine pointwise acts as the identity
--  (up to function extensionality).

theo-restrict+-presv-sat
    : {F : Filter}
    → (f' : NFFun)
    → NFFun-sats F f'
    → Exence-sats F (restrict+ f')
theo-restrict+-presv-sat {F} f' sat = sat

theo-combine-presv-sat
    : {F : Filter}
    → (E : Exence)
    → Exence-sats F E
    → NFFun-sats F (combine E)
theo-combine-presv-sat {F} (h , H) sat n = 
    subst (λ ((r , s)  , r⋖s) → F Allows getChoice r s r⋖s In r) eq (sat n)
    -- The goal unfolds to showing 
    -- Exence-sats F (restrict+ ∘ combine (h , H))
    -- i.e.
    -- (n : ℕ) → F Allows getChoice (h' n) (h' (suc n)) (H' n) In (h' n)    (G)
    -- where
    -- (h' , H') ≔ (restrict+ ∘ combine (h , H)).
    -- But the `restrict+ ∘ combine ≈ id` theorem gives that `h' n ≡ h n`
    -- and `h' (suc n) ≡ h (suc n)`, while `H' n` and `H n` are
    -- proof-irrelevant.
    -- So substitute those equalities in (G) and we are done.
    -- (Implementation detail: we first need to combine the equalities
    -- into equalities of tuples).
    where
        h' = proj₁ $ (restrict+ ∘ combine) (h , H)
        H' = proj₂ $ (restrict+ ∘ combine) (h , H)

        eq : _≡_ {A = ⋖-Pair n} ((h n , h (suc n)) , H n) 
                                ((h' n , h' (suc n)) , H' n)
        eq = exence-successor-tuples-eq h h' H H' refl n


--------------------------------------------------------------------------------
-- Satisfiable Filters
--------------------------------------------------------------------------------
-- A Filter is satisfiable that allow a complete sequence of choices
-- of normal forms for each n : ℕ.
--
-- We define a Filter to be 'Passable' if such a sequence exists.
--
-- The most interesting Filters are those that allow to locally "grow" a
-- normalisation function, by choosing recursively extensions
-- that satisfy the Filter. 
-- The Filter ought then to be nice and allow the growth to continue,
-- meaning some choice of extension is available if all previous choices
-- are allowed by the Filter. 'Passability' is not a sufficient strong
-- condition: it gives a series of default choices, but divering from those
-- defaults may still get the growth to get stuck in a partial normalisation
-- function with no allowed extension.
-- So we define the stronger notion of "DeadEndFree".

-- A filter is passable if there exists a sequence of choices
-- that the filter accepts at every point.
Passable : Filter → Set
Passable F = Σ[ E ∈ Exence ] Exence-sats F E

-- A filter is DeadEndFree if for any sequence of allowed choices
-- there always extists an allowed extension.
-- Diverging from those 'default' allowed extensions and choosing
-- other allowed extensions will never lead to an NFRestr 
-- without allowed further extensions.
DeadEndFree : Filter → Set
DeadEndFree F = 
    {n : ℕ} 
    → (r : NFRestr n) 
    → AllRestr-sat F r 
    → Σ[ c ∈ Choices r ] F Allows c In r

--------------------------------------------------------------------------------
-- Filter compatibility relation
--------------------------------------------------------------------------------
-- F ♥ G if for every sequence of normalisation function extensions
-- whose choices both F and G allow there exist an extension they also both
-- allow, i.e., F ♥ G is DeadEndFree.
--
-- ## Remark 1
-- _♥_ is symmetric, but not reflexive and not transitive.
-- F ♥ F is a nontrivial statement that F is DeadEndFree.
--
-- ## Remark 2
-- The following definition is wrong:
--      (F ♥ G) r = Σ[ c ∈ Choices r ] F r c ∧ G r c
-- This condition is too strong, because it requires F and G
-- to agree on some extension of any NFRestr r, even
-- NFRestr r containing earlier choices which neither F nor G accepts.
-- That is not needed to encode the intended 'there exists a normalisation
-- function F and G both accept'.

infixl 4 _⋀_ -- `And` in Cornelis. `and` (for `∧`) is on Bool.
_⋀_ : Filter → Filter → Filter
(F ⋀ G) {n} r c = F r c ∧ G r c

infixl 4 _♥_
_♥_ : (F G : Filter) → Set
_♥_ F G = DeadEndFree (F ⋀ G)

-- The only possible normal form of 0 is 0.
-- So any DeadEndFree Filter must allow this unique choice.
-- #TWEAK: function not used in the end.
lemma-DeadEndFree-firstchoice
    : {F : Filter}
    → DeadEndFree F
    → F Allows here {0} {empty} In empty
lemma-DeadEndFree-firstchoice {F} DeF 
    = subst (λ c → F Allows c In empty) c≡here c-allowed
    where
        c : Choices empty
        c = proj₁ $ DeF {0} empty allsat-empty
        c-allowed : F Allows c In empty
        c-allowed = proj₂ $ DeF {0} empty allsat-empty
        c≡here : c ≡ here
        c≡here = empty-has-one-choice c

--------------------------------------------------------------------------------
-- Extracting a normalisation function out of a satisfiable filter
--------------------------------------------------------------------------------
-- If F ♥ F, then there exists at least one normalisation function
-- satisfying F. There may be multiple. 
-- Some of such functions are as follows:
-- 1. Always pick the witnessing-choice given by the proof of F ♥ F.
-- 2. Introduce a new equivalence class when possible, otherwise
--      use the witnessing-choice of F ♥ F 
--      (implemented below as `extract-maxclass-nf).
--      (This maximises the number of equivalence classes).
-- 3. Always choose the largest allowed choice.
--      (This maximises the number of equivalence classes).
-- 4. Always choose the smallest allowed choice.
--      (This minimises the number of equivalence classes).
-- For many actual filters I consider to implement, the last one becomes
-- trivial: it always can choose 0, and does so accordingly;
-- resulting in an equivalence relation of just one boring equivalence class.
-- However, options 2 and 3 often give the desired relation.

-- Predicate that an Exence chooses to introduce a new equivalence class
-- whenever the filter allows it.
-- For many filters this is the same as maximising the number of equivalence
-- classes, although some filters may allow more equivalence classes
-- to be introduced later when fewer introduced earlier.
-- Hence "Greedily". 
ClassGreedy : Filter → Exence → Set
ClassGreedy F (h , H) = 
    (n : ℕ) 
    → F Allows (here {n} {h n}) In (h n)
    → getChoiceFromExence (h , H) n ≡ here {n} {h n}

ClassGreedyNFFun : Filter → NFFun → Set
ClassGreedyNFFun F f' = ClassGreedy F (restrict+ f')

theo-restrict+-presv-greed
    : {F : Filter}
    → (f' : NFFun)
    → ClassGreedyNFFun F f'
    → ClassGreedy F (restrict+ f')
theo-restrict+-presv-greed {F} f' greedy = greedy

theo-combine-presv-greed
    : {F : Filter}
    → (E : Exence)
    → ClassGreedy F E
    → ClassGreedyNFFun F (combine E)
theo-combine-presv-greed {F} (h , H) greedy n = 
    subst 
        (λ (( r , s) , r⋖s) →
          (F Allows here In r → getChoice r s r⋖s ≡ here)
        )
        eq
        (greedy n)
    -- The goal unfolds to showing 
    -- ClassGreedy F (restrict+ ∘ combine (h , H))
    -- i.e.
    -- (n : ℕ) 
    --      → F Allows here In (h' n) 
    --      → getChoice (h' n) (h' (suc n)) (H' n) ≡ here
    -- where
    -- (h' , H') ≔ (restrict+ ∘ combine (h , H)).
    -- Now proof is similar to theo-combine-presv-sat:
    -- we get ((h' n , h' (suc n)) , H' n) ≡ ((h n , h (suc n)) , H n)
    -- from restrict+-combine inversity and proof-irrelevance.
    -- We can rewrite the goal as a function of such triples
    -- and then just substitute that equality.
    where
        h' = proj₁ $ (restrict+ ∘ combine) (h , H)
        H' = proj₂ $ (restrict+ ∘ combine) (h , H)

        eq : _≡_ {A = ⋖-Pair n} ((h n , h (suc n)) , H n) 
                                ((h' n , h' (suc n)) , H' n)
        eq = exence-successor-tuples-eq h h' H H' refl n

module GreedyNewClass (F : Filter) (DeF : DeadEndFree F) where
    -- Pick the next choice (normal form for n) 
    -- accoding to the following rules:
    -- 1. If F allows a new equivalence class, do that.
    -- 2. Else, pick the allowed choice that DeF gives.
    -- Note: this recursively defines a sequence of allowed choices,
    -- but the definition is NOT RECURSIVE. (My previous implementation was and
    -- was rejected by the termination checker).
    nextChoice
        : {n : ℕ}
        → (r : NFRestr n)
        → AllRestr-sat F r
        → Σ[ c ∈ Choices r ] F Allows c In r
    nextChoice-cases
        : {n : ℕ}
        → (r : NFRestr (suc n))
        → AllRestr-sat F r
        → (b : Bool)
        → F r here ≡ b
        → Σ[ c ∈ Choices r ] F Allows c In r
    nextChoice {0} empty _ = (here , lemma-DeadEndFree-firstchoice DeF)
    nextChoice {suc n} r z = nextChoice-cases {n} r z (F r here) refl
    
    nextChoice-cases {n} r z true p = (here , p)
    nextChoice-cases {n} r z false p = DeF r z

    h+ : (n : ℕ) → Σ[ r ∈ NFRestr n ] AllRestr-sat F r
    h+ 0 = (empty , allsat-empty)
    h+ (suc n) = (addChoice r c , allsat-addChoice r c r-sat c-allowed)
        where
            r : NFRestr n
            r = proj₁ $ h+ n
            r-sat : AllRestr-sat F r
            r-sat = proj₂ $ h+ n
            c : Choices r
            c = proj₁ $ nextChoice r r-sat
            c-allowed : F Allows c In r
            c-allowed = proj₂ $ nextChoice r r-sat

    h : (n : ℕ) → NFRestr n 
    h = proj₁ ∘ h+

    H : (n : ℕ) → h n ⋖ h (suc n)
    H n = ⋖-addChoice (proj₁ $ nextChoice (h n) (proj₂ $ h+ n))

    altsat : Exence-sats-alt F (h , H)
    altsat = proj₂ ∘ h+

    sat : Exence-sats F (h , H)
    sat = Exence-sats-from-alt altsat

    greedy : ClassGreedy F (h , H)
    greedy zero _ =
        begin 
            getChoiceFromExence (h , H) zero
        ≡⟨⟩
            getChoice (h 0) (h 1) (H 0)
        ≡⟨⟩
            getChoice empty (addChoice empty c) (H 0)
        ≡⟨ lemma-getChoice-addChoice empty c (H 0) ⟩
            c
        ≡⟨ empty-has-one-choice c ⟩
            here {0} {empty}
        ∎
        where
            c : Choices empty
            c = proj₁ $ nextChoice empty (proj₂ $ h+ zero)
        
    greedy n@(suc n') p =
        begin 
            getChoiceFromExence (h , H) n
        ≡⟨⟩
            getChoice (h n) (h (suc n)) (H n)
        ≡⟨⟩
            getChoice (h n) (addChoice (h n) c) (H n)
        ≡⟨ lemma-getChoice-addChoice (h n) c (H n) ⟩
            proj₁ ( nextChoice (h n) (proj₂ $ h+ n))
        ≡⟨⟩
            proj₁ (nextChoice-cases (h n) (proj₂ $ h+ n) (F (h n) here) refl)
        ≡⟨ cong 
            (λ (x , y) → proj₁ (nextChoice-cases (h n) (proj₂ $ h+ n) x y ))
            p+ 
        ⟩
            proj₁ (nextChoice-cases (h n) (proj₂ $ h+ n) true p)
        ≡⟨⟩
            here 
        ∎
        where
            c : Choices (h n)
            c = proj₁ $ nextChoice (h n) (proj₂ $ h+ n)

            sublemma 
                : {A : Set} 
                → (a b c : A) 
                → (p : a ≡ b) 
                → (q : a ≡ c)
                → _≡_ {A = Σ[ x ∈ A ] (a ≡ x)} (b ,  p) (c , q)
            sublemma a b c refl refl = refl


            p+ : _≡_ {A = Σ[ b ∈ Bool ] (F (h n) here ≡ b)} 
                (F (h n) here , refl)
                (true , p)
            p+ = sublemma (F (h n) here) (F (h n) here) true refl p


extract-greedynewclass-Exence
    : {F : Filter}
    → DeadEndFree F
    → Σ[ E ∈ Exence ] (Exence-sats F E ) × (ClassGreedy F E)
extract-greedynewclass-Exence {F} DeF = ((h , H) , sat , greedy)
    where
        open GreedyNewClass F DeF

-- This is now an easy corollary.
lemma-DEF-to-Passable
    : (F : Filter)
    → DeadEndFree F
    → Passable F
lemma-DEF-to-Passable F DeF = 
    let (E , sat , greedy) = extract-greedynewclass-Exence DeF
    in (E , sat)

extract-greedynewclass-NFFun
    : {F : Filter}
    → DeadEndFree F
    → Σ[ f' ∈ NFFun ] (NFFun-sats F f' ) × (ClassGreedyNFFun F f')
extract-greedynewclass-NFFun {F} DeF = (f' , sat , greedy)
    where
        extractedExence : Σ[ E ∈ Exence ] 
                          (Exence-sats F E ) × (ClassGreedy F E)
        extractedExence = extract-greedynewclass-Exence {F} DeF

        E : Exence
        E = proj₁ extractedExence
        
        f' : NFFun
        f' = combine E

        -- The statement `NFFun-sats F f'` checks if the Exence `restrict+ f'`
        -- satisfies F.
        -- However, we know that f' was build from an Exence satisfying F,
        -- and `restrict+ ∘ combine` is essentially the identity.
        sat : Exence-sats F (restrict+ f')
        sat = theo-restrict+-presv-sat {F} f' $
              theo-combine-presv-sat {F} E (proj₁ $ proj₂ extractedExence)

        -- Same reasoning for greediness.
        greedy : ClassGreedyNFFun F f'
        greedy = theo-restrict+-presv-greed {F} f' $
                 theo-combine-presv-greed {F} E (proj₂ $ proj₂ extractedExence)


