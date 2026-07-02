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
open import Eser.Aux using (_↔_ ; _≈_)

open import Eser.Filters.Base
open import Eser.Filters.Conversions.NFFunToExence
open import Eser.Filters.Properties

module Eser.Filters.PointwiseProperties where

--------------------------------------------------------------------------------
-- Predicates whether an NFFun satisfies a Filter/Reco
--------------------------------------------------------------------------------

Exence-sats : Filter → Exence → Set
Exence-sats F (h , H) = (n : ℕ) → F (h n) (getChoiceFromExence (h , H) n) ≡ true

NFFun-sats : Filter → NFFun → Set
NFFun-sats F f' = Exence-sats F (restrict+ f')

Reco-sats : Reco → NFFun → Set
Reco-sats = ?

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

Exence-sats-to-alt
    : (F : Filter)
    → (E : Exence)
    → Exence-sats F E
    → Exence-sats-alt F E
Exence-sats-to-alt F (h , H) sat = ?

Exence-sats-from-alt
    : (F : Filter)
    → (E : Exence)
    → Exence-sats-alt F E
    → Exence-sats F E
Exence-sats-from-alt F (h , H) sat = ?


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

lemma-DEF-to-Passable
    : (F : Filter)
    → DeadEndFree F
    → Passable F
lemma-DEF-to-Passable F = ?

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

-- #TODO: use idempotence of ⋀
self-compat-to-passable
    : {F : Filter}
    → F ♥ F
    → DeadEndFree F
self-compat-to-passable = ?

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
GreedilyIntroducesClasses : Filter → Exence → Set
GreedilyIntroducesClasses F (h , H) = 
    (n : ℕ) 
    → F (h n) (here {n} {h n}) ≡ true 
    → getChoiceFromExence (h , H) n ≡ here {n} {h n}

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




--extract-greedynewclass-exence
--    : {F : Filter}
--    → DeadEndFree F
--    → Σ[ H' ∈ Exence ] (Exence-sats F H' ) × (GreedilyIntroducesClasses F H')
--extract-greedynewclass-exence {F} DeF = ((h , H) , hH-sats-F , hH-greedy)
--    where
--        -- z and h are defined in mutual induction.
--        h : (n : ℕ) → NFRestr n
--        h-cases 
--            : (n : ℕ) 
--            → (b : Bool) 
--            → NFRestr (suc n)
--        z : (n : ℕ) → AllRestr-sat F (h n)
--        z-cases 
--            : (n : ℕ) 
--            → (b : Bool) 
--            → (F (h n) here ≡ b) 
--            → AllRestr-sat F (h (suc n))

--        h zero = empty
--        h (suc n) = h-cases n (F (h n) here)

--        h-cases n false = addChoice (h n) c
--            where
--                c : Choices (h n)
--                c = proj₁ $ DeF (h n) (z n)
--        h-cases n true = newNF (h n)

--        z zero = allsat-empty
--        z (suc n) = z-cases n (F (h n) here) refl
--        z-cases n false p = subst (AllRestr-sat F) (sym h1+n-rewr) ans'
--            where
--                c : Choices (h n)
--                c = proj₁ $ DeF (h n) (z n)
--                c-allowed : F Allows c In (h n)
--                c-allowed = proj₂ $ DeF (h n) (z n)
--                h1+n-rewr : h (suc n) ≡ addChoice (h n) c
--                h1+n-rewr = 
--                    begin 
--                        h (suc n)
--                    ≡⟨⟩
--                        h-cases n (F (h n) here)
--                    ≡⟨ cong (h-cases n) p ⟩
--                        h-cases n false
--                    ≡⟨⟩
--                        addChoice (h n) c
--                    ∎
                    

--                ans' : AllRestr-sat F (addChoice (h n) c)
--                ans' = allsat-addChoice (h n) c (z n) c-allowed

--        z-cases n true p = subst (AllRestr-sat F) (sym h1+n-rewr) ans'
--            where
--                h1+n-rewr : h (suc n) ≡ newNF (h n)
--                h1+n-rewr = 
--                    begin 
--                        h (suc n)
--                    ≡⟨⟩
--                        h-cases n (F (h n) here)
--                    ≡⟨ cong (h-cases n) p ⟩
--                        h-cases n true
--                    ≡⟨⟩
--                        newNF (h n)
--                    ∎

--                ans' : AllRestr-sat F (newNF (h n))
--                ans' = allsat-newNF (h n) (z n) p


--        H : (n : ℕ) → h n ⋖ h (suc n)
--        H = ?
--        hH-sats-F : Exence-sats F (h , H)
--        hH-sats-F = ?
--        hH-greedy : GreedilyIntroducesClasses F (h , H)
--        hH-greedy = ?

    

---- Extract a normalisation function from a passable Filter.
--extract-maxclass-nf
--    : {F : Filter}
--    → Passable F
--    → Σ[ f ∈ NFFun ] (NFFun-sats F f ) × (MaximisesClasses F f)
--extract-maxclass-nf {F} pass = (f' , f-stats-F , f-max-classes)
--    where
--        E : Exence
--        E = proj₁ pass

--        f' = combine E

--        --f : ℕ → ℕ
--        --f = ?

--        --f-leq : (n : ℕ) → f n ≤ n
--        --f-leq n = ?

--        --f-fix : (n : ℕ) → f (f n) ≡ f n
--        --f-fix n = ?

--        --f' : NFFun
--        --f' = (f , f-leq , f-fix)

--        --f-stats-F : (Filter-sats F f' )
--        --f-stats-F = ?

--        f-max-classes : (MaximisesClasses F f')
--        f-max-classes = ?


