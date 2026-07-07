-- Module      : Eser.Filters.Congruence
-- Description : Initial sketch how to implement 'is-a-congruence' as a Filter.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Binary.Definitions using (Decidable ; DecidableEquality)
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)
open import Data.Maybe

open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n)

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_)

open import Eser.Filters.Base
open import Eser.Filters.Resurface

module Eser.Filters.Congruence where

--------------------------------------------------------------------------------
-- 𝐂𝐎𝐍𝐆𝐑𝐔𝐄𝐍𝐂𝐄
-- This story is about implementing the 'is-a-congruence' predicate
-- for relations over term algebras over signatures.
-- The low-level definition of 'congruence' depends on the operations in
-- the signature, but it is unpractical to reimplement congruence 
-- for every signature.
--
-- So instead we define a generalisation of 'congruence' for any 'ReplaceStruct',
-- which are abstractions capturing only the minimal features of term algebras
-- needed to define congruence.
-- ReplaceStructs are enumerable types together with an
-- 'is-argument-of'-relation denoted as _⊂_,
-- and a replacement operation allowing to swap 'arguments'.
-- We only impose the minimal set of axioms needed to define
-- the generalisation of 'congruence', which we call 'ReplaceRespecting'.
-- Consequently, not all ReplacementStructs correspond to term algebras;
-- for example, we do not require that replacing an 
-- argument in a term with the same argument
-- leaves the term unchanged, nor that changing an argument x in a term t by x'
-- gives a term actually containing x' as argument.
-- However, when specialising to ReplaceStructs that do correspond to actual
-- term algebras, one does recover the traditional notion of congruence.
--
-- We only consider enumerable term algebras T, 
-- so w.l.o.g. we omit the bijection T ≃ ℕ and just work directly on ℕ.
--
-- Concretely, we will do the following:
-- 1. Define ReplaceStructs.
-- 2. Define two notions of ReplaceRespecting (parametrised by a ReplaceStruct).
--   Recall that decidable equivalence relations correspond
--   to normalisation functions ℕ → ℕ, which correspond to extension-sequences
--   (Exences). We can define predicates globally on equivalence relations,
--   or locally as Filters that constrain choices for the equivalence class
--   of n when extending the domain a restricted 
--   equivalence relation from {0, ..., n-1} to {0, ..., n}.
--   The notions are:
-- 2.1. A global notion on equivalence relations ℕ → ℕ → Bool.
-- 2.2. A local notion implemented as a Filter.
-- 3. We prove that the global notion holds if and only if the local does.
--
-- Thereafter we will demonstrate this terse generalisation of congruence
-- 'works as intended' in practial contexts,
-- by specialising it to our implementation of signatures and term algebras
-- (from the modules in `Eser.Signature`, using the `Signatures` and
-- `ClosedTerms' of the `Eser` library):
-- 4. Show that the closed terms over any Signature from a ReplaceStruct.
-- 5. Define the traditional notion of 'congruence' (as a predicate
--  on relations).
-- 6. Show that a relation satisfies this notion of congruence
--  if and only if it satisfies the (global notion) of 'ReplaceRespecting'.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Replacement Structures
--------------------------------------------------------------------------------
-- Terse encoding of an enumerable type A with a 'is-argument-of'
-- relation _⊂_. We omit the bijection A ≃ ℕ and work on ℕ directly.
-- Arguments must be smaller in the enumertion than the term containing them.
-- There is a `replace` operation such that `replace y x x'`
-- represents the term `y` with argument `x` substituted by `x'`.
-- We abstract from most implementation details of `replace`,
-- and do not even distinguish between replacing a 
-- single or all occurrences of `x`.
-- Replacing an argument by a smaller one must result
-- in a term that is overall smaller.
--
-- Implementation note
-- I first used the following fields:
--      _⊂_ : ℕ → ℕ → Set
--      ⊂-dec : Decidable _⊂_
-- but then a `ReplaceStruct` becomes a Set₁, and I feared this may become an
-- annoyance further down the road.

record ReplaceStruct : Set where
    field
        _is-arg-of_ : ℕ → ℕ → Bool
        ⊂-resp-< : (y x : ℕ) → x is-arg-of y ≡ true → x < y
        replace : ℕ → ℕ → ℕ → ℕ
        replace-< 
            : (y x x' : ℕ) 
            → (x is-arg-of y ≡ true) 
            → (x' < x) 
            → (replace y x x' < y)
open ReplaceStruct


--------------------------------------------------------------------------------
-- Predicate 'ReplaceResp'
--------------------------------------------------------------------------------
module ReplaceResp (T : ReplaceStruct) where
    _⊂_ : ℕ → ℕ → Set
    _⊂_ n m = (_is-arg-of_ T) n m ≡ true


    -- Global version: a relation is 'Replacement Respecting'
    -- if replacing an argument x of y by a related argument x'
    -- results in a term y' that is related to y.
    module _ (R' : DecEquiv) where
        R = proj₁ R'
        ReplaceRespGlobal : Set
        ReplaceRespGlobal 
            = (y x x' : ℕ)
            → x ⊂ y
            → x' < x
            → R x x' ≡ true
            → R y (replace T y x x') ≡ true
        -- Remark: the `x' < x' premise is, intuitively, unnecessary.
        -- But it makes proving the correspondence to the local view
        -- much easier.
        -- For well-behaved `replace` functions it seems that this
        -- version of `ReplaceRespGlobal` implies the variant
        -- without the `x' < x` premise anyway (we don't prove this).
    
    -- #TODO: move next to defs to `Base.agda`.

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
 

    -- An NFRestr n encodes an equivalence relation restricted
    -- to domain {0, ..., n-1}. So on this domain we can use it as a relation.
    NFRestrRel 
        : {n : ℕ}
        → (r : NFRestr n)
        → {x x' : ℕ}
        → x < n
        → x' < n
        → Bool
    NFRestrRel {n} r x<n x'<n = does (resurface r x<n ≡? resurface r x'<n)

    AreRelated : {n : ℕ} → (r : NFRestr n) → ℕ → ℕ → Set
    AreRelated {n} r x x' = (p : x < n) → (q : x' < n) → NFRestrRel r p q ≡ true

    -- Predicate that no argument of y is related (according to r)
    -- to a smaller term.
    AllArgsNormal
        : {y : ℕ}
        → (r : NFRestr y)
        → Set
    AllArgsNormal {y} r
        = (x : ℕ) 
        → (x ⊂ y)
        → ¬ (Σ[ x' ∈ ℕ ] 
             Σ[ p ∈ x' < x ] 
             (AreRelated r x x')
            )
    -- Note: p and q are proof-irrelevant, and are already implied
    -- by x ⊂ y and (via transitivity) x' < x.
    -- However, giving them as arguments is more convenient than
    -- fixing defaults and having to use `subst`.
    
    -- Proof-relevant predicate that y has an argument x
    -- that is (according to r) related to x' with x' < x.
    NonNormalArg
        : {y : ℕ}
        → (r : NFRestr y)
        → Set
    NonNormalArg {y} r =
        Σ[ x ∈ ℕ ] Σ[ x' ∈ ℕ ] (x ⊂ y) × (x' < x) × (AreRelated r x x')

    allArgsNormal?
        : {n : ℕ}
        → (r : NFRestr n)
        → AllArgsNormal r ⊎ NonNormalArg r
    allArgsNormal? {n} r = ?

    -- Local version.
    -- When needing to filter out the allowed equivalence classes for `y`,
    -- it checks whether `y` contains an argument x 'not in normal form',
    -- which in this abstract context is defined as 'related to a smaller term
    -- x' '.
    -- If it does, then the only allowed equivalence class
    -- is the class of `replace y x x'`; since `replace y x x' < y` this choice
    -- is indeed available.
    -- Otherwise the filter gives free choices.
    ReplaceRespLocal : Filter
    ReplaceRespLocal-cases 
        : {y : ℕ}
        → (r : NFRestr y)
        → (c : Choices r)
        → AllArgsNormal r ⊎ NonNormalArg r
        → Bool
    -- All args are normal, no congruence constraints; free choice!
    ReplaceRespLocal-cases {y} r _ (inj₁ _) = true 
    -- Some argument of y can be 'normalised'. The equivalence class
    -- of y must equal the equivalence class of 
    -- y-but-with-this-argument-normalised.
    ReplaceRespLocal-cases {y} r c (inj₂ (x , x' , x⊂y , x'<x , x'∼x)) =
        does (c ≡? y'-nf)
        where
            y' : ℕ
            y' = replace T y x x'
            y'<y : y' < y
            y'<y = replace-< T y x x' x⊂y x'<x
            -- Resurface the normal form of y' as a choice of normal form for y.
            y'-nf : Choices r
            y'-nf = earlier-new $ resurface r y'<y

    ReplaceRespLocal {y} r c = ReplaceRespLocal-cases {y} r c (allArgsNormal? r)
    


