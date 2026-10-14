-- Module      : Eser.Filters.Closure.Single
-- Description : Properties of closing w.r.t. a single filter.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- For properties specific to closures w.r.t. compositions of filters, see
-- Eser.Filters.Closure.Composed instead.
--------------------------------------------------------------------------------

--{-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.Definitions 
    using (Tri ; Reflexive ; Symmetric ; Transitive ; DecidableEquality)
open Tri
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)
open import Data.List using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties

open import Eser.EqRel.Definitions
open import Eser.EqRel.Conversions
open import Eser.EqRel.EqRelProperties
open import Eser.Aux using 
    (_≈_ 
    ; _≈≈_ 
    ; _↔_ 
    ; ↔-to 
    ; ↔-from 
    ; ↔-trans 
    ; doubleCong
    ; ≡→↔
    )
open import Eser.Relation.Binary.Path

open import Eser.Filters.Conversions.NFFunToExence
open import Eser.Filters.Base
open import Eser.Filters.Properties
open import Eser.Filters.PointwiseProperties
open import Eser.Filters.Resurface
open import Eser.Filters.Composition
open _closure-of_

module Eser.Filters.Closure.Single where

--------------------------------------------------------------------------------
-- Preliminary/auxiliary lemmas
--------------------------------------------------------------------------------

-- Get the F-closure of R represented in the form of an Exence.
exclosure
    : {F : Filter}
    → (C : IsClosable F)
    → (R : EqRel)
    → Exence
exclosure C R = rel-to-exence $ rel (C R)

get-unique-choice-exence
    : {F : MFF}
    → (C : IsClosable' F)
    → (AF : AlwaysFires F)
    → (R : EqRel)
    → (y : ℕ)
    → getChoiceFromExence (exclosure C R) y 
      ≡ 
      (proj₁ $ get-unique-choice C AF (proj₁ (exclosure C R) y))
get-unique-choice-exence = ?


--------------------------------------------------------------------------------
-- 𝐓𝐡𝐞𝐨𝐫𝐞𝐦
-- Characterisation of a closure of a relation w.r.t. an EqFilter.
--
-- Let S be the E-closure of R.
-- Then x S y iff there exists a path 
--      x = z_1 < z_2 < ... < z_k = y
-- where for each i either 
--      z_i R z_{1+i} 
-- or 
--      Eq E z_i z_{i + 1}.
--------------------------------------------------------------------------------
-- Proof stategy: we first prove it for the Exence corresponding to the closure,
-- because this representation is much closer to filters and the construction of
-- the relation.
-- Then we lift the result via the canonical conversions to EqRel.
--------------------------------------------------------------------------------

get-closure-as-exence 
    : (E : EqFilter)
    → (R : EqRel)
    → Exence
get-closure-as-exence E R = rel-to-exence $ rel (C R)
    where
        C : IsClosable (EqFilter→Filter E)
        C = EqFilter-IsClosable E

-- Statement of next lemma.
ClosureExBiimpl
    : (E : EqFilter)
    → (R : EqRel)
    → Set
ClosureExBiimpl E R = 
      (x y : ℕ)
    → (ExRel (get-closure-as-exence E R) x y)
      ↔
      (Path (R relates_to_) (Eq E) x y )

eqfil-closure-char-exence
    : (E : EqFilter)
    → (R : EqRel)
    → ClosureExBiimpl E R
eqfil-closure-char-exence E R x y = (to x y , from x y)
    where
        F : Filter
        F = EqFilter→Filter E
        C : IsClosable F
        C = EqFilter-IsClosable E
        hH : Exence
        hH = rel-to-exence $ rel (C R)
        h : (n : ℕ) → NFRestr n
        h = proj₁ hH

        to : (x y : ℕ) 
            → ExRel hH x y
            → Path (R relates_to_) (Eq E) x y
        to x y = cases (<-cmp x y)
            where
                -- The only difficult case is when x < y.
                -- When x ≡ y we can return an empty path,
                -- and y < x is symmetric to the x < y case.
                -- (See `to` below for this case distinction).
                to-< 
                    : {x y : ℕ}
                    → x < y
                    → (p : MayFire (Σ[ m ∈ ℕ ] m < y ))
                    → p ≡ E y
                    → ExRel hH x y
                    → Path (R relates_to_) (Eq E) x y
                to-< {x} {y} x<y pass eq xhHy = ?
                    -- Make a case distinction on the normal form of y according
                    -- to R. It is some m ≤ y such that m R y.
                    --
                    -- The case m ≡ y leads to a contradiction.
                    -- hH satisfies F_R » E' 
                    -- (where F_R ≔ filterify R and E' ≔ EqFilter→MFF E), 
                    -- but we are in the case where E did not 
                    -- fire on input (h y), and F_R always fires,
                    -- so the choice that moves (h y) to (h 1+y) is the unique
                    -- choice F_R allows. Since m ≡ y, this choice can only be
                    -- `newNF`. However, x hH y means that the normal form of y
                    -- equals the normal form of x ≢ y, which is only possible
                    -- if this choice is NOT `newNF`.
                    -- So this choice is both equal and inequal to `newNF`:
                    -- contradiction.
                    --
                    -- If x ≡ m < y then return the singleton path m R y.
                    --
                    -- If x < m, then R ⊆ hH implies m hH y,
                    -- and by transitivity & symmetry of hH we obtain 
                    -- also x hH m. A well-founded recursive call gives
                    -- a Path x m (allowed since m < y). 
                    -- Composing this with the singleton path 
                    -- of mRy gives the desired result.
                    --
                    -- The case m < x is symmetric to the previous one,
                    -- noting that also x < y holds.
                to-< {x} {y} x<y (fire (m , m<y)) eq xhHy = ?
                    -- In this case, the EqFilter fired on input y
                    -- and forced the NF of y to be the same as the NF of m.
                    -- So we have m E y.
                    -- Since hH sats the EqFilter, it follows that hH related m
                    -- and y: m hH y.
                    --
                    -- If x ≡ m then return singleton path m E y.
                    --
                    -- Otherwise, w.l.o.g. assume x < m.
                    -- Since hH is transitive and symmetric and x hH y
                    -- we obtain also x hH m.
                    -- Since m < y we can make a well-founded recursive call
                    -- to obtain a Path x m. Apply path-trans with the m E y
                    -- singleton path to obtain the desired result
                    -- (or use path-sym , addstep, and path-sym again).
                    -- (If instead m < x we can do the same, since also x < y).

                cases 
                    : (Tri (x < y) (x ≡ y) (x > y))
                    → ExRel hH x y
                    → Path (R relates_to_) (Eq E) x y
                cases (tri≈ _ refl _) _ = empty x
                cases (tri< x<y _ _) = to-< x<y (E y) refl
                cases (tri> _ _ y<x) xhHy = 
                    path-sym (R relates_to_) (Eq E) 
                    $ to-< {y} {x} y<x (E x) refl
                        (relates-to-sym (exence-to-rel hH) {x} {y} xhHy)

        from 
            : (x y : ℕ) 
            → Path (R relates_to_) (Eq E) x y
            → ExRel hH x y
        from x y p = ?

--------------------------------------------------------------------------------
-- Conversion lemma of previous lemma to main theorem.
--------------------------------------------------------------------------------


ConversionStatement
    : (E : EqFilter)
    → (R : EqRel)
    → Set
ConversionStatement E R = (x y : ℕ) → (S relates x to y) ↔ (ExRel hH x y)
    where
        F : Filter
        F = EqFilter→Filter E
        C : IsClosable F
        C = EqFilter-IsClosable E
        hH : Exence
        hH = rel-to-exence $ rel (C R)
        S : EqRel
        S = rel (C R)

-- Pointwise conversion from the Exence representation
-- to the EqRel representation of a closure.
closure-exence-to-eqrel
    : (E : EqFilter)
    → (R : EqRel)
    → ConversionStatement E R
closure-exence-to-eqrel E R x y = ≡→↔ $ sym $ eq x y
    where
        F : Filter
        F = EqFilter→Filter E
        C : IsClosable F
        C = EqFilter-IsClosable E
        hH : Exence
        hH = rel-to-exence $ rel (C R)
        S : EqRel
        S = rel (C R)

        open ≡-Reasoning

        S'' : ℕ → ℕ → Bool
        S'' = proj₁ $ (FunToRel ∘ combine ∘ restrict+ ∘ RelToFun) S

        eq : (x y : ℕ)
           → ExRel hH x y ≡ S relates x to y 
        eq x y = 
            begin 
                ExRel hH x y 
            ≡⟨⟩
                ((FunToRel ∘ combine) hH) relates x to y
            ≡⟨⟩
                ((FunToRel ∘ combine ∘ restrict+ ∘ RelToFun) S) relates x to y
            ≡⟨⟩
                T (S'' x y) 
            ≡⟨ cong T $ eqrel-exence-round-trip S x y ⟩ 
                T (proj₁ S x y) 
            ≡⟨⟩
                S relates x to y
            ∎
            
-- Statement (final type) of the next theorem:
ClosureBiimpl
    : (E : EqFilter)
    → (R : EqRel)
    → Set
ClosureBiimpl E R = 
      (x y : ℕ)
    → (S relates x to y) 
      ↔
      (Path (R relates_to_) (Eq E) x y )
    where
        F : Filter
        F = EqFilter→Filter E
        C : IsClosable F
        C = EqFilter-IsClosable E
        -- S is the E-closure of R.
        S : EqRel
        S = rel (C R)

eqfilter-closure-characterisation
    : (E : EqFilter)
    → (R : EqRel)
    → ClosureBiimpl E R
eqfilter-closure-characterisation E R x y = 
    ↔-trans (closure-exence-to-eqrel E R x y) 
            (eqfil-closure-char-exence E R x y)
