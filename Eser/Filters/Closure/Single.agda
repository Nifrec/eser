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

        --open PathBase (R relates_to_) (Eq E)

        to : (x y : ℕ) 
            → ExRel hH x y
            → Path (R relates_to_) (Eq E) x y
        to x y = cases (<-cmp x y)
            where
                -- The only difficult case is when x < y.
                -- When x ≡ y we can return an empty path,
                -- and y < x is symmetric to the x < y case.
                to-< 
                    : {x y : ℕ}
                    → x < y
                    → Dec (IsFire (E y))
                    → ExRel hH x y
                    → Path (R relates_to_) (Eq E) x y
                to-< {x} {y} x<y (no ¬fire) xhHy = ?
                to-< {x} {y} x<y (yes fire) xhHy = ?

                cases 
                    : (Tri (x < y) (x ≡ y) (x > y))
                    → ExRel hH x y
                    → Path (R relates_to_) (Eq E) x y
                cases (tri≈ _ refl _) _ = empty x
                cases (tri< x<y _ _) = to-< x<y (isfire? (E y))
                cases (tri> _ _ y<x) xhHy = 
                    path-sym (R relates_to_) (Eq E) 
                    $ to-< {y} {x} y<x (isfire? (E x)) 
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
