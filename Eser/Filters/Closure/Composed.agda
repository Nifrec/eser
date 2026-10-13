-- Module      : Eser.Filters.Closure.Single
-- Description : Properties of closing w.r.t. a composition of filters.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

--{-# OPTIONS --safe #-}

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
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.EqRel.EqRelProperties
open import Eser.Aux using (_≈_ ; _↔_ ; ↔-to ; ↔-from)
open import Eser.Relation.Binary.Path

open import Eser.Filters.Conversions.NFFunToExence
open import Eser.Filters.Base
open import Eser.Filters.Properties
open import Eser.Filters.PointwiseProperties
open import Eser.Filters.Resurface
open import Eser.Filters.Composition
open import Eser.Filters.Closure.Single

module Eser.Filters.Closure.Composed where

--------------------------------------------------------------------------------
-- The order of composition of EqFilters does not matter for the closure.
--------------------------------------------------------------------------------

-- Same-extender-up-to-function-extensionalty relation.
-- (Output relations are homotopic).
_=ext_ : Extender → Extender → Set
G =ext F = (R : EqRel) → proj₁ (proj₁ $ G R) ≈ proj₁ (proj₁ $ F R)
 
-- 𝐓𝐡𝐞𝐨𝐫𝐞𝐦
-- When closing by multiple equation filters, the order does not matter.
eqfilter-closure-commutes
    : (E E' : EqFilter)
    → (∗ E ⋗ ∗ E') =ext (∗ E' ⋗ ∗ E)
eqfilter-closure-commutes E E' = {! See sheet exco 6. Depends on prev lemma. !}

--------------------------------------------------------------------------------
-- Characterisation of closure w.r.t. a list of EqFilters.
--------------------------------------------------------------------------------

Eq' : List EqFilter → ℕ → ℕ →  Set
Eq' L x y = Any (λ E → Eq E x y) L

eqfilter-closure-compos-subrelat
    : {L : List EqFilter}
    → {R : EqRel}
    → {x y : ℕ}
    → Eq' L x y
    → ((proj₁ $ (eq-list-closure L) R) relates x to y) 
eqfilter-closure-compos-subrelat {[]} {R} {x} {y} ()
eqfilter-closure-compos-subrelat {E ∷ Es} {R} {x} {y} (here xEy) =
    eqfilter-closure-subrelat {E} {S'} {x} {y} xEy
    where
        S' : EqRel
        S' = proj₁ $ (eq-list-closure Es) R
eqfilter-closure-compos-subrelat {E ∷ Es} {R} {x} {y} (there any) = xSy
    where
        S : EqRel
        S =  proj₁ $ (eq-list-closure (E ∷ Es)) R
        -- ^ That equals `proj₁ $ (∗ E) S'`
        S' : EqRel
        S' = proj₁ $ (eq-list-closure Es) R
        S'⊆S : S' ⊆ S
        S'⊆S = proj₂ $ (∗ E) S'
        xS'y : S' relates x to y
        xS'y = eqfilter-closure-compos-subrelat {Es} {R} {x} {y} any
        xSy : S relates x to y
        xSy = S'⊆S x y xS'y

Eq'-⊎
    : {Es : List EqFilter}
    → {E : EqFilter}
    → {x y : ℕ}
    → (Eq' Es ⊎⊎ Eq E) x y
    → Eq' (E ∷ Es) x y
Eq'-⊎ {Es} {E} {x} {y} = ↔-to $ Any-⊎-right (λ E → Eq E x y) E Es
    where
        open import Eser.Data.List.Relation.Unary.Any.Properties
            using (Any-⊎-right)

-- Let L : List EqFilter.
-- If S is the L-closure of R then R ⊆ S.
eqfilter-closure-composition-subrelat-R
    : (L : List EqFilter)
    → (R : EqRel)
    → R ⊆ (proj₁ $ (eq-list-closure L) R)
eqfilter-closure-composition-subrelat-R [] R x y xRy = xRy
eqfilter-closure-composition-subrelat-R (E ∷ Es) R = 
    ⊆-trans {R} {S'} {S} R⊆S' S'⊆S
    where
        S  : EqRel
        S  = (proj₁ $ (eq-list-closure (E ∷ Es)) R)
        S' : EqRel
        S' = (proj₁ $ (eq-list-closure Es) R)
        R⊆S' : R ⊆ S'
        R⊆S' = eqfilter-closure-composition-subrelat-R Es R
        S'⊆S : S' ⊆ S
        S'⊆S = ext (EqFilter-IsClosable E S')

-- 𝐓𝐡𝐞𝐨𝐫𝐞𝐦
-- Generalisation of `eqfilter-closure-characterisation` to compositions
-- of equations. 
-- Shows that the output of the L-closure is just R extended with
-- the equations in L and closed under transitivity.
eqfilter-closure-composition
    : (L : List EqFilter)
    → (R : EqRel)
    → (x y : ℕ)
    → ((proj₁ $ (eq-list-closure L) R) relates x to y) 
      ↔ 
      (Path (R relates_to_) (Eq' L) x y)
-- Proof strategy: induction on L. 
-- In the L ≗ [] case both sides are just xRy.
-- In the L ≗ (E ∷ Es) case both directions needs to be shown separately.
-- Let S ≔ proj₁ $ (eq-list-closure L) R.
-- 1. Assume xSy. eqfilter-closure-characterisation gives a path
--   containing S' and E as steps, where S' ≔ proj₁ $ (eq-list-closure Es) R.
--   The IH allows to rewrite the S'-steps into sub-paths over R and Es.
--   Then apply a 'flatten' lemma to make this into one path.
-- 2. For the other direction, a path is given, and proceed by induction
--   on the path, inductively proving that every step xTy implies xSy,
--   and then conclude by transitivity of S.
eqfilter-closure-composition [] R x y = ans
    where
        path→R : Path (R relates_to_) (Eq' []) x y → R relates x to y
        path→R = ?
        --path→R (samedir x<y p) = 
        --    path-uninhabited-right (λ x y → ¬Any[]) (relates-to-trans R) p
        --path→R (emptypath refl) = relates-to-refl R
        --path→R (oppdir x<y p) = relates-to-sym R $ 
        --    path-uninhabited-right (λ y x → ¬Any[]) (relates-to-trans R) p

        R→path : R relates x to y → Path (R relates_to_) (Eq' []) x y
        --R→path = ?
        R→path xRy = {! cases (<-cmp x y) !}
            --where
            --    cases 
            --        : Tri (x < y) (x ≡ y) (x > y) → 
            --        Path (R relates_to_) (Eq' []) x y
            --    cases (tri< x<y x≢y y≮x) =
            --        samedir x<y $ laststep x<y $ inj₁ xRy
            --    cases (tri≈ x≮y x≡y y≮x) = emptypath x≡y
            --    cases (tri> x≮y x≢y y<x) = 
            --        oppdir y<x $ laststep y<x $ inj₁ (relates-to-sym R xRy)

        -- The goal simplifies to this:
        ans : (R relates x to y) ↔ Path (R relates_to_) (Eq' []) x y
        ans = (R→path , path→R)
eqfilter-closure-composition (E ∷ Es) R x y = (to x y , from x y)
    where
        S : EqRel
        S = proj₁ $ (eq-list-closure (E ∷ Es)) R

        -- S' is the same as S but not yet closed under E.
        -- I.e., S is the E-closure of S'.
        S' : EqRel
        S' = proj₁ $ (eq-list-closure Es) R

        check : S ≡ proj₁ ((∗ E) S')
        check = refl


        --to-< 
        --    : {x y : ℕ}
        --    → S relates x to y 
        --    → <Path (R relates_to_) (Eq' (E ∷ Es)) x y
        --to-< {x} {y} x<y xSy = flatpath'
        --    where
        --        lastclosure 
        --            : S relates x to y 
        --            → Path (S' relates_to_) (Eq E) x y
        --        lastclosure = 
        --            ↔-to 
        --                {S relates x to y} 
        --                {Path (S' relates_to_) (Eq E) x y}
        --                $ eqfilter-closure-characterisation E S' x y
        --        nestedpath : <Path (S' relates_to_) (Eq E) x y
        --        nestedpath = tripath-elim-< (lastclosure xSy) x<y

        --        IH  : {x y : ℕ}
        --            → S' relates x to y 
        --            → Path (R relates_to_) (Eq' Es) x y 
        --        IH {x} {y} = ↔-to (eqfilter-closure-composition Es R x y)

        --        nestedpath' : <Path (Path (R relates_to_) (Eq' Es)) 
        --                            (Eq E) x y
        --        nestedpath' = path-map-left {S' relates_to_} {Eq E} 
        --                        {Path (R relates_to_) (Eq' Es)} 
        --                        IH {x} {y} nestedpath
        --        -- The Path steps must all be <Path steps in the same
        --        -- direction.
        --        nestedpath'' : <Path (<Path (R relates_to_) (Eq' Es)) (Eq E) x y
        --        nestedpath'' = nested-tripath-left nestedpath'

        --        flatpath : <Path (R relates_to_) (Eq' Es ⊎⊎ Eq E) x y
        --        flatpath = path-flatten-left nestedpath''

        --        flatpath' : <Path (R relates_to_) (Eq' (E ∷ Es)) x y
        --        flatpath' = path-map-right Eq'-⊎ flatpath
        to 
            : (x y : ℕ)
            → S relates x to y 
            → Path (R relates_to_) (Eq' (E ∷ Es)) x y
        to x y = ?
            --cases (<-cmp x y)
            --where
            --    cases 
            --        : Tri (x < y) (x ≡ y) (x > y)
            --        → S relates x to y 
            --        → Path (R relates_to_) (Eq' (E ∷ Es)) x y
            --    cases (tri< x<y _ _) xSy = samedir x<y $ to-< {x} {y} x<y xSy
            --    cases (tri≈ _ x≡y _) = λ _ → emptypath x≡y
            --    cases (tri> _ _ y<x) xSy = oppdir y<x 
            --        $ to-< {y} {x} y<x (relates-to-sym S {x} {y} xSy )

        R⊆S : R ⊆ S
        R⊆S = eqfilter-closure-composition-subrelat-R (E ∷ Es) R


        L→S : {x y : ℕ} → (Eq' (E ∷ Es) x y) → S relates x to y
        L→S = eqfilter-closure-compos-subrelat {E ∷ Es} {R}


        --from-samedir 
        --    : {x y : ℕ}
        --    → <Path (R relates_to_) (Eq' (E ∷ Es)) x y 
        --    → S relates x to y
        --from-samedir (laststep {x} {y} x<y (inj₁ xRy)) = R⊆S x y xRy
        --from-samedir (laststep {x} {y} x<y (inj₂ xLy)) = L→S xLy
        --from-samedir (addstep {x} {z} {y} x<z z<y (inj₁ xRz) p) = 
        --    relates-to-trans S {x} {z} {y} (R⊆S x z xRz) (from-samedir p)
        --from-samedir (addstep {x} {z} {y} x<z z<y (inj₂ xLz) p) =
        --    relates-to-trans S {x} {z} {y} (L→S xLz) (from-samedir p)

        from 
            : (x y : ℕ) 
            → Path (R relates_to_) (Eq' (E ∷ Es)) x y 
            → S relates x to y
        from = ?
        --from x y (samedir {x} {y} x<y p) = from-samedir p
        --from x y (emptypath refl) = relates-to-refl S {x}
        --from x y (oppdir {x} {y} y<x p) = 
        --    relates-to-sym S {y} {x} (from-samedir {y} {x} p)
    
-- 𝐂𝐨𝐫𝐨𝐥𝐥𝐚𝐫𝐲
-- Every equation in L : List EqFilter holds in the L-closure of R.
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All as All
-- #TODO L choose which (or both) of the two below to prove.
-- Both should be easy given the previous theorem (or the other).
-- When removing one statement, also remove the associated import.
eqfilter-closure-composition-anyeqs
    : (L : List EqFilter)
    → (R : EqRel)
    → {E : EqFilter}
    → E ∈ L
    → (x y : ℕ)
    → Eq E x y
    → (proj₁ $ (eq-list-closure L R)) relates x to y
eqfilter-closure-composition-anyeqs = ?
eqfilter-closure-composition-alleqs
    : (L : List EqFilter)
    → (R : EqRel)
    → (x y : ℕ)
    → All (λ E → Eq E x y → (proj₁ $ (eq-list-closure L R)) relates x to y) L
eqfilter-closure-composition-alleqs = ?

