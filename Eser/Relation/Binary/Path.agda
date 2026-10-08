-- Module      : Eser.Relation.Binary.Path
-- Description : Paths where each step exists in one of two relations.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Path R S x y
-- is a finite sequence x = z_1 < z_2 < ... < z_k = y
-- such that each z_i is related to z_{1+i} by either R or S.
-- E.g. 1 R 2 S 5 R 7 R 10
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat
open import Data.Nat.Properties -- using (<-trans)
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Data.Unit
open import Relation.Binary.Core using () renaming (_⇒_ to _⊆_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions using (Transitive)
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)

module Eser.Relation.Binary.Path where

data <Path (R S : ℕ → ℕ → Set) : ℕ → ℕ → Set where
    laststep 
        : {x y : ℕ} 
        → x < y 
        → R x y ⊎ S x y 
        → <Path R S x y
    addstep
        : {x y z : ℕ}
        → x < y
        → y < z
        → R x y ⊎ S x y
        → <Path R S y z
        → <Path R S x z

path-to-<
    : {R S : ℕ → ℕ → Set}
    → {x y : ℕ}
    → <Path R S x y
    → x < y
path-to-< (laststep x<y _) = x<y
path-to-< (addstep x<y y<z _ _) = <-trans x<y y<z

cat : {R S : ℕ → ℕ → Set}
    → {x y z : ℕ}
    → <Path R S x y
    → <Path R S y z
    → <Path R S x z
cat {R} {S} {x} {y} {z} (laststep x<y step) p = 
    addstep x<y y<z step p
    where 
        y<z : y < z
        y<z = path-to-< p
cat {R} {S} {x} {y} {z} (addstep {x} {a} {y} x<a _ step q) p = 
    addstep x<a a<z step qp
    where
        qp : <Path R S a z
        qp = cat q p
        a<z : a < z
        a<z = path-to-< qp

path-map-left
    : {R S T : ℕ → ℕ → Set}
    → R ⊆ T
    → <Path R S ⊆ <Path T S
path-map-left R⊆T {x} {y} (laststep x<y (inj₁ xRy)) = 
    laststep x<y $ inj₁ $ R⊆T xRy
path-map-left R⊆T {x} {y} (laststep x<y (inj₂ xSy)) = laststep x<y (inj₂ xSy)
path-map-left {R} {S} {T} R⊆T {x} {y} 
    (addstep {x} {z} {y} x<z z<y (inj₁ xRz) p) =
    let xTz = R⊆T xRz in
    addstep {T} {S} x<z z<y (inj₁ xTz) $ path-map-left R⊆T {z} {y} p
path-map-left R⊆T {x} {y} (addstep {x} {z} {y} x<z z<y (inj₂ xSz) p) =
    addstep x<z z<y (inj₂ xSz) $ path-map-left R⊆T p

-- Paths where one of the two relations is uninhabited and the other
-- is transitive, are just this last relation.
path-uninhabited-right
    : {R S : ℕ → ℕ → Set}
    → ((x y : ℕ) → ¬ (S x y))
    → Transitive R
    → <Path R S ⊆ R
-- Proof: induction on the `<Path R S x y`.
path-uninhabited-right {R} {S} ¬S trans-R {x} {y} 
    (laststep x<y (inj₁ xRy)) = xRy
path-uninhabited-right {R} {S} ¬S trans-R {x} {y} 
    (laststep x<y (inj₂ xSy)) = ⊥-elim $ ¬S x y xSy
path-uninhabited-right {R} {S} ¬S trans-R {x} {y} 
    (addstep {x} {z} {y} x<z z<y (inj₁ xRz) p) = trans-R xRz zRy
        where
            zRy : R z y
            zRy = path-uninhabited-right ¬S trans-R {z} {y} p
path-uninhabited-right {R} {S} ¬S trans-R {x} {y} 
    (addstep {x} {z} {y} _ _ (inj₂ xSz) _) = ⊥-elim $ ¬S x z xSz

-- Pointwise ⊎ of two relations.
_⊎⊎_ : (ℕ → ℕ → Set)
     → (ℕ → ℕ → Set)
     → (ℕ → ℕ → Set)
(S ⊎⊎ T) x y = (S x y) ⊎ (T x y)

path-weaken
    : {R S : ℕ → ℕ → Set}
    → (T : ℕ → ℕ → Set)
    → {x y : ℕ}
    → <Path R S x y
    → <Path R (S ⊎⊎ T) x y
path-weaken T (laststep x<y (inj₁ xRy)) = laststep x<y (inj₁ xRy)
path-weaken T (laststep x<y (inj₂ xSy)) = laststep x<y (inj₂ $ inj₁ xSy)
path-weaken {R} {S} T (addstep x<a a<y (inj₁ xRa) p) =
    addstep x<a a<y (inj₁ xRa) $ path-weaken T p
path-weaken {R} {S} T (addstep x<a a<y (inj₂ xSa) p) = 
    addstep x<a a<y (inj₂ $ inj₁ xSa) $ path-weaken T p

path-flatten-left
    : {R S T : ℕ → ℕ → Set}
    → {x y : ℕ}
    → <Path (<Path R S) T x y
    → <Path R (S ⊎⊎ T) x y
path-flatten-left {R} {S} {T} {x} {y} (laststep x<y (inj₁ p)) = path-weaken T p
path-flatten-left {R} {S} {T} {x} {y} (laststep x<y (inj₂ xTy)) = 
    laststep x<y (inj₂ $ inj₂ $ xTy)
path-flatten-left {R} {S} {T} {x} {y} (addstep x<a a<y (inj₁ q) p) = 
    cat (path-weaken T q) (path-flatten-left p)
path-flatten-left {R} {S} {T} {x} {y} (addstep x<a a<y (inj₂ xTa) p) =
    addstep x<a a<y (inj₂ $ inj₂ xTa) $ path-flatten-left p
    
--------------------------------------------------------------------------------
-- Tri-paths
--------------------------------------------------------------------------------
-- Use case: one wants to show that 
--      xSy ↔ <Path R T x y
-- but S is reflexive and symmetric.
-- The above expression works when x<y.
-- But <Path R T x y does not exist when x ≡ y or when y < x.
-- So the desired statement should be
--      xSy ↔   ((x < y) × <Path R T x y)
--            ⊎ x ≡ y
--            ⊎ ((y < x) × <Path R T y x)
-- The following type makes this easier to express.
-- Implementation note: it could also have used Data.Nat.Properties.<-cmp x y
-- to directly normalise to one of the three options.
-- But this seems only less convenient for proving such an '↔' theorem.
-- Also note: <Path R S x y implies x < y.
data TriPath (R S : ℕ → ℕ → Set) : ℕ → ℕ → Set where
    samedir   : {x y : ℕ} → x < y → <Path R S x y → TriPath R S x y
    emptypath : {x y : ℕ} → x ≡ y                 → TriPath R S x y
    oppdir    : {x y : ℕ} → y < x → <Path R S y x → TriPath R S x y

tripath-elim-<
    : {R S : ℕ → ℕ → Set}
    → {x y : ℕ}
    → TriPath R S x y
    → x < y
    → <Path R S x y
tripath-elim-< (samedir _ p) x<y = p
tripath-elim-< {x = x} (emptypath refl) x<y = ⊥-elim $ n≮n x x<y
tripath-elim-< {x = x} (oppdir y<x _) x<y = ⊥-elim $ n≮n x $ <-trans x<y y<x

-- Given a path in which some steps
-- may be of the form `TriPath R S z_i z_{1+i}`,
-- then we know these steps evaluate to a <Path
-- because z_i < z_{1+i} must hold.
nested-tripath-left
    : {R S T : ℕ → ℕ → Set}
    → {x y : ℕ}
    → <Path (TriPath R S) T x y
    → <Path (<Path R S) T x y
nested-tripath-left {R} {S} {T} {x} {y} (laststep x<y (inj₁ tri)) = 
    laststep x<y (inj₁ $ tripath-elim-< tri x<y)
nested-tripath-left {R} {S} {T} {x} {y} (laststep x<y (inj₂ xTy)) =
    laststep x<y (inj₂ xTy)
nested-tripath-left {R} {S} {T} {x} {y} 
    (addstep {x} {z} {y} x<z z<y (inj₁ tri) p) =
    addstep x<z z<y (inj₁ $ tripath-elim-< tri x<z) $ nested-tripath-left p
nested-tripath-left {R} {S} {T} {x} {y} 
    (addstep {x} {z} {y} x<z z<y (inj₂ xTz) p) =
    addstep x<z z<y (inj₂ xTz) $ nested-tripath-left p
    
