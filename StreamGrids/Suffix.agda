-- Module      : StreamGrids.Suffix
-- Description : Generic properties of suffices of lists.
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Note: what the Agda standard library calls a 'suffix' L' of a list L
-- is a sublist whose LEFT endpoint is aligned with that of L
--
--  L' :        [*******]
--  L  : [**************]
--
--  I.e.,
--  They define a suffix of 
--      a_n ∷ a_{n-1} ∷ a_{n-2} ∷ ... ∷ a_0 ∷ []
--      a_m ∷ a_{m-1} ∷ a_{m-2} ∷ ... ∷ a_0 ∷ []
--  with m ≤ n.
--  (If the right endpoints are aligned, which are the most recent element
--  added, then they call it a 'prefix'.
--
--  Warning: both `Suffix` and `Any` have constructors `here` and `there`,
--  and `_∈_` is defined in terms of `Any`.
--  When typing `here x≡y` to destruct a proof of `x ∈ (y ∷ ys)`,
--  Agda will complain it is of the wrong datatype.
--  Use `Any.here` instead and all is fine.

module StreamGrids.Suffix where

open import Data.List.Relation.Binary.Suffix.Heterogeneous
open import Data.List.Relation.Binary.Pointwise
open import Data.List.Membership.Propositional using (_∈_ ; _∉_)
open import Data.List
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any using (Any)
open import Level
open import Relation.Binary
open import Relation.Binary.Definitions
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Binary.Pointwise.Properties renaming (refl to Pointwise-refl)
open import Data.List.Relation.Binary.Suffix.Heterogeneous.Properties 
    renaming (trans to Suffix-trans)

-- If two lists are pointwise equal then every element of the one list
-- is also in the other list. 
-- This function also points to the same index.
pointwEqualElemInclusion
    : {ℓ : Level}
    → {A : Set ℓ}
    → {x : A}
    → {L' L : List A}
    → (Pointwise _≡_ L' L)
    → x ∈ L'
    → x ∈ L
pointwEqualElemInclusion {ℓ} {A} {x} 
    {y ∷ ys} {z ∷ zs} (y≡z ∷ p') (Any.here x≡y) =
    let x≡z = trans x≡y y≡z in
    Any.here x≡z
pointwEqualElemInclusion {ℓ} {A} {x} 
    {y ∷ ys} {z ∷ zs} (y≡z ∷ p') (Any.there x∈ys) =
    Any.there (pointwEqualElemInclusion {ℓ} {A} {x} {ys} {zs} p' x∈ys)

-- If L' is the suffix of L then L has every element of L'
-- (at a shifted index).
suffixElemInclusion 
    : {ℓ : Level}
    → {A : Set ℓ}
    → {x : A}
    → {L' L : List A}
    → (Suffix _≡_ L' L)
    → x ∈ L'
    → x ∈ L
suffixElemInclusion {ℓ} {A} {x} {L'} {L} (here L'≈L) x∈L' = 
    pointwEqualElemInclusion {ℓ} {A} {x} {L'} {L} L'≈L x∈L'
suffixElemInclusion {ℓ} {A} {x} {L'} {z ∷ zs} (there L'≼ys) x∈L' = 
    Any.there (suffixElemInclusion {ℓ} {A} {x} {L'} {zs} L'≼ys x∈L')

-- An index i in a suffix L' also exists as index in the superlist L
-- (and has the same element, but that's not proven here).
-- BUT elements are enumerated from newest to oldest (left-to-right)
-- and a suffix is a right end, so some conversion is needed!
suffixIdxInclusion 
    : {ℓ : Level}
    → {A : Set ℓ}
    → {L' L : List A}
    → (Suffix _≡_ L' L)
    → Indices L'
    → Indices L
suffixIdxInclusion = ?

-- Syntax L' ≼ L means that L' is a suffix of L.
PropEqSuffix : {ℓ : Level} {A : Set ℓ} (L' L : List A) → Set ℓ
PropEqSuffix {ℓ} {A} L' L = Suffix {A = A} (_≡_) L' L

_≼_ : {ℓ : Level } {A : Set ℓ} → Rel (List A) ℓ
(_≼_) {ℓ} {A} L' L = PropEqSuffix L' L

≼-refl : {ℓ : Level } {A : Set ℓ} → Reflexive (_≼_ {ℓ} {A})
≼-refl {L} = Suffix.here (Pointwise-refl _≡_.refl)

≼-trans : {ℓ : Level } {A : Set ℓ} → Transitive (_≼_ {ℓ} {A})
≼-trans = Suffix-trans trans

-- A suffix of a list has no element that the whole list doesn't have.
notInListThenNotInSuffix
    : {A : Set}
    → {a : A}
    → {L' L : List A}
    → L' ≼ L
    → a ∉ L
    → a ∉ L'
notInListThenNotInSuffix {A} {L'} {L} L'≼L a∉L a∈L' = 
    ⊥-elim (a∉L (suffixElemInclusion L'≼L a∈L'))
