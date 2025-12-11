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
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any using (Any)
open import Level

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

