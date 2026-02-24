-- Module      : Eser.Mergings
-- Description : Combinatorial tools for 'merging' two lists into one.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- This file is about the number of ways to merge two lists,
-- of length n and m respectively, into one list,
-- without changing the relative order of the elements in each list.
-- E.g. the mergings of [a a'] with [b b'] are
-- [a a' b b']
-- [a b a' b']
-- [a b b' a']
-- [b a a' b']
-- [b a b' a']
-- [b b' a a']

-- #TODO: these imports are copied, not all used; remove unused imports.
open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties using (¬-not ; not-¬)
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Unary using (Decidable)
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product
--open import Relation.Binary.Structures
open import Data.Fin hiding (_≤_ ; _≤?_ ; _<_ ; _>_ ; _+_)
open import Data.List
open import Data.Vec hiding (restrict)
open import Induction.WellFounded
open import Data.Nat.Induction using (<-Rec)
open import Data.Nat.Properties using (≤-refl ; n<1+n ; <-trans ; m<n⇒0<n) --; ≤-trans ; ≤-<-trans ; n≤0⇒n≡0 
--                                       ; n≤1+n ; m≤n⇒m<n∨m≡n ; _≤?_ ; ≰⇒≥)
--open import Data.Fin.Properties using (toℕ<n)
--open import Relation.Nullary -- Needed for with-abstractions on decidable ≡.
open import Function hiding (_↔_)

--open import Eser.Logic using (elimCaseLeft ; elimCaseRight)
--open import Relation.Nullary
--open ≡-Reasoning
--open import Data.Nat.Properties
--open import Data.Fin
--open import Data.Fin.Properties
--open import Data.Fin.Induction
--open import Data.Empty
--open import Data.List
--open import Data.List.Relation.Unary.AllPairs using (AllPairs)
--open import Data.List.Relation.Unary.All using (All)
--open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix)
--open import Data.List.Membership.Propositional using (_∈_ ; _∉_ )
--open import Data.List.Membership.Propositional.Properties using (∈-lookup)
--open import Data.List.Relation.Unary.Any using (Any)

open import Eser.Definitions using (_≈_ ; indices ; _≃_)

module Eser.Mergings where

-- Compute number of ways to merge two lists.
numMergings : ℕ → ℕ → ℕ
-- If one list is empty, there is only one choice.
numMergings 0 m = 1
numMergings n 0 = 1
-- When mergings a∷α with b∷β, there are two options:
-- (1) Either put a as the first element of the merging.
--      Then it remains to merge α with b∷β, so NM(n, m+1) mergings possible.
-- (2) Xor put a after b. Then it remains to merge a∷α with β.
--      So NM(n+1, m) mergings possible.
-- Clearly those two cases are mutually exclusive since only one of a and b can
-- be put first.
numMergings (suc n) (suc m) = numMergings n (ℕ.suc m) + numMergings (ℕ.suc n) m

-- Inductive type explicitly encoding all possible mergings.
-- Note how it corresponds to the explanation of the recursive case of
-- numMergings.
data Merging {A : Set} {B : Set} : List A → List B → Set where
    -- Also captures the case Merging [] []
    BetaTriv : (α : List A) → Merging α []
    -- Does NOT capture the case Merging [] []
    AlphaTriv : (b : B) → (β : List B) → Merging [] (b ∷ β)
    -- Take a merging γ of α and β and extend it to (a ∷ γ).
    AFirst : (a : A) → (α : List A) → (β : List B) → Merging α β
        → Merging (a ∷ α) β
    -- Take a merging γ of α and β and extend it to (b ∷ γ).
    BFirst : (b : B) → (α : List A) → (β : List B) → Merging α β
        → Merging α (b ∷ β)

-- Same as `Merging`, but the arguments are now vectors.
VMerging 
    : {A B : Set}
    → {n m : ℕ} 
    → (α : Vec A n) 
    → (β : Vec B m) 
    → Set
VMerging α β = Merging (toList α) (toList β)

MergingFinTheo
    : {A B : Set}
    → (n m : ℕ) 
    → (α : Vec A n) 
    → (β : Vec B m) 
    → VMerging α β ≃ Fin (numMergings n m)
MergingFinTheo n m α β = ?

-- Extract the vector encoded in a merging.
-- Only homogeneous implementation given, for when α and 
-- β have the same underlying type (to avoid all the annoying injections
-- that A⊎B would otherwise require),
-- (the heterogeneous case is not harder, I think, this project just did not
-- need it).
compileVMerging
    : {A : Set}
    → {n m : ℕ} 
    → {α : Vec A n} 
    → {β : Vec A m} 
    → VMerging α β
    → Vec A (n + m)
compileVMerging {α = α} {β = β} m = ?

compileMerging
    : {A : Set}
    → {α β : List A} 
    → Merging α β
    → List A
compileMerging {α = α} {β = β} (BetaTriv α) = α
compileMerging {α = α} {β = b ∷ β} (AlphaTriv b β) = b ∷ β
compileMerging {α = a ∷ α} {β = β} (AFirst a α β m) = a ∷ (compileMerging m)
compileMerging {α = α} {β = b ∷ β} (BFirst b α β m) = b ∷ (compileMerging m)
