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
open import Data.Sum hiding (map)
open import Data.Unit
open import Data.Empty
open import Relation.Unary using (Pred ; Decidable)
open import Data.Product hiding (map)
open import Data.Fin hiding (_≤_ ; _≤?_ ; _<_ ; _>_ ; _+_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.List
open import Data.List.Properties using (reverse-++ ; unfold-reverse ; ∷ʳ-++)
open import Data.Vec hiding (restrict ; map ; _++_ ; reverse ; _∷ʳ_)
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
open import Relation.Nullary
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

---- Extract the vector encoded in a merging.
---- Only homogeneous implementation given, for when α and 
---- β have the same underlying type (to avoid all the annoying injections
---- that A⊎B would otherwise require),
---- (the heterogeneous case is not harder, I think, this project just did not
---- need it).
--compileVMerging
--    : {A : Set}
--    → {n m : ℕ} 
--    → {α : Vec A n} 
--    → {β : Vec A m} 
--    → VMerging α β
--    → Vec A (n + m)
--compileVMerging {α = α} {β = β} m = ?

compileMerging
    : {A : Set}
    → {α β : List A} 
    → Merging α β
    → List A
compileMerging {α = α} {β = β} (BetaTriv α) = α
compileMerging {α = α} {β = b ∷ β} (AlphaTriv b β) = b ∷ β
compileMerging {α = a ∷ α} {β = β} (AFirst a α β m) = a ∷ (compileMerging m)
compileMerging {α = α} {β = b ∷ β} (BFirst b α β m) = b ∷ (compileMerging m)

--------------------------------------------------------------------------------
-- Inverse operations to merging
--
-- Destroy a list into two lists, plus a proof that that can be merged
-- together to reconstruct the original list.
-- We destroy the list by filtering out all elements that satisfy a certain
-- predicate. For example, the usecase needed in Eser.Signal uses 
-- a list of type A, a function f : A → B and then a predicate of
-- the form (λ x → f x ≡ Z) for some fixed Z (see also `split` below).
--
-- In the stdlib, there is Data.List.partition which implements a similar
-- computation, but gives fewer proofs of its behaviour.
--------------------------------------------------------------------------------

-- #TODO: first define unmerge, then split is special case where the predicate
-- compares f-images with the max.

-- Data structure used by `unmerge` to pass invariants to recursive calls.
-- `rest` is supposed to be a suffix of L of elements still to be divided over α
-- and β, but it is a parameter instead of a field to satisfy the termination
-- checker (although, this way it also nicely makes explicit at type level 
-- that the algorithm always ends with nothing left to divide).
record UnmergeInvariants 
    {A : Set} 
    (L : List A) 
    (rest : List A) --^ Remaining elements in the reversed L.
    {P : Pred A _} 
    (Pdec : Decidable P) 
    : Set where
    constructor mkIvars
    field
        α : List (Σ[ a ∈ A ] P a)
        β : List (Σ[ a ∈ A ] ¬ (P a))
        m : Merging (map proj₁ α) (map proj₁ β)
        seen : List A
        H-seen : (reverse rest) ++ seen ≡ reverse L
        H-m : compileMerging m ≡ seen
open UnmergeInvariants

reverseLemma
    : {A : Set}
    → (a : A)
    → (K H : List A)
    → reverse (a ∷ K) ++ H ≡ reverse K ++ (a ∷ H)
reverseLemma a K H =
    begin 
    reverse (a ∷ K) ++ H
    ≡⟨ cong (λ L → L ++ H) (unfold-reverse a K) ⟩
    ((reverse K) ∷ʳ a) ++ H
    ≡⟨ ∷ʳ-++ (reverse K) a H  ⟩
    reverse K ++ (a ∷ H)
    ∎

unmergeRec
    : {A : Set} 
    → {L : List A} 
    → {P : Pred A _} 
    → {Pdec : Decidable P} 
    → (rest : List A) --^ Remaining elements in the reversed L.
    → (UnmergeInvariants L rest Pdec)
    → UnmergeInvariants L [] Pdec
unmergeRec [] iv@(mkIvars α β m seen H-seen H-m) = iv
unmergeRec {L = L} {Pdec = Pdec} (x ∷ rest) (mkIvars α β m seen H-seen H-m) with (Pdec x)
... | yes Px =
    let α' = (x , Px) ∷ α
    in
    let β' = β
    in
    let m' : Merging  (map proj₁ α') (map proj₁ β')
        m' = AFirst x (map proj₁ α) (map proj₁ β) m
    in
    let seen' = x ∷ seen
    in
    let H-seen' = trans (sym (reverseLemma x rest seen)) H-seen
    in
    let H-m' = cong (λ K → x ∷ K) H-m
    in
    let iv' : UnmergeInvariants L rest Pdec
        iv' = mkIvars α' β' m' seen' H-seen' H-m'
    in
    unmergeRec rest iv'
-- The 'no' case is almost identical to the 'yes' case,
-- except that we concatenate x to β instead of α.
... | no ¬Px = 
    let α' = α
    in
    let β' = (x , ¬Px) ∷ β
    in
    let m' : Merging  (map proj₁ α') (map proj₁ β')
        m' = BFirst x (map proj₁ α) (map proj₁ β) m
    in
    let seen' = x ∷ seen
    in
    let H-seen' = trans (sym (reverseLemma x rest seen)) H-seen
    in
    let H-m' = cong (λ K → x ∷ K) H-m
    in
    let iv' : UnmergeInvariants L rest Pdec
        iv' = mkIvars α' β' m' seen' H-seen' H-m'
    in
    unmergeRec rest iv'

-- NOTE: you'll probably want to reverse the 
-- input list before feeding it into unmerge!
-- See type of field `H-seen` in UnmergeInvariants: 
-- α and β are a partition of `reverse L` in the final output (when rest ≐ []).
unmerge 
    : {A : Set} 
    → (L : List A) 
    → {P : Pred A _} 
    → (Pdec : Decidable P) 
    → UnmergeInvariants L [] Pdec
unmerge [] Pdec = record { 
      α = []
    ; β = []
    ; m = BetaTriv []
    ; seen = []
    ; H-seen = refl 
    ; H-m = refl }
unmerge (x ∷ L) Pdec with Pdec x
... | yes Px = 
    let α = (x , Px) ∷ []
    in
    let β = []
    in
    let m : Merging (map proj₁ α) (map proj₁ β)
        m = BetaTriv (map proj₁ α)
    in
    let seen = x ∷ []
    in
    let H-seen = sym (reverse-++ seen L)
    in
    let H-m = refl
    in
    let iv : UnmergeInvariants (x ∷ L) L Pdec
        iv = mkIvars α β m seen H-seen H-m
    in
    unmergeRec L iv
... | no ¬Px =
    let α = []
    in
    let β = (x , ¬Px) ∷ []
    in
    let m : Merging (map proj₁ α) (map proj₁ β)
        m = AlphaTriv x []
    in
    let seen = x ∷ []
    in
    let H-seen = sym (reverse-++ seen L)
    in
    let H-m = refl
    in
    let iv : UnmergeInvariants (x ∷ L) L Pdec
        iv = mkIvars α β m seen H-seen H-m
    in
    unmergeRec L iv
