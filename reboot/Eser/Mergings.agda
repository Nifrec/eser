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

{-# OPTIONS --allow-unsolved-metas #-}

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
open import Relation.Binary.PropositionalEquality.Properties renaming (setoid to ≡-setoid)
open ≡-Reasoning
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties using (∈-map⁺ ; ∈-map⁻)
open import Data.List.Membership.Setoid.Properties hiding (∈-map⁺ ; ∈-map⁻) 
    renaming (reverse⁻ to ∈-reverse⁻)
open import Data.List.Relation.Unary.All hiding (toList ; map)
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Relation.Binary.Pointwise.Base hiding (map)
open import Data.List.Properties using (reverse-++ ; reverse-involutive ; 
    unfold-reverse ; ∷ʳ-++ ; reverse-map ; map-∘)
open import Data.List.Relation.Binary.Pointwise.Properties renaming 
    (refl to Pointwise-refl)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (tail)
    renaming (there to Suffix-there ; here to Suffix-here)
open import Data.List.Extrema.Nat using (max ; xs≤max)
open import Data.Vec hiding (restrict ; map ; _++_ ; reverse ; _∷ʳ_ ; length)
open import Induction.WellFounded
open import Data.Nat.Induction using (<-Rec)
open import Data.Nat.Properties using (≤-refl ; n<1+n ; <-trans ; m<n⇒0<n 
    ; m≤n⇒m<n∨m≡n ; ≤-trans ; n≤1+n) -- ; ≤-<-trans ; n≤0⇒n≡0 
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
open import Eser.Logic using (elimCaseRight ; implCongrLeft ; implCongrRight)
open import Eser.Suffix using (_≼_ ; suffixElemInclusion)

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

compileMembership
    : {A : Set}
    → {α β : List A} 
    → (m : Merging α β)
    → (a : A)
    → a ∈ (compileMerging m) 
    → (a ∈ α) ⊎ (a ∈ β)
compileMembership {α} {β} (BetaTriv α₁) a a∈comp = inj₁ a∈comp
compileMembership {α} {β} (AlphaTriv b β₁) a a∈comp = inj₂ a∈comp
compileMembership (AFirst a₁ α β m) a (here px) = inj₁ (here px)
compileMembership (AFirst a₁ α β m) a (there a∈comp) = 
    let rec = compileMembership m a a∈comp
    in
    let a∈α→a∈a₁α : a ∈ α → a ∈ (a₁ ∷ α)
        a∈α→a∈a₁α a∈α = there a∈α
    in
    implCongrLeft rec a∈α→a∈a₁α
compileMembership (BFirst b α β m) a (here px) = inj₂ (here px)
compileMembership (BFirst b α β m) a (there a∈comp) =
    let rec = compileMembership m a a∈comp
    in
    let a∈β→a∈bβ : a ∈ β → a ∈ (b ∷ β)
        a∈β→a∈bβ a∈β = there a∈β
    in
    implCongrRight rec a∈β→a∈bβ

compileMembershipMapCongr
    : {A B : Set}
    → {α β : List A} 
    → (m : Merging α β)
    → (f : A → B)
    → (b : B)
    → b ∈ map f (compileMerging m) 
    → (b ∈ map f α) ⊎ (b ∈ map f β)
compileMembershipMapCongr {A} {B} {α} {β} m f b b∈MapFComp = 
    let meh : (Σ[ a ∈ A ] (a ∈ compileMerging m) × (b ≡ f a))
        meh = ∈-map⁻ f b∈MapFComp
    in
    let (a , a∈comp , b≡fa) = meh
    in
    let a∈α⊎a∈β : a ∈ α ⊎ a ∈ β
        a∈α⊎a∈β = compileMembership m a a∈comp
    in
    let a∈α→b∈fα : a ∈ α → b ∈ map f α
        a∈α→b∈fα a∈α = subst (λ x → x ∈ map f α) (sym b≡fa) (∈-map⁺ f a∈α)
    in
    let a∈β→b∈fβ : a ∈ β → b ∈ map f β
        a∈β→b∈fβ a∈β = subst (λ x → x ∈ map f β) (sym b≡fa) (∈-map⁺ f a∈β)
    in
    Data.Sum.map a∈α→b∈fα a∈β→b∈fβ a∈α⊎a∈β


-- Macro for getting length of the list encoded in a Merging.
mergelen
    : {A : Set}
    → {α β : List A} 
    → Merging α β
    → ℕ
mergelen = length ∘ compileMerging

-- Wrapping a Merging in a AFirst constructor increases the length of
-- the encoded list by 1. 
-- Obviously: the a : A argument is concatenated to the encoded list.
mergelenIncrementA
    : {A : Set}
    → {a : A}
    → {α β : List A} 
    → (m : Merging α β)
    → mergelen (AFirst a α β m) ≡ ℕ.suc (mergelen m)
mergelenIncrementA m = refl -- The RHS normalises to the LHS, so it's easy!

-- BFirst analog to mergelenIncrementA.
mergelenIncrementB
    : {A : Set}
    → {b : A}
    → {α β : List A} 
    → (m : Merging α β)
    → mergelen (BFirst b α β m) ≡ ℕ.suc (mergelen m)
mergelenIncrementB m = refl

-- Merging α with β results in a list L that is never shorter than α.
mergelenLemma
    : {A : Set}
    → {α β : List A} 
    → (m : Merging α β)
    → length α ≤ mergelen m
-- compileMerge m ≗ α in this case:
mergelenLemma {A} {α} {[]}     (BetaTriv α) = ≤-refl 
-- length α = 0 in this case:
mergelenLemma {A} {[]} {b ∷ β} (AlphaTriv b β) = z≤n
mergelenLemma {A} {a ∷ α} {β}  (AFirst a α β m) =
    let IH : length α ≤ mergelen m
        IH = mergelenLemma m
    in
    let sIHs : ℕ.suc (length α) ≤ ℕ.suc (mergelen m)
        sIHs = s≤s IH
    in
    let sIHs' : length (a ∷ α) ≤ ℕ.suc (mergelen m)
        sIHs' = sIHs -- These types are definitionally equal!
    in
    subst (λ z → length (a ∷ α) ≤ z) 
          (mergelenIncrementA {A} {a} {α} {β} m) 
          sIHs'
mergelenLemma {A} {α} {b ∷ β}  (BFirst b α β m) =
    let IH : length α ≤ mergelen m
        IH = mergelenLemma m
    in
    let H' : mergelen m ≤ ℕ.suc (mergelen m)
        H' = n≤1+n (mergelen m)
    in
    let H'' : mergelen m ≤ mergelen (BFirst b α β m)
        H'' = subst (λ z → mergelen m ≤ z) 
                    (mergelenIncrementB {A} {b} {α} {β} m) 
                    H'
    in
    ≤-trans IH H''
    
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
        α : List (Σ[ a ∈ A ] (P a) × (a ∈ L))
        β : List (Σ[ a ∈ A ] ¬ (P a) × a ∈ L)
        m : Merging (map proj₁ α) (map proj₁ β)
        seen : List A
        H-rest : rest ≼ L
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
unmergeRec [] iv = iv
unmergeRec {L = L} {Pdec = Pdec} (x ∷ rest) 
    (mkIvars α β m seen x∷rest≼L H-seen H-m) with (Pdec x)
... | yes Px =
    let x∈L : x ∈ L
        x∈L = suffixElemInclusion x∷rest≼L (Any.here refl)
    in
    let α' = (x , Px , x∈L) ∷ α
    in
    let β' = β
    in
    let m' : Merging  (map proj₁ α') (map proj₁ β')
        m' = AFirst x (map proj₁ α) (map proj₁ β) m
    in
    let seen' = x ∷ seen
    in
    let H-rest' : rest ≼ L
        H-rest' = Data.List.Relation.Binary.Suffix.Heterogeneous.tail x∷rest≼L
    in
    let H-seen' = trans (sym (reverseLemma x rest seen)) H-seen
    in
    let H-m' = cong (λ K → x ∷ K) H-m
    in
    let iv' : UnmergeInvariants L rest Pdec
        iv' = mkIvars α' β' m' seen' H-rest' H-seen' H-m'
    in
    unmergeRec rest iv'
-- The 'no' case is almost identical to the 'yes' case,
-- except that we concatenate x to β instead of α.
... | no ¬Px = 
    let x∈L : x ∈ L
        x∈L = suffixElemInclusion x∷rest≼L (Any.here refl)
    in
    let α' = α
    in
    let β' = (x , ¬Px , x∈L) ∷ β
    in
    let m' : Merging  (map proj₁ α') (map proj₁ β')
        m' = BFirst x (map proj₁ α) (map proj₁ β) m
    in
    let seen' = x ∷ seen
    in
    let H-rest' : rest ≼ L
        H-rest' = Data.List.Relation.Binary.Suffix.Heterogeneous.tail x∷rest≼L
    in
    let H-seen' = trans (sym (reverseLemma x rest seen)) H-seen
    in
    let H-m' = cong (λ K → x ∷ K) H-m
    in
    let iv' : UnmergeInvariants L rest Pdec
        iv' = mkIvars α' β' m' seen' H-rest' H-seen' H-m'
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
    ; H-rest = Data.List.Relation.Binary.Suffix.Heterogeneous.here []
    ; H-seen = refl 
    ; H-m = refl }
unmerge {A} (x ∷ L) {P} Pdec with Pdec x
... | yes Px = 
    let α : List (Σ[ a ∈ A ] (P a) × (a ∈ (x ∷ L)))
        α = (x , Px , Any.here refl) ∷ []
    in
    let β = []
    in
    let m : Merging (map proj₁ α) (map proj₁ β)
        m = BetaTriv (map proj₁ α)
    in
    let seen = x ∷ []
    in
    let H-rest : L ≼ (x ∷ L)
        H-rest = Suffix-there (Suffix-here (Pointwise-refl refl))
    in
    let H-seen = sym (reverse-++ seen L)
    in
    let H-m = refl
    in
    let iv : UnmergeInvariants (x ∷ L) L Pdec
        iv = mkIvars α β m seen H-rest H-seen H-m
    in
    unmergeRec L iv
... | no ¬Px =
    let α = []
    in
    let β = (x , ¬Px , here refl) ∷ []
    in
    let m : Merging (map proj₁ α) (map proj₁ β)
        m = AlphaTriv x []
    in
    let seen = x ∷ []
    in
    let H-rest : L ≼ (x ∷ L)
        H-rest = Suffix-there (Suffix-here (Pointwise-refl refl))
    in
    let H-seen = sym (reverse-++ seen L)
    in
    let H-m = refl
    in
    let iv : UnmergeInvariants (x ∷ L) L Pdec
        iv = mkIvars α β m seen H-rest H-seen H-m
    in
    unmergeRec L iv

decEqualsMax
    : {A : Set}
    → (L : List A)
    → (f : A → ℕ)
    → Decidable (λ a → f a ≡ max 0 (map f L))
decEqualsMax L f = λ a → f a Data.Nat.≟ (max 0 (map f L))

record UnmergeMaxOutp 
    {A : Set}
    (L : List A)
    (f : A → ℕ)
    : Set
    where
    constructor mkUnmMaxOutp
    field
        maxes  : List (Σ[ a ∈ A ] (f a ≡ max 0 (map f L)) × a ∈ L)
        others : List (Σ[ a ∈ A ] (f a < max 0 (map f L)) × a ∈ L)
        m : Merging (map proj₁ maxes) (map proj₁ others)
        H-m : compileMerging m ≡ L

notMaxMeansSmaller : (L : List ℕ) → (n : ℕ) → n ≢ max 0 L → n ∈ L → n < max 0 L
notMaxMeansSmaller L n n≢max n∈L = 
    let all≤max = xs≤max 0 L
    in
    let n≤max : n ≤ max 0 L
        n≤max = Data.List.Relation.Unary.All.lookup all≤max n∈L
    in
    let Hn : (n < max 0 L) ⊎ (n ≡ max 0 L) 
        Hn = m≤n⇒m<n∨m≡n n≤max
    in
    elimCaseRight Hn n≢max

-- #TODO: unused in the end
addMembership
    : {A : Set}
    → (L : List A)
    → List (Σ[ a ∈ A ] (a ∈ L))
addMembership L = mapWith∈ L (λ {a} a∈L → (a , a∈L))
 
reversePresvMax
    : (n : ℕ)
    → (L : List ℕ)
    → max n L ≡ max n (reverse L)
reversePresvMax n [] = refl
reversePresvMax n (x ∷ L) = {! !}

-- Substituting equal lists in a Merging does not change the encoded list
-- that the Merging constructs.
mergeSubst
    : {A : Set}
    → {L L' K K' : List A}
    → (m : Merging L K)
    → (hₗ : L ≡ L')
    → (hₖ : K ≡ K')
    → compileMerging m ≡ 
        compileMerging 
            (subst (λ v → Merging L' v) hₖ 
            (subst (λ v → Merging v K) hₗ m)
            )
mergeSubst {A} {L} {L} {K} {K} m refl refl = refl

mergeSubstLeft
    : {A : Set}
    → {L L' K : List A}
    → (m : Merging L K)
    → (h : L ≡ L')
    → compileMerging m ≡ compileMerging (subst (λ v → Merging v K) h m)
mergeSubstLeft {A} {L} {L} {K} m refl = refl

mergeSubstRight
    : {A : Set}
    → {L K K' : List A}
    → (m : Merging L K)
    → (h : K ≡ K')
    → compileMerging m ≡ compileMerging (subst (λ v → Merging L v) h m)
mergeSubstRight {A} {L} {K} {K} m refl = refl

-- If f ≈ g (homotopy) then map f L ≡ map g L for all lists L.
mapRewrHomot
    : {A B : Set}
    → {f g : A → B}
    → (f ≈ g)
    → (map f) ≈ (map g)
mapRewrHomot {f = f} {g = g} f≈g [] = refl
mapRewrHomot {f = f} {g = g} f≈g (a ∷ as) = 
    begin 
        map f (a ∷ as)
    ≡⟨  refl ⟩
        (f a) ∷ (map f as)
    ≡⟨ cong (λ b → b ∷ (map f as)) (f≈g a) ⟩
        (g a) ∷ (map f as)
    ≡⟨ cong (λ L → (g a) ∷ L) (mapRewrHomot f≈g as) ⟩
        (g a) ∷ (map g as)
    ≡⟨ refl ⟩
        map g (a ∷ as)
    ∎
    

-- When mapping a list of tuples under a function that acts as the id
-- on the first component, then the list of first projections remains the same.
mapProj₁Id
    : {A : Set}
    → {B C : A → Set}
    → (g : Σ[ a ∈ A ](B a) → Σ[ a ∈ A ](C a))
    → (proj₁ ∘ g) ≈ proj₁
    → (map proj₁ ∘ map g) ≈ (map proj₁)
mapProj₁Id g h L = 
    begin 
        map proj₁ (map g L) 
    ≡⟨  sym (map-∘ {g = proj₁} {f = g} L) ⟩
        map (proj₁ ∘ g) L
    ≡⟨  mapRewrHomot h L ⟩
        map proj₁ L
    ∎

-- Special case of unmerge:
-- given L : List A and a function f : A → ℕ,
-- let α be the elements in L whose f-images reach the maximum value (of map f
-- L), and β the other elements.
-- Note that α is never empty if L is not, but β might be.
unmergeMax
    : {A : Set} 
    → (L : List A) 
    → (f : A → ℕ)
    → UnmergeMaxOutp L f
-- This function is mostly a decorator around `unmerge`; it just recasts
-- the output of a special case of unmerge.
unmergeMax {A} L f =
    let Lᴿ = reverse L
    in
    let iv : UnmergeInvariants Lᴿ [] (decEqualsMax Lᴿ f)
        iv = unmerge Lᴿ (decEqualsMax Lᴿ f)
    in
    let sameMax : max 0 (map f Lᴿ) ≡ max 0 (map f L)
        sameMax = 
            begin 
                max 0 (map f Lᴿ)
            ≡⟨ cong (max 0) (reverse-map f L) ⟩
                max 0 (reverse (map f L))
            ≡⟨ sym (reversePresvMax 0 (map f L)) ⟩
                max 0 (map f L)
            ∎
    in
    let ∈-unreverse : {a : A} → (a ∈ Lᴿ) → a ∈ L
        ∈-unreverse a∈Lᴿ = ∈-reverse⁻ (≡-setoid _) a∈Lᴿ
    in
    let αToMaxes 
            : (Σ[ a ∈ A ] (f a ≡ max 0 (map f Lᴿ)) × a ∈ Lᴿ)
            → (Σ[ a ∈ A ] (f a ≡ max 0 (map f L)) × a ∈ L)
        αToMaxes (a , fa≡maxLᴿ , a∈Lᴿ) =
                          (a 
                          , subst (λ v → f a ≡ v) sameMax fa≡maxLᴿ 
                          , ∈-reverse⁻ (≡-setoid _) a∈Lᴿ
                          )
    in
    let HαToMaxes : (proj₁ ∘ αToMaxes) ≈ proj₁
        HαToMaxes (a , _ , _) = refl
    in
    let maxes : List (Σ[ a ∈ A ] (f a ≡ max 0 (map f L)) × a ∈ L)
        maxes = map αToMaxes (α iv)
    in
    let π₁maxesEq : (map proj₁ (α iv)) ≡ (map proj₁ maxes)
        π₁maxesEq = sym (mapProj₁Id αToMaxes HαToMaxes (α iv))
    in
    let βToOthers 
            : (Σ[ a ∈ A ] (f a ≢ max 0 (map f Lᴿ)) × a ∈ Lᴿ)
            → (Σ[ a ∈ A ] (f a < max 0 (map f L)) × a ∈ L)
        βToOthers = 
            let g = λ (b , ¬Pb , b∈L) → (b , notMaxMeansSmaller (map f Lᴿ) 
                    (f b) ¬Pb (∈-map⁺ f b∈L) , b∈L)
            in
            let g' = λ (a , fa<maxLᴿ , a∈Lᴿ) 
                    → (a 
                      , subst (λ v → f a < v) sameMax fa<maxLᴿ 
                      , ∈-reverse⁻ (≡-setoid _) a∈Lᴿ
                      )
            in
            (g' ∘ g)
    in
    let HβToOthers : (proj₁ ∘ βToOthers) ≈ proj₁
        HβToOthers (b , _ , _) = refl
    in
    let others : List (Σ[ a ∈ A ] (f a < max 0 (map f L)) × a ∈ L)
        others = map βToOthers (β iv)
    in
    let π₁othersEq = (map proj₁ (α iv)) ≡ (map proj₁ others)
        π₁othersEq = sym (mapProj₁Id βToOthers HβToOthers (β iv))
    in
    let merge : Merging (map proj₁ maxes) (map proj₁ others)
        merge =
            --let m' = subst (λ v → Merging (map proj₁ (α iv)) v) π₁othersEq (m iv)
            --in
            --subst (λ v → Merging v (map proj₁ others)) π₁maxesEq m'
            let m' = subst (λ v → Merging v (map proj₁ (β iv))) π₁maxesEq (m iv)
            in
            subst (λ v → Merging (map proj₁ maxes) v) π₁othersEq m'
    in
    let H-m' = compileMerging (m iv) ≡ L
        H-m' = 
            begin 
            compileMerging (m iv)
            ≡⟨  H-m iv ⟩
            [] ++ (seen iv)
            ≡⟨ H-seen iv ⟩
            reverse (reverse L)
            ≡⟨ reverse-involutive L ⟩
            L
            ∎
    in
    let H-m : compileMerging merge ≡ L
        H-m = trans (sym (mergeSubst (m iv) π₁maxesEq π₁othersEq)) H-m'
    in
    mkUnmMaxOutp maxes others merge H-m
