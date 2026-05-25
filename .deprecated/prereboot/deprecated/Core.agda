-- Module      : StreamGrids.Core
-- Description : Core definitions and functions
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
module StreamGrids.Core where

-- TODO: probably not all of these are needed.
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.Empty
open import Data.Fin hiding (_<_)
open import Function using (Inverseᵇ)
open import Data.List
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Nullary

-- The ones below are certainly needed.
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Linked using (Linked)
-- Implementation note: Data.List.Relation.Unary.Sorted.TotalOrder
-- gives `Sorted` instead of `Linked`, but it only works with reflexive
-- total orders, and _«_ is always irreflexive.

open import StreamGrids.Chain
open import StreamGrids.Card
open import StreamGrids.List

--------------------------------------------------------------------------------
-- StreamGrids
--
-- A StreamGrid is a Signoid plus a decidable equivalence relation between raw
-- terms of the Signoid.
-- The equivalences are explored coinductively (without actually needing
-- to use any coinduction mechanisms in Agda),
-- as the equivalence-decider gets as input a list of already explored
-- equivalences and needs to choose the next one.
--
-- A StreamGrid encodes a type with a decidable ≡ relation,
-- such that all `x ≡ y` equivalences are propositions (in the homotopy type
-- theoretic sense, so a StreamGrid is an hSet and `x ≡ y` and hProp).
--------------------------------------------------------------------------------

-- Canonical PrefixList of A: just [e(0), e(1), e(2), ..., e(n-1)].
prefix : {ℓ : Level.Level} {A : Set ℓ} → (e : ℕ → A) → (n : ℕ) → List A
prefix _ zero = []
prefix e (suc n) = (e (suc n)) ∷ (prefix e n)

---- A list `L` is an n-prefix of an enumeration of a type `A`
---- if 
---- (1) it contains the first n A-elements exactly once 
---- and
---- (2) it contains nothing else
--PrefixList : {A : Set _} → (e : ℕ → A) → (n : ℕ) → List A → Set _
--PrefixList e n = (prefix e n)  (fold L _++_ []) 

module SGStates
    {ℓ : Level.Level}
    {A : Set ℓ}
    {_«_ _⊂_ : Rel A ℓ}
    (S : Signoid _«_ _⊂_)
    where
    
    private 
        card : ℕ∞
        card = Signoid.numEl S

        -- Existing indices in the enumeration of A.
        -- That's ℕ if A has infinitely many elements
        -- and Fin n otherwise.
        SIndices : Set
        SIndices = cardToSet card

        -- The associated '<' relation on the indices of A.
        _<S_ : Rel SIndices 0ℓ
        _<S_ = cardTo< {Signoid.numEl S}

    -- All of the first n elements of A occur in L.
    IsPrefix : (L : List (List A)) → SIndices → Set _
    IsPrefix L n 
        = ((a : A) → ((Signoid.getIdx S a) <S n) → a ∈∈ L)
        --^ Every of the first n elements of A occurs in L...
        × ℕequalsCardToSetElem (flatLength L) n
        --^ ...and L has excatly n elements in total.

    -- #TODO: the above relation is, (after fixing L), an equivalence relation.
    -- If the need arises, prove refl sym trans.
        
    -- If two subterms x' < x are deemed equivalent in L,
    -- then any superterm must have been coerced along this x' ≈ x relation.
    -- (In case of constructors, we must have c(x) ≈ c(x') if we have x ≈ x').
    IsCongruence : (L : List (List A)) → Set _
    IsCongruence L 
        = (y x x' : A)
        → (x⊂y : x ⊂ y)
        → (x'«x : x' « x)
        → L ⊢ x' ≈ x
        → L ⊢ y ≈ proj₁ (Signoid.coercion S {y} {x} {x'} x⊂y x'«x)


    ---- Partially explored StreamGrid.
    ---- `Linked _«_` means just 'sorted according to _«_'.
    --SGState : Set ℓ
    --SGState = 
    --    Σ[ n ∈ SIndices ](
    --    Σ[ L ∈ List (List A)](
    --        (IsPrefix L n)
    --    ×
    --    (Linked _«_ (firstElem L))
    --    ×
    --    (All (λ as → Linked _«_ as) L)
    --    ×
    --    (IsCongruence L)
    --    )
    --    )

    -- Partially explored StreamGrid.
    -- The equivalences between the first n raw terms have been decided
    -- and form an congruence.
    -- Note: `Linked _«_` means just 'sorted according to _«_'.
    SGState : (n : SIndices) → Set ℓ
    SGState n = 
        Σ[ L ∈ List (List A)](
        (IsPrefix L n)
        ×
        (Linked _«_ (firstElem L))
        ×
        (All (λ as → Linked _«_ as) L)
        ×
        (IsCongruence L)
        )

    next : (n : SIndices) → (h : IsNotMax n) → A
    next n h = Signoid.enum S (cardToClipSuc n)

    -- Predicate expressing that the next element y to explore, 
    -- contains a subterm x that is equivalent to some smaller element x'.
    -- (This implies that, to preserve congruence consistenct,
    -- y must equal its x ≈ x' coercion in the only allowed successor state).
    -- #TODO: h is not used -- remove it?
    CongrConstrApplies
        : {n : SIndices}
        → (h : IsNotMax n) 
        --^ Otherwise the predicate makes no sense.
        → (q : SGState n)
        → Set _
    CongrConstrApplies {n} h (L , Lprops) 
        = (x x' : A) 
        → x ∈∈ L 
        → x' ∈∈ L 
        → x' « x 
        → (L ⊢ x' ≈ x )
        → x ⊂ next n h
    
    -- #TODO: h is not used -- remove it?
    addToIdx
        : {n : SIndices}
        → (q : SGState n)
        → (i : Indices (proj₁ q))
        → (h1 : IsNotMax n)
        --^ Proof that there actually exists a next element in A to add.
        → (h2 : ¬ (CongrConstrApplies h1 q))
        --^ Proof that the choice of equality for next element to add is not
        -- constrained by the congruence condition.
        → SGState (cardToClipSuc n)
    addToIdx {n} (L , pref , linked , subLinked , congr) i h1 h2 = 
        let subI = L ,, i in
        let L' = L [ i ]%= (λ as → (next n h1) ∷ as) in
        --^ Add next element to sublist with index i.
        let prefComplete = (λ a a<n → ?) in
        let pref' = (prefComplete , {! !}) in
        let linked' = ? in
        let subLinked' = ? in
        let congr' = ? in
        L' , pref' , linked' , subLinked' , congr'

    allFreeChoices 
        : {n : SIndices} 
        → SGState n 
        → List (SGState (cardToClipSuc n))
    allFreeChoices {n} q = ?

    sucStatesList 
        : {n : SIndices} 
        → SGState n  
        → List (SGState (cardToClipSuc n))
    -- Algorithm sketch:
    -- if <n is max>
    -- then
    --      <we're already done;
    --      return a list only containing the current state>
    -- elif <congruence constraint apply> 
    -- then 
    --      <singleton q a> 
    -- else 
    --      <allFreeChoices q a>
    -- where
    --      <a = nextToChoose q>
    -- Well, in practise both `singleton` and `allFreeChoices` know which
    -- element `a` must be. 
    sucStatesList q = ? 

    -- Wrapping the sucStatesList into a type.
    -- First I considered using some ListToType {B} {L : List B} → Set,
    -- but just using the indices avoids introducing new definitions
    -- and encodes exactly the same data anyway.
    SucStates : {n : SIndices} → SGState n → Set _
    SucStates q = Indices (sucStatesList q)



    ---- Allowed successor StreamGrid states.
    ---- These contain the same raw terms in the same nested lists,
    ---- but also the lexicographically next term in one allowed position.
    --sucState : 
    --    {ℓ : Level.Level}
    --    {A : Set ℓ}
    --    {_<_ _⊂_ : Rel A ℓ}
    --    {sig : Signoid _<_ _⊂_}
    --    → SGState sig 
    --    → List (SGState sig)
    --sucState {sig} s = ?

open SGStates


--SGDecider : 
--    {ℓ : Level.Level}
--    {A : Set ℓ}
--    {_<_ _⊂_ : Rel A ℓ}
--    → Signoid _<_ _⊂_
--    → Set ℓ
--SGDecider sig = (L : SGStates.sucState sig) → Σ[ s' ∈ SGStates.SGState sig ]( s' ∈ L )

--record StreamGrid 
--    {ℓ : Level.Level}
--    {A : Set ℓ}
--    {_<_ _⊂_ : Rel A ℓ}
--    : Set ℓ 
--    where
--    field
--        signoid : Signoid _<_ _⊂_
--        decider : SGDecider signoid
