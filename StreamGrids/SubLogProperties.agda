-- Module      : StreamGrids.SubLogProperties
-- Description : Additional properties of the ⋤ relation.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Theorems about the _⋤_ (subchoicelog-relation) defined
-- in StreamGrids.States.

open import Level
open import Relation.Binary hiding (Irrelevant)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Fin
open import Data.Fin.Properties
open import Data.Unit
open import Data.Empty
open import Data.List
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix)
open import Data.List.Membership.Propositional using (_∈_ ; _∉_ )
open import Data.List.Membership.Propositional.Properties using (∈-lookup)
open import Data.List.Relation.Unary.Any using (Any)

-- Certainly used local imports.
open import StreamGrids.States
open import StreamGrids.Signoid
open import StreamGrids.Card
open import StreamGrids.Suffix
open import StreamGrids.Logic
open import StreamGrids.Fin
open import StreamGrids.Distance


module StreamGrids.SubLogProperties
    {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    (S : Signoid _⊂_)
    where
    
    -- Instantiate the definitions of StreamGrids.States to our current Signoid.
    open SGStates {ℓ} {A} {_⊂_} S
    -- Also load abbreviations such as `Q`, `C`, `elToIdx`, etc.
    open SignoidShortcuts



    -- Scroll down to `nflistEntry` below, this `private` block
    -- just gathers some auxiliary lemmas for this theorem.
    private
        P : Q → Set ℓ
        P q = (q' : Q) → (q' ⋤ q) → (idx q' ∈ nflist q) → (idx q' ∈ nflist q')

        -- It is possible to change the type of j<i' to j≤i' and use this lemma
        -- also for the onestep base cases of nflistEntryRec.
        -- Currently this did not have high priority.
        onestepLemma
            : (i' j : C)
            → (j<i' : cardTo< j i')
            → (L' : NFList)
            → (s' : SGState i' L')
            → (h : IsNotMax i')
            → (lc : LegalChoices (i' , L' , s'))
            → j ∈ UpdateNFList (i' , L' , s') h lc
            → j ∈ L'
        onestepLemma i' j j<i' L' s' h (newNF _ _ _) (Any.here j≡idxSucH) =
                let i'<idxSucH = endoSucBigger h
                in
                let j<idxSucH = cardTo<Trans {card} j<i' i'<idxSucH
                in
                ⊥-elim (<And≡Impossible j<idxSucH j≡idxSucH)    
        onestepLemma i' j j<i L' s' h (newNF _ _ _) (Any.there i'∈L') = i'∈L'
        onestepLemma i' j j<i L' s' h (freeChoice _ _ _ _) i'∈L = i'∈L
        onestepLemma i' j j<i L' s' h (forcedChoice _ _ _) i'∈L = i'∈L

        nflistEntryRec
            : (q : Q)
            → ((q₁ : Q) → (q₁ ⋤ q) → P q₁)
            → P q
        -- In the newNF case, L has one additional element on top of L',
        -- which is idxsuc h, or intuitively, just 1+i. Obviously idxsuc h > i,
        -- so i cannot be this additional element.
        nflistEntryRec q recurse q'@(i' , L' , s') 
            (onechoice q' h (newNF s h₁ x)) 
            (Any.here i'≡idxsuch) = 
                let i'<idxsuch = endoSucBigger h
                in
                ⊥-elim (<And≡Impossible i'<idxsuch i'≡idxsuch)    
        nflistEntryRec q recurse q'@(i' , L' , s') 
            (onechoice q' h (newNF s h₁ x)) 
            (Any.there i'∈L') = i'∈L'
        -- In the next two cases it holds that L ≐ L', so that's easy:
        nflistEntryRec q recurse q'@(i' , L' , s') 
            (onechoice q' h (freeChoice s h₁ x x₁)) i'∈L = i'∈L
        nflistEntryRec q recurse q'@(i' , L' , s') 
            (onechoice q' h (forcedChoice s h₁ x)) i'∈L = i'∈L
        -- The multi-step case: q extends q₁.
        -- A recursive call gives that i'∈L₁ then i'∈L'.
        -- Showing that i'∈L₁ can be done again by onestep reasoning.
        nflistEntryRec q recurse q'@(i' , L' , s') 
                       q'⋤q@(multichoice q' q₁ q'⋤q₁ h lc) i'∈L =
            let q₁⋤q : q₁ ⋤ q
                q₁⋤q = onechoice q₁ h lc
            in
            let rec : i' ∈ (nflist q₁) → i' ∈ L'
                rec = recurse q₁ q₁⋤q q' q'⋤q₁
            in
            let i'<idxq₁ : cardTo< i' (idx q₁)
                i'<idxq₁ = sublogSmallerIdx q'⋤q₁
            in
            let i'∈L₁ : i' ∈ (nflist q₁)
                i'∈L₁ = onestepLemma (idx q₁) (i') i'<idxq₁ 
                                     (nflist q₁) (sgstate q₁) h lc i'∈L
            in
            rec i'∈L₁



    -- An element can enter a NFList in a succession of choicelogs exactly once,
    -- at the stage where its enumeration-index is the choicelog-index,
    -- and thereafter stays in the NFList forever
    -- (or never enter it).
    -- Conversely, when present in a successor's state NFList,
    -- then it must have been present in the list of its own subchoicelog.
    nflistEntry
        : {q' q : Q}
        → (q' ⋤ q)
        → (idx q') ∈ (nflist q)
        → (idx q') ∈ (nflist q')
    nflistEntry {q'} {q} q'⋤q idxq'∈L = ⋤-rec P nflistEntryRec q q' q'⋤q idxq'∈L

    nflistEntrySmaller
        : (q : Q)
        → (j : C)
        → (j<i : cardTo< j (idx q))
        → j ∈ (nflist q)
        → j ∈ nflist (proj₁ (getSubLog q j j<i))
    nflistEntrySmaller q j j<i j∈L = 
        let (q' , q'⋤q , j≡idxq') = getSubLog q j j<i
        in
        let idxq'∈L : idx q' ∈ nflist q
            idxq'∈L = subst (λ x → x ∈ nflist q) j≡idxq' j∈L
        in
        let meh : idx q' ∈ nflist q'
            meh = nflistEntry {q'} {q} q'⋤q idxq'∈L
        in
        subst (λ x → x ∈ nflist q') (sym j≡idxq') meh

    -- The graph of the relation ⋤ has the form of a tree.
    -- But the indices (the proj₁ images of Q elements) of states
    -- correspond to their height, and consequently,
    -- every state has *exactly one* predecessor of a given height smaller than
    -- its own.
    predecUnique
        : {q q₁ q₂ : Q}
        → q₁ ⋤ q
        → q₂ ⋤ q
        → idx q₁ ≡ idx q₂
        → q₁ ≡ q₂
    predecUnique q q₁ q₂ q₁⋤q q₂⋤q i₁≡i₂ = ?

