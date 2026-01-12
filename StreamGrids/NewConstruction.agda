-- Module      : StreamGrids.Construction
-- Description : Tools to construct types and relations via StreamGrids
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Termination for iterFromTill was an annoyance.
-- Imperically it is obvious:
-- ```
-- q := root h
-- for j = 0 to i
--      q := add decider's next choice to q
-- return q
-- ```
-- Doing it functional is a bit confusing. The distance from (idx q) to i
-- decreases every iteration, so that should give termination.
-- Initially I defined distance as
-- E.g., dist 1 4 ≐ 3 and dist 2 3 ≐ 1.
-- dist : {n m : ℕ} → n Data.Nat.< m → ℕ
-- dist {n} {m} n<m = ∣ n - m ∣
-- Noting that |_-_| is given in the stdlib Data.Nat.Base.
-- It was difficult to prove the required properties of this, when generalised
-- to work with finite sets (using toℕ to inject to ℕ).
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
open import StreamGrids.SubLogProperties
open import StreamGrids.Card
open import StreamGrids.Suffix
open import StreamGrids.Logic
open import StreamGrids.Fin
open import StreamGrids.Distance
open import StreamGrids.Addibles


module StreamGrids.NewConstruction where

module LowLvl
    {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    (S : Signoid _⊂_)
    where
    
    -- Instantiate the definitions of StreamGrids.States to our current Signoid.
    open SGStates {ℓ} {A} {_⊂_} S
    -- Also load abbreviations such as `Q`, `C`, `elToIdx`, etc.
    open SignoidShortcuts


    Decider : Set _
    Decider = (q : Q) → IsNotMax (idx q) → LegalChoices q

    -- Add one choice to a choicelog using a given decider.
    -- This chooses the equivalence class for the next element.
    nextState
        : Decider
        → (q : Q)
        → (h : IsNotMax (idx q))
        → Q
    nextState D q h = 
        let lc : LegalChoices q
            lc = D q h
        in
        (idxSuc h , UpdateNFList q h lc , choose q h lc)

    -- Extend a choicelog with the next choice accoring to the given Decider.
    addChoice
        : Decider
        → (q : Q)
        → (h : IsNotMax (idx q))
        → Σ[ q+ ∈ Q ] ((q ⋤ q+) × (idx q+ ≡ endoSuc h))
    addChoice D q h =
        let q+ : Q
            q+ = nextState D q h
        in
        let q⋤q+ : q ⋤ q+
            q⋤q+ = onechoice q h (D q h)
        in
        (q+ , q⋤q+ , refl)

iterTill : 
    {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    (S : Signoid _⊂_)
    → LowLvl.Decider S
    → (i : SGStates.SignoidShortcuts.C S)
    → Σ[ q ∈ SGStates.Q S ](SGStates.idx S q ≡ i)
iterTill S@(record {card = ∞}) D ℕ.zero =
    let nonempty = elToNonempty ℕ.zero
    in
    (SGStates.rootLog S nonempty , refl)
iterTill S@(record {card = ∞}) D (ℕ.suc i) = 
    let iterAlmostThere = Σ[ q ∈ SGStates.Q S ](SGStates.idx S q ≡ i)
        iterAlmostThere = iterTill S D i
    in
    let q = proj₁ iterAlmostThere
    in
    let h : IsNotMax i
        h = tt
    in
    let choiceAdded = (LowLvl.addChoice S D q h)
    in
    let meh : SGStates.idx S (proj₁ choiceAdded) ≡ endoSuc h
        meh = sym (proj₂ (proj₂ choiceAdded))
    in
    let geh : SGStates.idx S (proj₁ choiceAdded) ≡ ℕ.suc i
        geh = subst (λ x → ℕ.suc x) (proj₂ iterAlmostThere) meh
    in
    (proj₁  choiceAdded , meh)
iterTill S@(record {card = fin (ℕ.suc c)}) D Fin.zero = ?
iterTill S@(record {card = fin (ℕ.suc c)}) D (Fin.suc i) = ?

--iterTillSublog
--    : {ℓ : Level}
--    {A : Set ℓ}
--    {_⊂_ : Rel A ℓ}
--    (S : Signoid _⊂_)
--    → (D : LowLvl.Decider S)
--    → (i a : SGStates.SignoidShortcuts.C)
--    → iterTill i SGStates.⊑ iterTill (i + a)
--iterTillSublog

module GlobalNF
    {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    (S : Signoid _⊂_)
    where
    open SGStates {ℓ} {A} {_⊂_} S
    open LowLvl {ℓ} {A} {_⊂_} S
    open SignoidShortcuts

    -- Compute the normal form of any element of A.
    -- This is well defined, since every element will eventually
    -- be added to a choicelog in the inductively defined succession of
    -- choicelogs induces by a decider, at which point its normal form is well
    -- defined. Furthermore, the normal form will remain the same in successor
    -- choicelogs.
    nfGlobalIdx : Decider → C → C
    nfGlobalIdx D i = 
        let q : Q
            q = {! iterTill S D i !}
        in
        lookup (nflist q) (nfLastEl q)

    -- Element version of nfGlobalIdx (represent elements as A terms,
    -- instead of by their enumeration-index).
    nfGlobal : Decider → A → A
    nfGlobal D x =
        let ix : C
            ix = elToIdx x
        in
        idxToEl (nfGlobalIdx D ix)


    -- An element x is in NF w.r.t. a given decider D
    -- if it is will eventually the NFList of the choicelog 
    -- that the decider iteratively builds up.
    -- "Eventually" is the point in the enumeration corresponding to x,
    -- in which case x is either the last element in the NFList and stays there,
    -- or will never appear in the NFList.
    -- See `NormalFormTaxonomy.md` for a discussion of definitions of "isNF".
    IsListNF : Decider → C → Set
    IsListNF D i = {! i ∈ (nflist (iterTill S D i)) !}

    -- Element representation version of IsNF (i.o. enumeration-index
    -- representation).
    IsListNFEl : Decider → A → Set
    IsListNFEl D x = IsListNF D (elToIdx x)

    -- The predicate "IsListNF" is a proposition, i.e., proof-irrelevant,
    -- i.e., for given arguments it is either a singleton type xor uninhabited.
    IsNFIsAProp
        : (D : Decider)
        → (i : C)
        → Irrelevant (IsListNF D i)
    IsNFIsAProp = ?

    -- #TODO: this is still a proposition.
    -- It is using `Data.List.Membership.Setoid.Properties.unique⇒irrelevant`
    -- if one can show `Unique (nflist q)` for all `q : Q`,
    -- which ought to be easily provable.

    --nfGlobalIsNF
    --    : (D : Decider)
    --    → (i : C)
    --    → IsListNF D (nfGlobalIdx D i)
    --nfGlobalIsNF D i = 
    --    let q : Q
    --        q = {! iterTill S D i !}
    --    in
    --    let i* : C
    --        i* = (lookup (nflist q) (nfLastEl q)) -- Def of nfGlobalIdx
    --    in
    --    let goallist : List C
    --        goallist = nflist {! ( iterTill S D i* ) !}        
    --    in
    --    -- This gives membership in the NFList of q ≐ iterTill S D i,
    --    -- not in iterTill S D i*. The latter is required by definition of
    --    -- IsListNFlj
    --    let almost : (lookup (nflist q) (nfLastEl q)) ∈ (nflist q)
    --        almost = ∈-lookup {xs = nflist q} (nfLastEl q)
    --    in
    --    let desired : i* ∈ goallist
    --        desired = {! nflistEntry S {iterTill S D i*} {q} ? almost !}
    --        -- We know i*≤i. Case i*≡i is easy. Case i*<i can use
    --        -- nflistEntrySmaller. Only remains to show that the sublog q'
    --        -- must equal iterTill i*. This requires A4.
    --    in
    --    desired
    --    --let q : Q
    --    --    q = iterTill S D i
    --    --in
    --    --let check : nfGlobalIdx D i ≡ lookup (nflist q) (nfLastEl q)
    --    --    check = refl
    --    --in
    --    --let list : List C
    --    --    list = nflist (iterTill S D i)
    --    --in 
    --    --let desired : (nfGlobalIdx D i) ∈ list
    --    --    desired = sol
    --    --in
    --    --desired

open GlobalNF


-- The constructed quotient as a type, actually as an hSet.
-- The constructed equality relation is simply ≡ on this type.
data AsType 
    {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    (S : Signoid _⊂_)
    (D : LowLvl.Decider S) 
    : Set ℓ
    where
    fromNF : (x : A) → (IsListNFEl S D x) → AsType S D

quotientMap :
    {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    → (S : Signoid _⊂_)
    → (D : LowLvl.Decider S) 
    → (A → AsType S D)
quotientMap x = {! fromNF (nfGlobal x) !}
    
-- Two elements are related by the constructed equivalence relation
-- iff they have the same normal form.
data AsRelat
    {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    (S : Signoid _⊂_)
    (D : LowLvl.Decider S) 
    : Rel A ℓ
    where
    sameNF 
        : (x y : A) 
        → (nfGlobal S D x) ≡ (nfGlobal S D y) 
        → AsRelat S D x y
