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


module StreamGrids.Construction where

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

    -- Add choices to a choicelog q until the enumeration-index
    -- of the most recently chosen element is i.
    -- Of course, this is only possible if i has not been chosen in q already.
    -- To please the termination checker, the function also takes some fuel `f`
    -- that is at least as great as the number of choices still to add to q to
    -- get to i. This decreases every recursive call, because we extend q by one
    -- choice every time until we arrive at i.
    iterFromTill
        : Decider
        → (q : Q)
        → (i : C)
        → (idxq<i : cardTo< (idx q) i)
        → (f : ℕ)
        --^ "Fuel", is decreased every iteration, used to please Agda's
        -- termination checker.
        → (distCard {card} idxq<i) Data.Nat.≤ f
        → Σ[ q* ∈ Q ]( idx q* ≡ i )
    iterFromTill D q i idxq<i zero d = 
        let z<dist : ℕ.zero Data.Nat.< distCard {card} idxq<i 
            z<dist = distCardNonZero {card} idxq<i
        in
        let z<z : ℕ.zero Data.Nat.< ℕ.zero
            z<z = <-≤-trans z<dist d -- Note that d : dist < 0,
        in
        ⊥-elim (n≮n ℕ.zero z<z)
    iterFromTill D q i idxq<i (suc f) d 
        with (cardToDecidableEq card (idxSuc (biggerToIsNotMax idxq<i)) i)
    ... | yes p = let h = biggerToIsNotMax idxq<i in (nextState D q h , p)
    ... | no  idxq+≢i = 
        let h : IsNotMax (idx q)
            h = biggerToIsNotMax idxq<i
        in
        let q+ : Q
            q+ = nextState D q h
        in
        -- Note: idx q+ ≐ idxSuc h.
        let idxq+<i : cardTo< (idx q+) i
            -- See 'where' clause below for lemma
            idxq+<i = lemma idxq<i idxq+≢i 
        in
        let d+ : (distCard {card} idxq+<i) Data.Nat.≤ f
            d+ = s≤s⁻¹ ( subst (λ x → x Data.Nat.≤ ℕ.suc f) 
                               (sym (decrDist {card} idxq<i idxq+<i)) 
                               d
                       )
        in
        iterFromTill D q+ i idxq+<i f d+
        where
            lemma 
                : {c : ℕ∞}
                → { j k : cardToSet c}
                → (j<k : cardTo< j  k)
                → endoSuc (biggerToIsNotMax j<k) ≢ k
                → cardTo< (endoSuc (biggerToIsNotMax j<k)) k
            lemma {∞} {j} {k} j<k Sj≢k = 
                let Sj<k⊎Sj≡k = m≤n⇒m<n∨m≡n j<k 
                in
                let Sj<k : cardTo< (endoSuc (biggerToIsNotMax j<k)) k
                    Sj<k = elimCaseRight Sj<k⊎Sj≡k Sj≢k
                in
                Sj<k
            lemma {fin (suc c)} {j} {k} j<k Sj≢k =
                let h = biggerToIsNotMax j<k
                in
                let STj≡TSj : ℕ.suc (toℕ j) ≡ toℕ (endoSuc h)
                    STj≡TSj = sym (endoSucInjToNatSuc {c} {j} h)
                in
                let Sj<k⊎Sj≡k : toℕ (endoSuc h) Data.Nat.< toℕ k 
                                ⊎ toℕ (endoSuc h) ≡ toℕ k
                    Sj<k⊎Sj≡k = subst (λ x → x Data.Nat.< toℕ k ⊎ x ≡ toℕ k)
                        STj≡TSj (m≤n⇒m<n∨m≡n j<k)
                in
                -- We got Sj≢k, but we need toℕ(Sj)≢toℕ(k). Luckily, toℕ is
                -- injective.
                let TSj≢Tk : toℕ (endoSuc h) ≢ toℕ k
                    TSj≢Tk TSj≡Tk = Sj≢k (toℕ-injective TSj≡Tk)
                in
                let Sj<k : cardTo< (endoSuc h) k
                    Sj<k = elimCaseRight Sj<k⊎Sj≡k TSj≢Tk
                in
                Sj<k
-- The next function is not in a module environment because it needs
-- to pattern match on the cardinality of the Signoid.

-- Compute the choicelog containing the first i element
-- with choices made according to a given decider.
-- This starts from an empty choicelog, and hence constructs the root first.
-- (The constructor of the root requires a nonemptyness proof of the
-- enumerated set, but i already witnesses nonemptyness anyway).
iterTill : 
    {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    (S : Signoid _⊂_)
    → LowLvl.Decider S
    → SGStates.SignoidShortcuts.C S
    → SGStates.Q S
iterTill S@(record {card = ∞}) D ℕ.zero =
    let nonempty = elToNonempty ℕ.zero
    in
    SGStates.rootLog S nonempty
iterTill S@(record {card = fin (suc c)}) D Fin.zero =
    let nonempty = elToNonempty Fin.zero
    in
    SGStates.rootLog S nonempty
-- The next two cases have EXACTLY the same proof, but are difficult
-- to merge into one case since the i-arguments live in different sets
-- (namely ℕ vs Fin (suc card)).
-- #TODO: can this redundancy be reduced?
iterTill S@(record {card = ∞}) D i@(ℕ.suc i') = 
        let nonempty = elToNonempty i
        in
        let q : SGStates.Q S
            q = SGStates.rootLog S nonempty
        in
        let
            idxq<i : cardTo< {Signoid.card S} (SGStates.idx S q) i
            idxq<i = s≤s z≤n
        in
        let f : ℕ
            f = cardToℕ i
        in
        let |0,i|≤f : (distCard {Signoid.card S} idxq<i) Data.Nat.≤ f
            |0,i|≤f = s≤s (Data.Nat.Properties.≤-refl)
        in
        proj₁ (LowLvl.iterFromTill S D q i idxq<i f |0,i|≤f)
iterTill S@(record {card = fin (ℕ.suc c)}) D i@(Fin.suc i') =
        let nonempty = elToNonempty i
        in
        let q : SGStates.Q S
            q = SGStates.rootLog S nonempty
        in
        let
            idxq<i : cardTo< {Signoid.card S} (SGStates.idx S q) i
            idxq<i = s≤s z≤n
        in
        let f : ℕ
            f = cardToℕ i
        in
        let |0,i|≤f : (distCard {Signoid.card S} idxq<i) Data.Nat.≤ f
            |0,i|≤f = s≤s (Data.Nat.Properties.≤-refl)
        in
        proj₁ (LowLvl.iterFromTill S D q i idxq<i f |0,i|≤f)

iterTillIdx
    : {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    (S : Signoid _⊂_)
    → (D : LowLvl.Decider S)
    → (i : SGStates.SignoidShortcuts.C S)
    → proj₁ (iterTill S D i) ≡ i
iterTillIdx = ?
    
-- #TODO: this would be much more readable if we could just use infix _⋤_
-- and not all the SGStates.<sth> S notations. 
-- But we need to pattern match on the cardinality of S.
-- Maybe make the cardinality of S a parameter rather than a field?
iterTillSublog
    : {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    (S : Signoid _⊂_)
    → (D : LowLvl.Decider S)
    → (i : SGStates.SignoidShortcuts.C S)
    → (a : Addibles (Signoid.card S) i)
    → (SGStates._⊑_ S) (iterTill S D i) (iterTill S D (add (Signoid.card S) i a))
iterTillSublog S@(record {card = ∞}) D i ℕ.zero = 
    let lemma : i ≡ add ∞ i ℕ.zero
        lemma = sym (addℕzero i)
    in
    inj₁ (cong (λ x → iterTill S D x) lemma)
iterTillSublog S@(record {card = ∞}) D i (ℕ.suc a) = 
    let _⊑_ = SGStates._⊑_ S
    in
    let _⋤_ = SGStates._⋤_ S
    in
    let rec : (iterTill S D i) ⊑ (iterTill S D (add ∞ i a))
        rec = iterTillSublog S D i a
    in
    let lemma : add ∞ i (ℕ.suc a) ≡ ℕ.suc (add ∞ i a)
        lemma = ?
    in
    let q = iterTill S D (add ∞ i a)
    in
    let h : IsNotMax (add ∞ i a)
        h = tt -- Cuz we are doing the ℕ case where not max exists!
    in
    let lc : SGStates.LegalChoices S q
        lc = D q h
    in
    let s' : SGStates.SGState S (endoSuc {∞} {add ∞ i a} h) (SGStates.UpdateNFList S q h lc)
        s' = SGStates.choose q h lc
    in
    let q' : SGStates.Q S
        q' = (endoSuc {∞} {add ∞ i a} h , SGStates.UpdateNFList S q h lc , s')
    in
    let geh : q ⋤ q'
        geh = SGStates.onechoice q h lc
    in
    -- It should be provable that proj₁ (iterTill i) ≡ i always hold.
    -- Then in the next statement, both sides are `endoSuc h`.
    let keypointIdx : proj₁ q' ≡ proj₁ (iterTill S D (endoSuc {∞} {add ∞ i a} h))
        --keypoint = cong (λ x → (x , (SGStates.UpdateNFList S q h lc) , s')) ?
        keypointIdx = iterTillIdx S D (endoSuc h)
    in
    let keypointList : proj₂ q' ≡ proj₂ (iterTill S D (endoSuc {∞} {add ∞ i a} h))
        keypointList = refl
    in
    let meh : (iterTill S D (add ∞ i a)) ⋤ iterTill S D (ℕ.suc (add ∞ i a))
        -- Problem: Agda does not see that this increases the index of the state
        -- by 1. 
        meh = ? --SGStates.onechoice ? ? ?
    in
    ?
iterTillSublog S@(record {card = fin zero}) D ()
iterTillSublog S@record { card = (fin (ℕ.suc c))} D Fin.zero Fin.zero = inj₁ refl
iterTillSublog S@record { card = (fin (ℕ.suc c))} D Fin.zero (Fin.suc a) = {!  !}
iterTillSublog S@record { card = (fin (ℕ.suc c))} D (Fin.suc i) a = {! !}

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
            q = iterTill S D i
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
    IsListNF D i = i ∈ (nflist (iterTill S D i))

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

    nfGlobalIsNF
        : (D : Decider)
        → (i : C)
        → IsListNF D (nfGlobalIdx D i)
    nfGlobalIsNF D i = 
        let q : Q
            q = iterTill S D i
        in
        let i* : C
            i* = (lookup (nflist q) (nfLastEl q)) -- Def of nfGlobalIdx
        in
        let goallist : List C
            goallist = nflist ( iterTill S D i* )
        in
        -- This gives membership in the NFList of q ≐ iterTill S D i,
        -- not in iterTill S D i*. The latter is required by definition of
        -- IsListNFlj
        let almost : (lookup (nflist q) (nfLastEl q)) ∈ (nflist q)
            almost = ∈-lookup {xs = nflist q} (nfLastEl q)
        in
        let desired : i* ∈ goallist
            desired = {! nflistEntry S {iterTill S D i*} {q} ? almost !}
            -- We know i*≤i. Case i*≡i is easy. Case i*<i can use
            -- nflistEntrySmaller. Only remains to show that the sublog q'
            -- must equal iterTill i*. This requires A4.
        in
        desired
        --let q : Q
        --    q = iterTill S D i
        --in
        --let check : nfGlobalIdx D i ≡ lookup (nflist q) (nfLastEl q)
        --    check = refl
        --in
        --let list : List C
        --    list = nflist (iterTill S D i)
        --in 
        --let desired : (nfGlobalIdx D i) ∈ list
        --    desired = sol
        --in
        --desired

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
