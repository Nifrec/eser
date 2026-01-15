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
open import Data.Fin.Induction
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
    let idx = SGStates.idx S
    in
    let iterAlmostThere = Σ[ q ∈ SGStates.Q S ](idx q ≡ i)
        iterAlmostThere = iterTill S D i
    in
    let q = proj₁ iterAlmostThere
    in
    let idxq = idx q
    in
    let idxq≡i : idxq ≡ i
        idxq≡i = proj₂ iterAlmostThere
    in
    -- In context of natural numbers n : ℕ, it holds that IsNotMax n ≐ ⊤.
    -- So tt can both be typed as `IsNotMax idxq` and `IsNotMax i`.
    -- This is exploited in the `cong` below.
    let h : IsNotMax idxq 
        h = tt
    in
    let choiceAdded = (LowLvl.addChoice S D q h)
    in
    let H : idx (proj₁ choiceAdded) ≡ ℕ.suc i
        H = begin
                idx (proj₁ choiceAdded) 
                ≡⟨ sym (proj₂ (proj₂ choiceAdded)) ⟩
                endoSuc {∞} {idxq} h
                ≡⟨ cong (λ x → endoSuc {∞} {x} h) idxq≡i  ⟩
                endoSuc {∞} {i} h 
                ≡⟨ endoSucNatSuc h ⟩
                ℕ.suc i
            ∎
    in
    (proj₁  choiceAdded , H)
-- Finite set case.
-- While i ≐ Fin.zero can be done like ℕ.zero,
-- the case Fin.suc i gave the following problem:
-- Problem: C ≐ Fin (suc c) but i lives in Fin c instead.
-- So we must use inject₁ i in the recursive call, which demands the input
-- to be in C. But `inject₁ i` is NOT a direct subterm of `Fin.suc i`,
-- so the termination checker does not like this.
-- Luckily, it holds that Fin.< is well-founded and
-- `inject₁ i < Fin.suc i`, which proves termination.
iterTill S@(record {card = fin (ℕ.suc c)}) D =
    Data.Fin.Induction.<-weakInduction P zeroCase recurseCase
    where
        X = Fin (ℕ.suc c)
        P : (i : X) → Set _
        P i = Σ[ q ∈ SGStates.Q S ](SGStates.idx S q ≡ i)
        zeroCase : P Fin.zero
        zeroCase = 
            let nonempty = elToNonempty Fin.zero
            in
            (SGStates.rootLog S nonempty , refl)
        recurseCase : ∀ i → (P (inject₁ i)) → P (Fin.suc i)
        recurseCase i rec =
            let lemma : i Data.Fin.< Fin.suc i 
                lemma = Data.Nat.Properties.n<1+n (toℕ i)
            in
            let lemma' : ℕ.suc (toℕ (inject₁ i)) ≡ ℕ.suc (toℕ i)
                lemma' = cong ℕ.suc (Data.Fin.Properties.toℕ-inject₁ i)
            in
            let inj-i<Si : (inject₁ i) Data.Fin.< (Fin.suc i)
                inj-i<Si = subst (λ x → x Data.Nat.≤ toℕ (Fin.suc i)) 
                                 (sym lemma') lemma
            in
            let idx = SGStates.idx S
            in
            let iterAlmostThere = Σ[ q ∈ SGStates.Q S ](idx q ≡ inject₁ i)
                iterAlmostThere = rec 
            in
            let q = proj₁ iterAlmostThere
            in
            let idxq = idx q
            in
            let idxq≡i : idxq ≡ inject₁ i
                idxq≡i = proj₂ iterAlmostThere
            in
            let h : IsNotMax (inject₁ i) 
                h = biggerToIsNotMax inj-i<Si
            in
            let h' : IsNotMax (idxq)
                h' = subst IsNotMax (sym idxq≡i) h
            in
            let choiceAdded = (LowLvl.addChoice S D q h')
            in
            let H : idx (proj₁ choiceAdded) ≡ Fin.suc i
                H = begin
                        idx (proj₁ choiceAdded) 
                        ≡⟨ sym (proj₂ (proj₂ choiceAdded)) ⟩
                        endoSuc h'
                        ≡⟨ endoSucPresvEquality idxq≡i h' h ⟩
                        endoSuc h 
                        ≡⟨ endoSucFinSuc i h ⟩
                        Fin.suc i
                    ∎
            in
            (proj₁ choiceAdded , H)


-- Intuition: if i ≤ j then (iterTill i) ⊑ (iterTill j).
-- But proving this requires induction, so we prove
-- (iterTill i) ⊑ (iterTill (i + a)) for "all a we can still add to i"
-- by induction on a.
-- The type of such a's is all of ℕ in case of infinite cardinality, 
-- and a finite set in case A is finite; in both cases we can indeed to
-- induction on a.
iterTillSublog
    : {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    (S : Signoid _⊂_)
    → (D : LowLvl.Decider S)
    → (i : SGStates.SignoidShortcuts.C S)
    → (a : Addibles (Signoid.card S) i)
    → SGStates._⊑_ S (proj₁ (iterTill S D i)) 
                     (proj₁ (iterTill S D (add (Signoid.card S) i a)))
iterTillSublog {ℓ} S@(record {card = ∞}) D i ℕ.zero = 
    let P : SGStates.SignoidShortcuts.C S → Set ℓ
        P x = SGStates._⊑_ S (proj₁ (iterTill S D i)) 
                             (proj₁ (iterTill S D x))
    in
    subst P (sym (addℕzero i)) (inj₁ refl)
iterTillSublog S@(record {card = ∞}) D i (ℕ.suc a) = 
    let _⊑_ = SGStates._⊑_ S
    in
    let _⋤_ = SGStates._⋤_ S
    in
    let q = (proj₁ (iterTill S D i)) 
    in
    let q+ = (proj₁ (iterTill S D (add (Signoid.card S) i a)))
    in
    let q⊑q+ : q ⊑ q+
        q⊑q+ = iterTillSublog S D i a
    in
    -- Last iteration step that iterTill performs, when inspecting its
    -- implementation.
    let lastStep = LowLvl.addChoice S D q+ tt
    in
    let q++ = proj₁ lastStep
    in
    -- We also know idx q+ = endoSuc idx q
    let q+⋤q++ : q+ ⋤ q++
        q+⋤q++ = proj₁ (proj₂ lastStep)
    in
    let q+⊑q++ : q+ ⊑ q++
        q+⊑q++ = inj₂ q+⋤q++
    in
    let q⊑q++ : q ⊑ q++
        q⊑q++ = SGStates.⊑-trans S q⊑q+ q+⊑q++
    in
    let q* = proj₁ (iterTill S D (add (Signoid.card S) i (ℕ.suc a)))
    in
    -- Small technicality: the goal is q* and equals q++,
    -- but not definitionally because q++ iters until 
    --      ℕ.suc (add (Signoid.card S) i a)
    -- whereas q* is defined as iterating until
    --      add (Signoid.card S) i (ℕ.suc a)
    let check : q++ ≡ proj₁ (iterTill S D (ℕ.suc (add (Signoid.card S) i a)))
        check = refl
    in
    let lemma : (ℕ.suc (add (Signoid.card S) i a))
                ≡
                (add (Signoid.card S) i (ℕ.suc a))        
        lemma = sym (addSucCommℕ i a)
    in
    let q++≡q* : q++ ≡ q*
        q++≡q* = cong (λ x → proj₁ (iterTill S D x)) lemma
    in
    subst (λ x → q ⊑ x) q++≡q* q⊑q++
-- Agda does not see that Addibles card i can never be the empty type.
-- (It never is, because we can *always* add 0 to i).
iterTillSublog {ℓ} S@(record {card = fin (ℕ.suc c)}) D i =
    FinAddiblesRec c i P rec
    where
        _⊑_ = SGStates._⊑_ S
        _⋤_ = SGStates._⋤_ S
        idx = SGStates.idx S
        P : cardToSet (fin (ℕ.suc c)) → Set ℓ
        P i+a = (proj₁ (iterTill S D i)) ⊑ (proj₁ (iterTill S D i+a))
        rec 
            : (x : ℕ) 
            → (a : Fin x)
            → (z : toℕ i ℕ+ x ≡ ℕ.suc c)
            → P (cast z (i F+ a))
        -- All the indirection above is just to be able to pattern match on `a`
        -- here.
        rec (ℕ.suc x) Fin.zero z =
            let W : SGStates.SignoidShortcuts.C S → Set ℓ
                W = λ j → (proj₁ (iterTill S D i)) ⊑ (proj₁ (iterTill S D j))
            in
            let H₁ : i ≡ cast z (i F+ (Fin.zero {x}) )
                H₁ = addFinZeroCasted c x i z
            in
            let H₂ : (proj₁ (iterTill S D i)) ⊑ (proj₁ (iterTill S D i))
                H₂ = inj₁ refl
            in
            subst W H₁ H₂
        rec x@(ℕ.suc (ℕ.suc x'')) (Fin.suc a) z = 
            let q = (proj₁ (iterTill S D i)) 
            in
            -- +-suc allows to rewrite (toℕ i ℕ+ (ℕ.suc (ℕ.suc x'')))
            -- into the following form, which has ℕ.suc as outermost on both
            -- hands.
            let z' : ℕ.suc (toℕ i ℕ+ (ℕ.suc x'')) ≡ ℕ.suc c
                z' = trans (sym (+-suc (toℕ i) (ℕ.suc x''))) z
            in
            let z1 : toℕ i ℕ+ (ℕ.suc x'') ≡ c
                z1 = Data.Nat.Properties.suc-injective z'
            in
            --let j : Fin c
            --    j = cast z1 (i F+ a)
            --in
            --let q+ = proj₁ (iterTill S D (inject₁ j))
            --in
            --let idxq+≡Ij : idx q+ ≡ inject₁ j
            --    idxq+≡Ij = proj₂ (iterTill S D (inject₁ j))
            --in
            let j : Fin (ℕ.suc c)
                j = cast z (i F+ inject₁ a)
            in
            let q+ = proj₁ (iterTill S D j)
            in
            let idxq+≡j : idx q+ ≡ j
                idxq+≡j = proj₂ (iterTill S D j)
            in
            -- TODO: termination issue! But I solved this before via WF rec.
            -- in iterTill or so. Can do the same trick again!
            let q⊑q+ : q ⊑ q+
                q⊑q+ = rec x (inject₁ a) z
            in
            let h : IsNotMax j
                h = ?
            in
            let h' : IsNotMax (idx q+)
                h' = subst IsNotMax (sym idxq+≡j) h
            in
            let lastStep = LowLvl.addChoice S D q+ h'
            in
            let q++ = proj₁ lastStep
            in
            let q+⊑q++ : q+ ⊑ q++
                q+⊑q++ = inj₂ (proj₁ (proj₂ lastStep))
            in
            let idxq++≡Sj : idx q++ ≡ endoSuc h'
                idxq++≡Sj = proj₂ (proj₂ lastStep)
            in
            let q⊑q++ : q ⊑ q++
                q⊑q++ = SGStates.⊑-trans S q⊑q+ q+⊑q++
            in
            let i+Sa = (cast z (i F+ Fin.suc a))
            in 
            let q* = proj₁ (iterTill S D i+Sa)
            in
            let idxq*≡i+Sa : idx q* ≡ i+Sa
                idxq*≡i+Sa = proj₂ (iterTill S D i+Sa)
            in
            -- TODO: puzzle a bit more here
            -- TODO: first rewrite i+Sa?
            let meh : i+Sa ≡ Fin.suc (cast z1 (i F+ a))
                meh = {! sym (cast-suc-comm ? ? ? ?) !}
            in
            -- TODO: above equality doesn't give it. 
            let lemma : i+Sa ≡ endoSuc h'
                lemma = {! trans meh (endoSucFinSuc h') !}
            in
            let q++≡q* : q++ ≡ q*
                q++≡q* = {! cong (λ x → proj₁ (iterTill S D x)) lemma !}
            in
            subst (λ x → q ⊑ x) q++≡q* q⊑q++

--iterTillSublogFinCase
--    : {ℓ : Level}
--    {A : Set ℓ}
--    {_⊂_ : Rel A ℓ}
--    (c : ℕ)
--    (S : FinSignoid _⊂_ c)
--    → (D : LowLvl.Decider (fromFinSignoid _⊂_ c S))
--    → (i : SGStates.SignoidShortcuts.C (fromFinSignoid _⊂_ c S))
--    → (a : Addibles (Signoid.card (fromFinSignoid _⊂_ c S)) i)
--    → (bullshit : Addibles (Signoid.card (fromFinSignoid _⊂_ c S)) i ≡ Fin ℕ.zero)
--    → SGStates._⊑_ (fromFinSignoid _⊂_ c S) 
--                     (proj₁ (iterTill (fromFinSignoid _⊂_ c S) D i)) 
--                     (proj₁ (iterTill (fromFinSignoid _⊂_ c S) D (add (fin (ℕ.suc c)) i a)))
--iterTillSublogFinCase c S D i a bullshit = ?

--iterTillSublogFinCaseOneAddible
--    : {ℓ : Level}
--    {A : Set ℓ}
--    {_⊂_ : Rel A ℓ}
--    (c : ℕ)
--    (S : FinSignoid _⊂_ c)
--    → (D : LowLvl.Decider (fromFinSignoid _⊂_ c S))
--    → (iWithOneAddible :
--        Σ[ i ∈ SGStates.SignoidShortcuts.C (fromFinSignoid _⊂_ c S)) ]
--        (ℕ.suc c ∸ toℕ i ≡ 1)

--    → (i : SGStates.SignoidShortcuts.C (fromFinSignoid _⊂_ c S))
--    → (oneAddibles : ℕ.suc c ∸ toℕ i ≡ 1)
--    --→ (oneAddible : Addibles (Signoid.card (fromFinSignoid _⊂_ c S)) i ≡ Fin 1)
--    → (a : Addibles (Signoid.card (fromFinSignoid _⊂_ c S)) i)
--    → SGStates._⊑_ (fromFinSignoid _⊂_ c S) 
--                     (proj₁ (iterTill (fromFinSignoid _⊂_ c S) D i)) 
--                     (proj₁ (iterTill (fromFinSignoid _⊂_ c S) D (add (fin (ℕ.suc c)) i a)))
--iterTillSublogFinCaseOneAddible c S D i refl (Fin.suc Fin.zero) = ?

--noAddiblesCase
--    : {ℓ : Level}
--    {A : Set ℓ}
--    {_⊂_ : Rel A ℓ}
--    → (c : ℕ)
--    → (S' : FinCardSignoid _⊂_ c)
--    → (D : LowLvl.Decider (proj₁ S'))
--    → (i : cardToSet (Signoid.card (proj₁ S'))) 
--    --→ (i : Fin (ℕ.suc c)) -- This is cardToSet (Signoid.card S)
--    → (a : Addibles (Signoid.card (proj₁ S')) i)
--    → (noAddibles : ℕ.suc c ∸ toℕ i ≡ ℕ.zero)
--    → SGStates._⊑_ (proj₁ S')
--        (proj₁ (iterTill (proj₁ S') D i)) 
--        (proj₁ (iterTill (proj₁ S') D (add (Signoid.card (proj₁ S')) i a)))

        

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
