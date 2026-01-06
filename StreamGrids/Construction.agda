-- Module      : StreamGrids.Construction
-- Description : Tools to construct types and relations via StreamGrids
-- Copyright   : (c) Lulof Pirée, 2025
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
open import Relation.Binary
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


    -- Predicate whether the most recent element is a normal form,
    -- which it is iff constructed via the `root _` or `choose ... newNf ...`
    -- constructors.
    IsNFState : Q → Set
    IsNFState (_ , _ , root h) = ⊤
    IsNFState (_ , _ , choose _ _ (newNF _ _ _)) = ⊤
    IsNFState (_ , _ , choose _ _ (freeChoice _ _ _ _)) = ⊥
    IsNFState (_ , _ , choose _ _ (forcedChoice _ _ _)) = ⊥

    IsNFInState
        : (q : Q)
        → (i : C)
        → (i<idxq : i <C q)
        → Set
    IsNFInState q i i<idxq = IsNFState (proj₁ (SGStates.getSubLog q i i<idxq))

    -- Check if an element becomes a normal form in the choice log
    -- generated inductively from the empty choice log by the given decider.
    -- Construct the choice log up to the point where x is the most recent
    -- added, then check if it uses the `root` or `choose ... newNf ...`
    -- constructors.
    IsNFInSG : Decider → A → Set
    IsNFInSG D x = IsNFState (iterTill S D (elToIdx x))

    IsListNF : Decider → C → Set
    IsListNF D i = i ∈ (nflist (iterTill S D i))
    -- #TODO: this is still a proposition.
    -- It is using `Data.List.Membership.Setoid.Properties.unique⇒irrelevant`
    -- if one can show `Unique (nflist q)` for all `q : Q`,
    -- which ought to be easily provable.

    -- #TODO: rename, maybe move
    sublemma
        : (i : C)
        → (j : Indices (nflist (iterTill i))
        → IsNF ( lookup (nflist (iterTill i)) j)
    sublemma 

    -- The next theorem asserts that the output of nfGlobalIdx (and hence
    -- nfGlobal as well) is indeed always a normal form.
    --
    -- It is very specific to this way of computing the normal form,
    -- since nfGlobal assumes no choice log has been given in advance,
    -- and builds up a new choicelog from an empty start.
    -- #TODO: it would also be convenient to prove that all elements
    -- of the nflist of any given preexisting choicelog are normal 
    -- -- but then cannot be normal w.r.t.
    -- to a Decider cuz the choicelog might have been build by multiple deciders
    -- alternatingly. 
    -- This would require a strip-down definition of `IsNF` that digs into a
    -- given choicelog until it finds the desired element,
    -- and checks there how it has been constructed.
    nfGlobalIsNF
        : ( i : C)
        → IsNF (nfGlobalIdx i)
    nfGlobalIsNF i = ?

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
    fromNF : (x : A) → (IsNF S D x) → AsType S D

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
