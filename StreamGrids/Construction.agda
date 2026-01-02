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


    -- #TODO: move next few funs to other file?

    -- Compute distance from one number to a greater one.
    -- E.g., dist 1 4 ≐ 3 and dist 2 3 ≐ 1.
    dist : {n m : ℕ} → n Data.Nat.< m → ℕ
    dist {ℕ.zero} {m} (s≤s z≤n) = m
    dist {ℕ.suc n} {ℕ.suc m} (s≤s n<m) = dist {n} {m} (n<m)

    -- Same as dist, but for finite sets,
    finDist : {c : ℕ} → {n m : Fin c} → (n<m : n Data.Fin.< m) → ℕ 
    finDist n<m = dist n<m

    -- Same as dist, but generalised to work for both ℕ and finite sets.
    distCard 
        : {c : ℕ∞}
        → {n m : cardToSet c}
        → cardTo< n m
        → ℕ
    distCard {∞} {n} {m} n<m = dist n<m
    distCard {fin (suc c)} {n} {m} n<m = dist n<m

    -- If a bigger element than n exists in a finite set,
    -- then n is not the maximum element of the set.
    biggerToIsNotMax
        : {c : ℕ∞}
        → {n m : cardToSet c}
        → cardTo< n m
        → IsNotMax n
    biggerToIsNotMax {fin (suc c)} {n} {m} n<m = 
        let Sm≤Sc : ℕ.suc (toℕ m) Data.Nat.≤ ℕ.suc c
            Sm≤Sc = toℕ<n m
        in
        let
            m≤c : toℕ m Data.Nat.≤ c
            m≤c = s≤s⁻¹ Sm≤Sc
        in
        let
            c≡TFc : c ≡ toℕ (fromℕ c)
            c≡TFc = sym (toℕ-fromℕ c)
        in
        let
            m≤TFc : toℕ m Data.Nat.≤ (toℕ (fromℕ c))
            m≤TFc = subst (λ x → toℕ m Data.Nat.≤ x) c≡TFc m≤c
        in
        Data.Nat.Properties.≤-trans n<m m≤TFc
    biggerToIsNotMax {∞} {n} {m} n<m = tt

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

    lemma'
        : {n : ℕ}
        → {j k : Fin (ℕ.suc n)}
        → (j<k : j Data.Fin.< k)
        → (Sj<k : (ℕ.suc (toℕ j)) Data.Nat.<  (toℕ k))
        → ℕ.suc (distCard {∞} Sj<k) ≡ distCard {fin (ℕ.suc n)} j<k
    lemma' {n} {Fin.zero} {Fin.suc (Fin.suc k)} (s≤s z≤n) (s≤s (s≤s z≤n)) = refl
    lemma' {ℕ.suc n} {Fin.suc j} {Fin.suc k} (s≤s j<k) (s≤s Sj<k) = 
        let rec = lemma' j<k Sj<k in rec

    -- Distance d from 1 to k is k-1, or equivalently, d+1 is k.
    lemma'''
        : {c : ℕ}
        → {k : Fin (ℕ.suc c)}
        → (0<k : Data.Fin.zero {ℕ.suc c} Data.Fin.< k)
        → (S0<k : toℕ (endoSuc (biggerToIsNotMax 0<k)) Data.Nat.< (toℕ k))
        → ℕ.suc (distCard {fin (ℕ.suc c)} S0<k) ≡ toℕ k
    lemma''' {ℕ.zero} {Fin.zero} () S0<k
    lemma''' {ℕ.zero} {Fin.suc ()} (s≤s z≤n) (s≤s S0<k)
    lemma''' {c@(ℕ.suc c'@(ℕ.suc c''))} 
             {Fin.suc (Fin.suc k)} 
             (s≤s z≤n) 
             p@(s≤s 0<Sk) = 
        let u : cardTo< {fin (ℕ.suc c)} (Fin.suc Fin.zero) (Fin.suc (Fin.suc k)) 
            u = s≤s (s≤s z≤n)
        in
        let p≡u : p ≡ u
            p≡u = Data.Nat.Properties.≤-irrelevant (s≤s 0<Sk) u
        in
        let normalOutp : ℕ
            normalOutp = distCard {fin (ℕ.suc c)} u
        in
        let outpValue : normalOutp ≡ (ℕ.suc (toℕ k))
            outpValue = refl
        in
        let outp≡outu : distCard {fin (ℕ.suc c)} p ≡ normalOutp
            outp≡outu = cong (distCard {fin (ℕ.suc c)}) p≡u
        in
        cong ℕ.suc (trans outp≡outu outpValue)

    lemma''
        : {c : ℕ}
        → {j k : Fin (ℕ.suc c)}
        → (j<k : j Data.Fin.< k)
        → (STj<k : (ℕ.suc (toℕ j)) Data.Nat.<  (toℕ k))
        → (Sj<k : toℕ (endoSuc (biggerToIsNotMax j<k)) Data.Nat.< (toℕ k))
        → distCard {fin (ℕ.suc c)} Sj<k ≡ distCard {∞} STj<k
    lemma'' {c} {Fin.zero} {Fin.suc k@(Fin.suc k')} (s≤s z≤n) 
            STj<k@(s≤s (s≤s z≤n)) (s≤s Sj<k) =
        let LHS = distCard {fin (ℕ.suc c)} (s≤s Sj<k)
        in
        -- The LHS does not reduce to a value automatically, but we have a lemma
        -- for that. It just needs 
        let LHSvalueAlmost : ℕ.suc LHS ≡ toℕ (Fin.suc k)
            LHSvalueAlmost = lemma''' (s≤s z≤n) (s≤s Sj<k)
        in
        let LHSvalue : LHS ≡ toℕ k
            LHSvalue = Data.Nat.Properties.suc-injective LHSvalueAlmost
        in
        let call = lemma''' (s≤s z≤n) (s≤s Sj<k)
        in
        let _ = distCard {fin (ℕ.suc c)} (s≤s Sj<k)
        in
        let RHS = distCard {∞} STj<k
        in
        let RHSvalue : RHS ≡ toℕ k -- The RHS computes nicely. 
            RHSvalue = refl
        in
        trans LHSvalue (sym RHSvalue)
    lemma'' {ℕ.suc c} {Fin.suc j} {Fin.suc k} (s≤s j<k) (s≤s STj<k) (s≤s Sj<k) =
        let rec = lemma'' {c} {j} {k} j<k STj<k Sj<k
        in
        rec

    --Incrementing the lower of two numbers decreases the distance by 1.
    decrDist
        : {c : ℕ∞}
        → {j k : cardToSet c}
        → (j<k : cardTo< j k)
        → (Sj<k : cardTo< (endoSuc (biggerToIsNotMax j<k)) k)
        → ℕ.suc (distCard {c} Sj<k) ≡ distCard {c} j<k
    decrDist {∞} {ℕ.zero} {ℕ.suc k} (s≤s z≤n) (s≤s (s≤s z≤n)) = refl
    decrDist {∞} {ℕ.suc j} {ℕ.suc k} (s≤s j<k) (s≤s Sj<k) =
        decrDist {∞} {j} {k} (j<k) (Sj<k)
    decrDist {fin (suc c)} {j} {k} j<k Sj<k =
        let h = biggerToIsNotMax j<k in
        let STj<k : (ℕ.suc (toℕ j)) Data.Nat.<  (toℕ k) 
            STj<k = subst (λ x → x Data.Nat.< (toℕ k)) 
                         (endoSucInjToNatSuc h)
                         Sj<k
        in
        let H₁ :  ℕ.suc (distCard {∞} STj<k) ≡ distCard {fin (ℕ.suc c)} j<k
            H₁ = lemma' j<k STj<k
        in
        let
            H₂ : distCard {fin (ℕ.suc c)} Sj<k ≡ distCard {∞} STj<k
            H₂ = lemma'' j<k STj<k Sj<k
        in
        trans (cong ℕ.suc H₂) H₁

    -- distCard requires to prove that j<k, 
    -- so the distance from j to k is always greater than zero.
    distCardNonZero
        : {c : ℕ∞}
        → {j k : cardToSet c}
        → (j<k : cardTo< {c} j k)
        → ℕ.zero Data.Nat.< distCard {c} j<k
    distCardNonZero {fin (ℕ.suc c)} {Fin.zero} {Fin.suc k} (s≤s z≤n) = s≤s z≤n
    distCardNonZero {fin (ℕ.suc (ℕ.suc c))} {Fin.suc j} {Fin.suc k} (s≤s j<k) = 
        distCardNonZero {fin (ℕ.suc c)} {j} {k} j<k
    distCardNonZero {∞} {ℕ.zero} {ℕ.suc k} (s≤s z≤n) = s≤s z≤n
    distCardNonZero {∞} {ℕ.suc j} {ℕ.suc k} (s≤s j<k) = 
        distCardNonZero {∞} {j} {k} j<k

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

    -- #TODO: finish and move to Card.agda
    -- If `cardToSet c` is inhabited, then c cannot be zero.
    elToNonempty
        : {c : ℕ∞}
        → cardToSet c
        → fin ℕ.zero <∞ c
    elToNonempty {fin (ℕ.suc c)} i = s≤s z≤n
    elToNonempty {∞} i = tt

    -- Compute the choicelog containing the first i element
    -- with choices made according to a given decider.
    -- This starts from an empty choicelog, and hence constructs the root first.
    -- (The constructor of the root requires a nonemptyness proof of the
    -- enumerated set, but i already witnesses nonemptyness anyway).
    iterTill 
        : Decider 
        → C 
        → Q
    iterTill D i = 
        let nonempty = elToNonempty i
        in
        rootLog nonempty

    -- Compute the normal form of any element of A.
    -- This is well defined, since every element will eventually
    -- be added to a choicelog in the inductively defined succession of
    -- choicelogs induces by a decider, at which point its normal form is well
    -- defined. Furthermore, the normal form will remain the same in successor
    -- choicelogs.
    nfGlobalIdx : Decider → C → C
    nfGlobalIdx D i = 
        let q : Q
            q = iterTill D i
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


    IsNF : Decider → A → Set
    IsNF D x = ⊥ -- #TODO
        -- Idea: iter till x is topmost element in choicelog.
        -- Then just pattern match on the legalChoice: if not newNF
        -- then ⊥ else ⊤. Easy!

data AsType 
    {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    (S : Signoid _⊂_)
    (D : LowLvl.Decider S) : Set ℓ
    where
    fromNF : (x : A) → (LowLvl.IsNF S D x) → AsType S D
    
