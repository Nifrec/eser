-- Module      : StreamGrids.Construction
-- Description : Tools to construct types and relations via StreamGrids
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
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
    dist {n} {m} n<m = ∣ n - m ∣ -- |_-_| is given in the stdlib Data.Nat.Base.

    -- Mimicks |_-_| from Data.Nat.Base.
    -- Ofc one could also use | toℕ_ - toℕ_ | but this seems more convenient in
    -- proofs.
    finDist : {c : ℕ} → Fin c → Fin c → ℕ 
    finDist Fin.zero m = toℕ m
    finDist n Fin.zero = toℕ n
    finDist (Fin.suc n) (Fin.suc m) = ℕ.suc (finDist n m)

    -- Same as dist, but generalised to work for both ℕ and finite sets.
    distCard 
        : {c : ℕ∞}
        → {n m : cardToSet c}
        → cardTo< n m
        → ℕ
    distCard {∞} {n} {m} n<m = dist n<m
    distCard {fin (suc c)} {n} {m} n<m = dist n<m
    
    -- Same as dist, but generalised to work for both ℕ and finite sets.
    newDistCard 
        : {c : ℕ∞}
        → {n m : cardToSet c}
        → cardTo< n m
        → ℕ
    newDistCard {∞} {n} {m} n<m = dist n<m
    newDistCard {fin (suc c)} {n} {m} n<m = finDist n m

    -- If n<m then |n-m| > 0.
    nonzeroDist
        : {n m : ℕ}
        → (n<m : n Data.Nat.< m)
        → ℕ.zero Data.Nat.< dist n<m 
    nonzeroDist {ℕ.zero} {ℕ.suc m} (s≤s z≤n) = s≤s Data.Nat.z≤n
    nonzeroDist {ℕ.suc n} {ℕ.suc m} (s≤s n<m) = nonzeroDist n<m

    -- nonzeroDist generalised to work with both ℕ and finite sets.
    nonzeroDistCard
        : {c : ℕ∞}
        → {n m : cardToSet c}
        → (n<m : cardTo< n m)
        → ℕ.zero Data.Nat.< distCard {c} n<m
    nonzeroDistCard {∞} {n} {m} n<m = nonzeroDist n<m
    nonzeroDistCard {fin (ℕ.suc c)} {n} {m} n<m = nonzeroDist n<m

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


    --Incrementing the lower of two numbers decreases the distance by 1.
    decrDist
        : {c : ℕ∞}
        → {j k : cardToSet c}
        → (j<k : cardTo< j k)
        → (Sj<k : cardTo< (endoSuc (biggerToIsNotMax j<k)) k)
        → ℕ.suc (newDistCard {c} Sj<k) ≡ newDistCard {c} j<k
    decrDist {∞} {ℕ.zero} {ℕ.suc k} 0<Sk 1<Sk = refl
    decrDist {∞} {ℕ.suc j} {ℕ.suc k} Sj<Sk SSj<Sk = 
        decrDist {∞} {j} {k} (s≤s⁻¹ Sj<Sk) (s≤s⁻¹ SSj<Sk)
    --decrDist {fin (ℕ.suc c)} {j} {k} j<k Sj<k = 
    --    let meh = ? -- use Sj<k
    --    in
    --    decrDist {∞} {toℕ j} {toℕ k} j<k meh
    decrDist {fin (ℕ.suc c)} {Fin.zero} {Fin.suc k} (s≤s z≤n) (s≤s 1<Sk) = refl {x = toℕ k}
        --let t1 : distCard {fin (ℕ.suc c)} (s≤s (z≤n {toℕ k})) 
        --         ≡ ∣ toℕ (Data.Fin.lower (Fin.zero {ℕ.suc c}) (z<s)) - toℕ k ∣
        --    t1 = refl
        --in
        --?
        --let meh = sym (lemma (Fin.suc k))
        --in
        --{! meh !}
        where
            lemma 
                : {n : ℕ} 
                → (k : Fin (ℕ.suc n)) 
                → ∣ toℕ (Data.Fin.lower (Fin.zero {n}) (z<s {n})) - toℕ k ∣ ≡ toℕ k
            lemma {n} Fin.zero = refl
            lemma {n} (Fin.suc k) = refl
    decrDist {fin (ℕ.suc c)} {Fin.suc j} {k} j<k Sj<k = {! !}

    -- Add choices to a choicelog q until the enumeration-index
    -- of the most recently chosen element is i.
    -- Of course, this is only possible if i has not been chosen in q already.
    iterFromTill
        : Decider
        → (q : Q)
        → (i : C)
        → (idxq<i : cardTo< (idx q) i)
        -- #TODO This does not typecheck. missing arg to `dist`,
        -- namely toℕ idx q < toℕ i. Replace h by an arg of this type.
        -- Prove that h can be inferred from it.
        → (f : ℕ)
        --^ "Fuel", is decreased every iteration, used to please Agda's
        -- termination checker.
        → (distCard {card} idxq<i) Data.Nat.≤ f
        → Σ[ q* ∈ Q ]( idx q* ≡ i )
    iterFromTill D q i idxq<i zero d = 
        let z<dist : ℕ.zero Data.Nat.< distCard {card} idxq<i 
            z<dist = nonzeroDistCard {card} idxq<i
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
            d+ = ?
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
    elToNonempty {c} i = ?

    -- Compute the choicelog containing the first i element
    -- with choices made according to a given decider.
    iterTill 
        : Decider 
        → C 
        → Q
    -- #TODO: do we need an argument (h : (fin ℕ.zero) <∞ card)?
    -- I think not, since `i : C` already implies that A is not the empty set.
    iterTill D i = ?

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
    
