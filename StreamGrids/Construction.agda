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

    -- Same as dist, but lifted to work for both ℕ and finite sets.
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
    iterFromTill D q i idxq<i zero d = ⊥-elim ? --#TODO: cannot happen cuz d.
    iterFromTill D q i idxq<i (suc f) d 
        with (cardToDecidableEq card (idxSuc (biggerToIsNotMax idxq<i)) i)
    ... | yes p = let h = biggerToIsNotMax idxq<i in (nextState D q h , p)
    ... | no  p = 
        let h : IsNotMax (idx q)
            h = biggerToIsNotMax idxq<i
        in
        let q+ : Q
            q+ = nextState D q h
        in
        -- Note: idx q+ ≐ idxSuc h.
        let idxq+<i : cardTo< (idx q+) i
            idxq+<i = ?
        in
        let d+ : (distCard {card} idxq+<i) Data.Nat.≤ f
            d+ = ?
        in
        iterFromTill D q+ i idxq+<i f d+

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
    
