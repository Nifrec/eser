-- Module      : StreamGrids.ChoiceLog.Core
-- Description : Core definitions and functions
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Intrinsic "choice-log" representation of StreamGrid states: 
-- an inductive type where all constraints are part of the constructors.
--
-- This is in contrast with the list-of-lists representation of states,
-- where all invariants of the states are added externally via a big nesting of
-- Σ's stating properties about the list-of-lists.
-- The latter approach became very cumbersome when computing a new state,
-- as all the external properties needed to be reproven,
-- which turned out to be complicated.
--
-- In the current representation, a state is essentially a stack of choices.
-- A successor state just adds an allowed choice on top of the stack,
-- making it much easier to prove that all previous properties are still
-- preserved.
--
-- "Substacks" version of implementation of normal form computation.
-- * Elements of a state are sub-choice-logs, or just substacks of choices.
-- * States are not indexed.
-- * States are still represented by a choice log, not a list of lists.
-- * The is-a-substack-relation is defined and heavily employed.
-- * Normal forms ... #TODO
-- The hope is that substacks are easier to work with than with numbers.
-- Especially the finite sets were an infinite source of headaches in
-- the previous attempt, "PhCore".
--
-- "NewSCore" version of normal form computation using NewSignoid
-- as definition of Signoids, and non-contractible LegalChoices.
--
-- "NFListCore" version improves "NewSCore" by annotating SGState's with a list
-- of normal forms. This is necessary to avoid circular dependencies
-- between the definition of IsNF and LegalChoices (making IsNF an inductive
-- type and using mutual induction does not fix it; it becomes
-- non-strictly-positive).
-- Normal forms are identified with their index in the enumeration,
-- and this representation is stored in the list.
-- This version makes IsNF no longer needed, checking normality becomes trivial.
-- * _⊑_ needs to be proven to be Well-Founded.
-- * Some auxiliary lemmas about list indices are needed.
--
-- "NFListIElemCore" changes the definition of LegalChoices
-- to use iElem rather than sElem again (i.e., representing 
-- elements in choice logs by their enumeration-index rather than
-- as sub-choice-logs).
--
-- "IdxAndListCore" version (16 Dec 2025) again adds a numerical index to
-- states, the enumeration index of the last element added (this is off-by-one
-- in comparison with the numerical index used before the "Substacks" version).
-- This is necessary to be able to avoid building longer choicelogs than there
-- exist distinct elements, and to compute the height and the
-- next-element-to-add from a state, because of the following:
-- * the `choose` constructor of SGStates should not allow adding choices
--      to a stack that already has all elements of A. 
--      So it asks for a proof that the height of the input stack is not max.
-- * the `height` function would proceed by structural induction to compute the
--      number of choices in a choicelog.
-- These definitions are defined in terms of each other, this circularity
-- breaks things. Hence the solution is to cache the index of the last element
-- added during the construction of the choice log (like how the NFList does it
-- for normal forms). This gives enough information to quickly check if another
-- element can be added or not.

{-# OPTIONS --allow-unsolved-metas #-}

module StreamGrids.ChoiceLog.IdxAndListCore where

-- Certainly used standard library imports.
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

open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Membership.Propositional using (_∈_ ; _∉_)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Binary.Pointwise.Properties renaming (refl to Pointwise-refl)
open import Data.List.Relation.Binary.Suffix.Heterogeneous.Properties 
    renaming (trans to Suffix-trans)

-- Certainly used local imports.
open import StreamGrids.NewSignoid
open import StreamGrids.Card
open import StreamGrids.Suffix

module SGStates
    {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    (S : Signoid _⊂_)
    where

    -- Setting some abbreviations for some of the data of the Signoid
    -- for better readability.
    private 
        card : ℕ∞
        card = Signoid.card S

        -- Existing indices in the enumeration of A.
        -- That's ℕ if A has infinitely many elements
        -- and Fin n otherwise.
        C : Set
        C = cardToSet card

        idxSuc : {i : C} → (h : IsNotMax i) → C
        idxSuc {i} h = endoSuc {card} {i} h

        -- Default _<_ relation on `C`, which is either Fin._<_
        -- or ℕ._<_ (or just ⊥ if card = zero).
        _<C_ : Rel C _
        _<C_ = cardTo< {card}

        NFList : Set
        NFList = List C

        idxToEl : C → A
        idxToEl = Signoid.idxToEl S

        elToIdx : A → C
        elToIdx = Signoid.elToIdx S

    -- These inductive types are defined via mutual induction,
    -- so we declare them all up front here.
    data SGState : C → NFList → Set ℓ


    Q : Set _
    Q = Σ[ i ∈ C ](Σ[ L ∈ NFList ](SGState i L))

    -- Get the enumeration-index of the last element added to a choicelog.
    idx : Q → C
    idx (i , _ , _) = i

    -- Get the last element added to a choicelog.
    el : Q → A
    el q = idxToEl (idx q)

    data LegalChoices : Q → Set ℓ
    UpdateNFList : (q : Q) → LegalChoices q → NFList
      
    -- Strict Is-a-sub-ChoiceLog-of relation.
    -- I made custom `\subst` binding in my nvim/Cornelis setup.
    -- for the `⋤` symbol.
    data _⋤_ : Rel Q ℓ

    -- Is-a-sub-ChoiceLog-of relation.
    -- A state/ChoiceLog q is a stack of choices,
    -- and q' ⊑ q denotes simply that q' is a substack of q.
    -- This relation forms a poset: reflexive, transitive, antisymmetric.
    -- `⊑` in Cornelis: `\sqsubseteq` or `\squb=`. 
    -- I made custom `\substeq` binding in my setup.
    -- Note: for ℕ, < is defined in terms of ≤ as
    -- m < n ≝ (S m) ≤ n.
    -- This approach does NOT work here cuz if q' ⊑ q
    -- then there typically are multiple possible direct successors of q'.
    _⊑_ : Rel Q ℓ
    q' ⊑ q = (q' ≡ q) ⊎ (q' ⋤ q)

    --record ForcedCoercion (q : SGState) : Set ℓ
    --record NoForcedCoercion (q : SGState ) : Set ℓ
    --NormalForms : SGState → Set ℓ
    --data _⊢_≈_ : SGState → A → A → Set ℓ

    data SGState where
        root 
            : (h : (fin ℕ.zero) <∞ card)
            --^ *If* at least one element exists,...
            → SGState (nonzeroCardToZeroElem h) ((nonzeroCardToZeroElem h) ∷ [])
            --^ ...then there is a canonical root state with only that
            -- element explored (and the reflexive congruence on it).
            -- The list of normal forms is [ 0 ].
        choose 
            : (q : Q)
            → (h : IsNotMax (idx q))
            → (lc : LegalChoices q )
            → SGState (idxSuc h) (UpdateNFList q lc)

--------------------------------------------------------------------------------
-- Substack (sub-choice-log) relation ⊑.
--------------------------------------------------------------------------------
    
    data _⋤_ where
        onechoice 
            : (q : Q) 
            → (h : IsNotMax (idx q))
            → (lc : LegalChoices q)
            → q ⋤ (idxSuc h , UpdateNFList q lc , choose q h lc)
        multichoice
            : (q' q : Q)
            → (q' ⋤ q)
            → (h : IsNotMax (idx q))
            → (lc : LegalChoices q)
            → q' ⋤ (idxSuc h , UpdateNFList q lc , choose q h lc)

    ⊑-refl : Reflexive _⊑_
    ⊑-refl {q} = ?

    -- #TODO: transitivity broke after changing the def of Q and _⊑_.
    --⊑-trans : Transitive _⊑_
    --⊑-trans {q} {q} {r} (refl q) q⊑r = q⊑r
    --⊑-trans {p} {q} {q} p⊑q (refl q) = p⊑q
    --⊑-trans {p} {q} {r} (sub q' p ℓq p⊑q') (sub r' (choose q' ℓq) ℓr q⊑r') =
    --    let q = choose q' ℓq in
    --    let q'⊑q = sub q' q' ℓq (refl q') in
    --    let p⊑q = ⊑-trans p⊑q' q'⊑q in
    --    let p⊑r' = ⊑-trans p⊑q q⊑r' in
    --    sub r' p ℓr p⊑r'

--------------------------------------------------------------------------------
-- Element representations.
--------------------------------------------------------------------------------
    
    -- Substack definition of element-already-chosen-in-a-state.
    -- In contrast to the index-based definition (`iElem`, used in PhCore.agda).
    -- An element is identified with the prefix of the choice log up to the
    -- point where that element is added to the congruence.
    sElem : Q → Set ℓ
    sElem q = Σ[ q' ∈ Q ](q' ⊑ q)

    getState : {q : Q} → sElem q → Q
    getState {q} (q' , q'⊑q) = q' -- Same as proj₁

    -- Number of elements whose equalities have already been chosen in a
    -- ChoiceLog.
    height : Q → C
    -- #TODO: this will require a lemma stating that the maximum
    -- height is bounded by card. I.e., actual-height <∞ card.
    height q = ? 
    
    -- Convert from sElem-representation of an element to the number
    -- it has in the enumeration of A.
    getIdx : {q : Q} → sElem q → C
    getIdx {q} q' = height (getState (q'))

    -- Convert from sElem-representation of an element to the A-term
    -- it represents.
    getEl : {q : Q} → sElem q → A
    getEl {q} q' = Signoid.idxToEl S (getIdx q')

    -- The relation _⊂_, but slightly modified to work on the sElem
    -- representation of terms, rather than direct A terms.
    sElem⊂ : {q : Q} → Rel (sElem q) _
    sElem⊂ q' q'' = (getEl q') ⊂ (getEl q'')

    infix 30 sElem⊂
    syntax sElem⊂ q' q'' = q' ⊂* q''

    -- _⊂I_ is the relation _⊂_, 
    -- but slightly modified to work on the enumeration-index
    -- representation of terms, rather than direct A terms.
    iElem⊂ : Rel C _
    iElem⊂ i i' = (idxToEl i) ⊂ (idxToEl i')

    infix 30 iElem⊂
    syntax iElem⊂ i i' = i ⊂I i'

    nextEl : Q → A
    nextEl q = idxToEl (height q)

    nextIdx : Q → C
    nextIdx q = height q

--------------------------------------------------------------------------------
-- Definitions of other auxiliary inductive types used in the construction
-- of states.
--------------------------------------------------------------------------------
    -- Predicate that tells that all arguments (via the _⊂_ relation)
    -- of the next element for which to choose its equalities
    -- are normal forms.
    AllArgsNormal
            : {i : C}
            → {L : NFList}
            → (s : SGState i L)
            → Set _
    AllArgsNormal {i} {L} s = 
                (x : sElem (i , L , s))
                → ((getEl x) ⊂ (nextEl (i , L , s))) 
                → (getIdx x) ∈ L

    -- Same as AllArgsNormal, but using the enumeration-index representation of
    -- elements.
    IAllArgsNormal
            : {i : C}
            → {L : NFList}
            → (s : SGState i L)
            → Set _
    IAllArgsNormal {i} {L} s = 
                (x : C)
                → ((idxToEl x) ⊂ (nextEl (i , L , s))) 
                → x ∈ L

    -- Predicate that the next element y has an x ⊂ y
    -- such that x is NOT a normal form.
    NormalisibleArg
            : {i : C}
            → {L : NFList}
            → (s : SGState i L)
            → Set _
    NormalisibleArg {i} {L} s
            = Σ[ x ∈ sElem (i , L , s) ](
                ((getEl x) ⊂ (nextEl (i , L , s)))
                ×
                (getIdx x) ∉ L
                )

    -- Same as NormalisibleArg,
    -- but using the enumeration-index representation of elements.
    INormalisibleArg
            : {i : C}
            → {L : NFList}
            → (s : SGState i L)
            → Set _
    INormalisibleArg {i} {L} s
            = Σ[ x ∈ C ](
                ((idxToEl x) ⊂ (nextEl (i , L , s)))
                ×
                (x ∉ L)
                )

    -- Set of indices that exist for a given list.
    -- #TODO: maybe move this somewhere else? It is copied from
    -- StreamGrids/List.agda.
    Indices : {X : Set _} → List X → Set
    Indices L = Fin (length L)

    data LegalChoices where
        newNF 
            : {i : C}
            → {L : NFList}
            → (s : SGState i L)
            → (IAllArgsNormal s)
            → LegalChoices (i , L , s)
        freeChoice
            : {i : C}
            → {L : NFList}
            → (s : SGState i L)
            → (IAllArgsNormal s)
            → (Indices L)
            --^ (Index of) normal form to which we set the next element equal.
            → LegalChoices (i , L , s)
        forcedChoice
            : {i : C}
            → {L : NFList}
            → (s : SGState i L)
            → (INormalisibleArg s)
            → LegalChoices (i , L , s)

    UpdateNFList (i , L , s) (newNF s₁ x) = (nextIdx (i , L , s)) ∷ L
    UpdateNFList (i , L , s) (freeChoice s₁ x x₁) = L
    UpdateNFList (i , L , s) (forcedChoice s₁ x) = L

--------------------------------------------------------------------------------
-- Normal-form-computing algorithm.
--------------------------------------------------------------------------------
    
    _≼_ : Rel NFList _
    L' ≼ L = Suffix (_≡_) L' L

    ≼-refl : Reflexive _≼_
    ≼-refl {L} = Suffix.here (Pointwise-refl _≡_.refl)

    ≼-trans : Transitive _≼_
    ≼-trans = Suffix-trans trans


    -- #TODO: remove? this lemma is true but not used in the end.
    --rootHasNoSublog
    --    : (q : Q)
    --    → (lc : LegalChoices q)
    --    → (h : (fin ℕ.zero) <∞ card)
    --    → ¬ ((UpdateNFList q lc) , choose q lc ) ⋤ (nonzeroCardToZeroElem h ∷ [] , root h)
    --rootHasNoSublog q lc h ()

    rootHasNoSublog
        : {q : Q}
        → {h : (fin ℕ.zero) <∞ card}
        → ¬ (q ⋤ (nonzeroCardToZeroElem h , nonzeroCardToZeroElem h ∷ [] , root h))
    rootHasNoSublog ()

    open import Induction.WellFounded as WF
    ⋤-wellFounded : WellFounded _⋤_
    ⋤-wellFounded (_ , L , root h) = 
        acc λ { q'⋤root → ⊥-elim (rootHasNoSublog q'⋤root) }
    ⋤-wellFounded (_ , L , choose q h lc) = acc f
        where
            f : {q' : Q} → q' ⋤ (idxSuc h , UpdateNFList q lc , choose q h lc) → Acc _⋤_ q'
            f {q'} (onechoice q₁ h lc) = ⋤-wellFounded q₁
            f {q'} (multichoice q' q₁ q'⋤q₁ h lc) = 
                let rec = acc-inverse (⋤-wellFounded q₁) in
                rec q'⋤q₁

    -- #TODO: wfRec and wfRec-building from the standard library might
    -- do this automatically. Skipped this for now.
    -- Current implementation mimics the <-rec function defined in
    -- the book "PROGRAM=PROOF" page 331 by Samuel Mimram (2025 version).
    ⋤-rec
        : (P : Q → Set _)
        → ((q : Q) → ((q' : Q) → (q' ⋤ q) → P q') → P q)
        -- ^ If you can compute P q provided that P q' can be computed
        -- for all predecessors of q'...
        → (q : Q) → (P q)
        -- ^ ... then inductively we can compute P q for all q : Q.
    ⋤-rec P recurse q = lemma q (⋤-wellFounded q)
        where
            lemma : (q : Q) → (Acc _⋤_ q) → P q
            lemma q (acc allPredAcc) 
                = recurse q (λ q' → (λ q'⋤q → (lemma q' (allPredAcc q'⋤q))))

    -- Lemma A3 in my 12 Dec 2025 notes.
    -- If q' ⋤ (L, choose q' lc), then L must be an extension
    -- of the normal forms of q.
    -- This is a special case (and auxiliary lemma) 
    -- of `multichoiceSuffix` below.
    onechoiceSuffix
        : {i : C}
        → {L : NFList}
        → {s : SGState i L}
        → {h  : IsNotMax i}
        → {lc : LegalChoices (i , L , s)}
        → (i , L , s) ⋤ (idxSuc h , UpdateNFList (i , L , s) lc , choose (i , L , s) h lc)
        → L ≼ UpdateNFList (i , L , s) lc
    onechoiceSuffix {_} {L} {s} {_} {newNF s x} q⊑q = Suffix.there ≼-refl
    onechoiceSuffix {_} {L} {s} {_} {freeChoice s x x₁} q⊑q = ≼-refl
    onechoiceSuffix {_} {L} {s} {_} {forcedChoice s x} q⊑q = ≼-refl


    -- When adding more choices to a choice log, the new list of normal forms
    -- is an extension of the original list. 
    multichoiceSuffix
        : {i' i : C}
        → {L' L : NFList}
        → {s' : SGState i' L'}
        → {s  : SGState i L}
        → (i' , L' , s') ⊑ (i , L , s)
        → L' ≼ L
    -- Easy case: given q'⊑q where both are the root,
    -- we know both have as NFList simply [0].
    -- Only hurdle is that Agda doesn't immediately see that 
    --      nonzeroCardToZeroElem h' = nonzeroCardToZeroElem h
    multichoiceSuffix {i'} {i} {L'} {L} {root h'} {root h} q'⊑q = 
        let zeroh≡zeroh' = thereIsOneZero' {card} h h' in
        let ref = ≼-refl {nonzeroCardToZeroElem h ∷ []} in
        subst (λ k → Suffix _≡_ (k ∷ []) (nonzeroCardToZeroElem h ∷ [])) 
            zeroh≡zeroh' ref
    -- Any q'⊑q where q has only the root element and q' at least
    -- two elements (`choose` as topmost constructor) is impossible.
    multichoiceSuffix {i'} {i} {L'} {L} {choose q h lc} {root k} (inj₁ ())
    multichoiceSuffix {i'} {i} {L'} {L} {choose q h lc} {root k} (inj₂ ())
    -- q'⊑q gives two cases. In the first case, q'≡q,
    -- i.e., (L' , s'_ = (L , choose q lc).
    -- Then trivially L' ≡ L as well, and ≼ is reflexive.
    multichoiceSuffix {i'} {i} {L'} {L} {s'} {choose q'' h lc} (inj₁ refl) = ≼-refl
    -- In the other case we have q`⋤q (strict sublog).
    -- First subcase: q' = (L' , s') has only one choice fewer than q.
    -- Hence we are in the onechoice situation, which we already proved above.
    multichoiceSuffix {i'} {i} {L'} {L} {s'} {choose (i' , L' , s') h lc} 
        (inj₂ q'⋤q@(onechoice (i' , L' , s') h' lc)) =
        onechoiceSuffix {i'} {L'} {s'} {h'} {lc} q'⋤q
    -- Second subcase: q has several choices on top of those in q'.
    -- Then we have:
    --      (1) q = choose q₁ lc
    --      (2) q' ⊑ q₁
    --      (3) q₁ = (L₁ , s₁)
    --  We can recurse on (2) to obtain 
    --      (4) L' ≼ L₁
    --  and the onechoiceSuffix lemma on (1) will give
    --      (5) L₁ ≼ L
    --  Transitivity of ≼ on (4) and (5) then gives the desired
    --      (6) L' ≼ L
    multichoiceSuffix {i'} {i} {L'} {L} {s'} {choose q₁ h lc} 
        (inj₂ (multichoice q' q₁@(i₁ , L₁ , s₁) q'⋤q₁ h₁ lc)) = 
        let q'⊑q₁ = inj₂ q'⋤q₁ in
        let L'≼L₁ = multichoiceSuffix {i'} {i₁} {L'} {L₁} {s'} {s₁} q'⊑q₁ in
        let L₁≼L  = onechoiceSuffix {i₁} {L₁} {s₁} {h} {lc} (onechoice q₁ h lc) in
        ≼-trans L'≼L₁ L₁≼L
        
    nf  : {i : C}
        → {L : NFList}
        → {s : SGState i L} 
        → (x : sElem (i , L , s)) 
        → Indices L
    -- We know that L' is [ 0 ].
    -- Prove that L' is a sublist of L, then we know that 0 ∈ L.
    -- * (SomeLemma x⊑q) should give L' ⊆ L.
    -- * (SomeOtherLemma (L' , root h)) should give L' = [ 0 ],
    --      or even only 0 ∈ L' is enough.
    nf {i} {L} {s} ((i' , L' , root h) , x⊑q) = ?    
    nf {i} {L} {s} ((i' , L' , choose (i'' , L'' , s'') h (newNF s'' x)) , x⊑q) = {! !}
    nf {i} {L} {s} ((i' , L' , choose (i'' , L'' , s'') h (freeChoice s'' x x₁)) , x⊑q) = {! !}
    nf {i} {L} {s} ((i' , L' , choose (i'' , L'' , s'') h (forcedChoice s'' x)) , x⊑q) = {! !}
        where
            q : Q
            q = (i , L , s)

    -- #TODO: better define this in terms of sElem first,
    -- thereafter make iElem version (with type as below)
    -- that
    -- 1. Maps an iElem to an sElem.
    -- 2. Calls the sElem version of nf().
    -- #TODO: 'Inf' stands for iElem-nf, but sounds like "infinite" as well.
    --  Find a better name.
    Inf 
        : {i : C}
        → {L : NFList}
        → {s : SGState i L}
        → (x : C)
        → (x <C height (i , L , s))
        → Indices L
    Inf {L} {s} x x∈s = {! !}



    
--------------------------------------------------------------------------------
-- Maybe keep, maybe move, maybe remove.
--------------------------------------------------------------------------------
    --next : {n : StateIndices} → IsNotMax n → A
    --next {n} notMax = Signoid.enum S (cardLower notMax)

    --⊑-antisym : Antisymmetric _≡_ _⊑_
    --⊑-antisym {q} {q} (refl q) q⊑q = refl
    --⊑-antisym {q} {q} q⊑q (refl q) = refl
    --⊑-antisym {p} {q} (sub q' p ℓq p⊑q') (sub p' q ℓp q⊑p') = 
    --    let p'⊑p = sub p' p' ℓp (refl p') in
    --    let p'⊑q' = ⊑-trans p'⊑p p⊑q' in
    --    let q'⊑q = sub q' q' ℓq (refl q') in
    --    let q'⊑p' = ⊑-trans q'⊑q q⊑p' in
    --    let p'≡q' = ⊑-antisym p'⊑q' q'⊑p' in
    --     Still need ℓp = ℓq, given that we could
    --     apply cong pm p'≡q' with (λ x → choose x ℓp), and then subst the
    --     right occurrence of ℓp via ℓp=ℓq.
    --    let pℓp≡qℓp = cong (λ x → choose x) p'≡q' (refl (choose p')) in
    --    {!  !}

    -- #TODO: conjecture: Totality and decidability of _⊑_ can also be proven.

