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
open import Data.List.Membership.Propositional using (_∈_ ; _∉_ )
open import Data.List.Membership.Propositional.Properties using (∈-lookup)
open import Data.List.Relation.Unary.Any using (Any)

-- Certainly used local imports.
open import StreamGrids.NewSignoid
open import StreamGrids.Card
open import StreamGrids.Suffix
open import StreamGrids.Logic

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

        -- Idem for ≤.
        _≤C_ : Rel C _
        _≤C_ = cardTo≤ {card}

        NFList : Set
        NFList = List C

        idxToEl : C → A
        idxToEl = Signoid.idxToEl S

        elToIdx : A → C
        elToIdx = Signoid.elToIdx S

        invIdxElIdx
            : (i : C)
            → (elToIdx (idxToEl i)) ≡ i
        invIdxElIdx i = 
            let h = proj₂ (Signoid.inv S) in
            h {i} {idxToEl i} refl

    -- These inductive types are defined via mutual induction,
    -- so we declare them all up front here.
    data SGState : C → NFList → Set ℓ


    Q : Set _
    Q = Σ[ i ∈ C ](Σ[ L ∈ NFList ](SGState i L))

    -- Get the enumeration-index of the last element added to a choicelog.
    idx : Q → C
    idx (i , _ , _) = i

    -- Get the list of normal forms of a choicelog.
    nflist : Q → NFList
    nflist (_ , L , _) = L

    -- Get the last element added to a choicelog.
    el : Q → A
    el q = idxToEl (idx q)

    data LegalChoices : Q → Set ℓ
    UpdateNFList : (q : Q) → (h : IsNotMax (idx q)) → LegalChoices q → NFList
      
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
            → SGState (idxSuc h) (UpdateNFList q h lc)

    -- Macro.
    -- Given the data for an SGState successor s+ for s in q = (i , L , s),
    -- the index and NFList of s+ are already fixed as well.
    QSucc
        : {q : Q}
        → (h : IsNotMax (idx q))
        → (lc : LegalChoices q)
        → Q
    QSucc {q} h lc = (idxSuc h , UpdateNFList q h lc , choose q h lc)

--------------------------------------------------------------------------------
-- Substack (sub-choice-log) relation ⊑.
--------------------------------------------------------------------------------
    
    data _⋤_ where
        onechoice 
            : (q : Q) 
            → (h : IsNotMax (idx q))
            → (lc : LegalChoices q)
            → q ⋤ (idxSuc h , UpdateNFList q h lc , choose q h lc)
        multichoice
            : (q' q : Q)
            → (q' ⋤ q)
            → (h : IsNotMax (idx q))
            → (lc : LegalChoices q)
            → q' ⋤ (idxSuc h , UpdateNFList q h lc , choose q h lc)

    ⋤-trans : Transitive _⋤_
    --⋤-trans {q₁} {q₂} {q₃} q₁⋤q₂ q₂⋤q₃ = ?
    ⋤-trans {q₁} {q₂} {q₃@(i₃ , L₃ , s₃)} q₁⋤q₂ q₂⋤q₃@(onechoice q₂ h lc) = 
        multichoice q₁ q₂ q₁⋤q₂ h lc
    ⋤-trans {q₁} {q₂} {q₃@(i₃ , L₃ , s₃)} q₁⋤q₂ (multichoice q₂ q₄ q₂⋤q₄ h lc) =
        multichoice q₁ q₄ (⋤-trans q₁⋤q₂ q₂⋤q₄) h lc 

    -- Analogous to natural numbers: m < 1+n means m ≤ n,
    -- it holds q' ⋤ <some extension of q> → q' ⊑ q.
    -- This is FC-j in my notes.
    sublogLastChoice
        : {q' q : Q}
        → (h : IsNotMax (idx q))
        → (lc : LegalChoices q)
        → q' ⋤ QSucc h lc
        -- #TODO: what is better, the above macro or the full def below?
        --→ q' ⋤ (idxSuc h , UpdateNFList q h lc , choose q h lc)
        → q' ⊑ q
    sublogLastChoice {q'} {q} h lc (onechoice q h lc) = 
        let q'≡q = refl in
        inj₁ q'≡q
    sublogLastChoice {q'} {q} h lc (multichoice q' q q'⋤q h lc) = inj₂ q'⋤q
     

--------------------------------------------------------------------------------
-- Element representations.
-- #TODO: everything below getState (until, not including, the next header
-- comment) should be deprecated.
--------------------------------------------------------------------------------
    
    -- Substack definition of element-already-chosen-in-a-state.
    -- In contrast to the index-based definition (`iElem`, used in PhCore.agda).
    -- An element is identified with the prefix of the choice log up to the
    -- point where that element is added to the congruence.
    sElem : Q → Set ℓ
    sElem q = Σ[ q' ∈ Q ](q' ⊑ q)

    getState : {q : Q} → sElem q → Q
    getState {q} (q' , q'⊑q) = q' -- Same as proj₁
    
    -- Convert from sElem-representation of an element to the number
    -- it has in the enumeration of A.
    getIdx : {q : Q} → sElem q → C
    getIdx {q} q' = idx (getState (q'))

    -- Convert from sElem-representation of an element to the A-term
    -- it represents.
    getEl : {q : Q} → sElem q → A
    getEl {q} q' = Signoid.idxToEl S (getIdx q')

    ---- The relation _⊂_, but slightly modified to work on the sElem
    ---- representation of terms, rather than direct A terms.
    --sElem⊂ : {q : Q} → Rel (sElem q) _
    --sElem⊂ q' q'' = (getEl q') ⊂ (getEl q'')

    --infix 30 sElem⊂
    --syntax sElem⊂ q' q'' = q' ⊂* q''

    ---- _⊂I_ is the relation _⊂_, 
    ---- but slightly modified to work on the enumeration-index
    ---- representation of terms, rather than direct A terms.
    --iElem⊂ : Rel C _
    --iElem⊂ i i' = (idxToEl i) ⊂ (idxToEl i')

    --infix 30 iElem⊂
    --syntax iElem⊂ i i' = i ⊂I i'

    nextEl : {q : Q} → (h : IsNotMax (idx q)) → A
    nextEl h = idxToEl (idxSuc h)
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
            → (h : IsNotMax i)
            → Set _
    AllArgsNormal {i} {L} s h = 
                (x : sElem (i , L , s))
                → ((getEl x) ⊂ (nextEl {i , L , s} h)) 
                → (getIdx x) ∈ L

    -- Same as AllArgsNormal, but using the enumeration-index representation of
    -- elements.
    IAllArgsNormal
            : {i : C}
            → {L : NFList}
            → (s : SGState i L)
            → (h : IsNotMax i)
            → Set _
    IAllArgsNormal {i} {L} s h = 
                (x : C)
                → ((idxToEl x) ⊂ (nextEl {i , L , s} h))
                → x ∈ L

    -- Predicate that the next element y has an x ⊂ y
    -- such that x is NOT a normal form.
    NormalisibleArg
            : {i : C}
            → {L : NFList}
            → (s : SGState i L)
            → (h : IsNotMax i)
            → Set _
    NormalisibleArg {i} {L} s h
            = Σ[ x ∈ sElem (i , L , s) ](
                ((getEl x) ⊂ (nextEl {i , L , s} h))
                ×
                (getIdx x) ∉ L
                )

    -- Same as NormalisibleArg,
    -- but using the enumeration-index representation of elements.
    INormalisibleArg
            : {i : C}
            → {L : NFList}
            → (s : SGState i L)
            → (h : IsNotMax i)
            → Set _
    INormalisibleArg {i} {L} s h
            = Σ[ x ∈ C ](
                ((idxToEl x) ⊂ (nextEl {i , L , s} h))
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
            → (h : IsNotMax i)
            → (IAllArgsNormal s h)
            → LegalChoices (i , L , s)
        freeChoice
            : {i : C}
            → {L : NFList}
            → (s : SGState i L)
            → (h : IsNotMax i)
            → (IAllArgsNormal s h)
            → (Indices L)
            --^ (Index of) normal form to which we set the next element equal.
            → LegalChoices (i , L , s)
        forcedChoice
            : {i : C}
            → {L : NFList}
            → (s : SGState i L)
            → (h : IsNotMax i)
            → (INormalisibleArg s h)
            → LegalChoices (i , L , s)

    UpdateNFList (i , L , s) h (newNF s₁ _ x) = (idxSuc h) ∷ L
    UpdateNFList (i , L , s) h (freeChoice s₁ _ x x₁) = L
    UpdateNFList (i , L , s) h (forcedChoice s₁ _ x) = L

--------------------------------------------------------------------------------
-- Well-foundedness of _⋤_ and recursion principle for _⋤_.
--------------------------------------------------------------------------------

    rootLog : (h : (fin ℕ.zero) <∞ card) → Q
    rootLog h = ( nonzeroCardToZeroElem h 
                , nonzeroCardToZeroElem h ∷ [] 
                , root h)

    rootHasNoSublog
        : {q : Q}
        → {h : (fin ℕ.zero) <∞ card}
        → ¬ (q ⋤ rootLog h)
    rootHasNoSublog ()

    open import Induction.WellFounded as WF
    ⋤-wellFounded : WellFounded _⋤_
    ⋤-wellFounded (_ , L , root h) = 
        acc λ { q'⋤root → ⊥-elim (rootHasNoSublog q'⋤root) }
    ⋤-wellFounded (_ , L , choose q h lc) = acc f
        where
            f : {q' : Q} 
              → q' ⋤ (idxSuc h , UpdateNFList q h lc , choose q h lc) 
              → Acc _⋤_ q'
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

--------------------------------------------------------------------------------
-- Suffix of normal-forms-list relation.
--------------------------------------------------------------------------------
    

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
        → (i , L , s) 
          ⋤ 
          (idxSuc h , UpdateNFList (i , L , s) h lc , choose (i , L , s) h lc)
        → L ≼ UpdateNFList (i , L , s) h lc
    onechoiceSuffix {_} {L} {s} {_} {newNF s _ x} q⊑q = Suffix.there ≼-refl
    onechoiceSuffix {_} {L} {s} {_} {freeChoice s _ x x₁} q⊑q = ≼-refl
    onechoiceSuffix {_} {L} {s} {_} {forcedChoice s _ x} q⊑q = ≼-refl

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
        let ref = ≼-refl in
        subst (λ k → Suffix _≡_ (k ∷ []) (nonzeroCardToZeroElem h ∷ [])) 
            zeroh≡zeroh' ref
    -- Any q'⊑q where q has only the root element and q' at least
    -- two elements (`choose` as topmost constructor) is impossible.
    multichoiceSuffix {i'} {i} {L'} {L} {choose q h lc} {root k} (inj₁ ())
    multichoiceSuffix {i'} {i} {L'} {L} {choose q h lc} {root k} (inj₂ ())
    -- q'⊑q gives two cases. In the first case, q'≡q,
    -- i.e., (L' , s'_ = (L , choose q lc).
    -- Then trivially L' ≡ L as well, and ≼ is reflexive.
    multichoiceSuffix {i'} {i} {L'} {L} {s'} {choose q'' h lc} (inj₁ refl) 
        = ≼-refl
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
        let L₁≼L  = onechoiceSuffix {i₁} {L₁} {s₁} {h} {lc} (onechoice q₁ h lc) 
        in
        ≼-trans L'≼L₁ L₁≼L
        
    -- Same as above, but now with states wrapped into single elements.
    multichoiceSuffix'
        : {q' q : Q}
        → q' ⊑ q
        → (nflist q') ≼ (nflist q)
    multichoiceSuffix' {i' , L' , s'} {i , L , s}
        = multichoiceSuffix {i'} {i} {L'} {L} {s'} {s}

--------------------------------------------------------------------------------
-- Auxiliary lemmas needed to compute normal forms.
--------------------------------------------------------------------------------
--#TODO: rename the lemmas. Current names are the ones used in my paper notes.

    FC-a 
        : {i : C}
        → (h₁ : IsNotMax i)
        → (h₂ : IsNotMax i)
        → (idxSuc h₁ ≡ idxSuc h₂)
    FC-a {i} h₁ h₂ = endoSucUnique h₁ h₂


    -- Lemma FC-b : if there is an enumeration-index i smaller than
    -- the index of the last element added to choicelog q,
    -- then there exists a STRICT subchoicelog 
    -- of q where i was the last element added.
    -- (Strict subchoicelog is stronger than an sElem: it uses ⋤ i.o. ⊑).
    getSubLog
        : (q : Q)
        → (i : C)
        → (i <C idx q)
        → Σ[ q' ∈ Q ]( (q' ⋤ q) × (i ≡ idx q'))
    -- The hypothesis i<iq is impossible if q is a root log:
    -- i < nonzeroCardToZeroElem h is impossible.
    getSubLog (iq , L , root h) i i<iq = ⊥-elim (nothingIs<0 i h i<iq)
    getSubLog (iq , L , choose q' h lc) i i<iq 
        with cardToDecidableEq card i (idx q')
    -- If i = iq' then q' itself is already the choicelog we seek!
    ... | yes i≡iq' = (q' , onechoice q' h lc , i≡iq')
    -- In the last case, i ≢ iq', so (1) i > iq' xor (2) i < iq'. 
    -- But i < iq and iq = 1 + iq', so if i > iq' then 1 + iq' > i > iq',
    -- which means that (1 + iq') is at least 2 greater than iq'; contradiction.
    -- So only option (2) remains: i < iq'. Then we can recurse getSubLog
    -- and use transitivity of ⋤ (a sublog of q' is also a sublog of q).
    ... | no  i≢iq' with (cardTo<Dec {card} i (idx q'))
    ... | yes (i<iq') = 
        let (q'' , q''⋤q' , iq''≡i) = getSubLog q' i i<iq' in
        let q'⋤q = onechoice q' h lc in
        (q'' , ⋤-trans q''⋤q' q'⋤q , iq''≡i)
    -- The impossible case i > iq':
    ... | no  (i≮iq') = 
        let iq'<i = n≮m→n≢m→m<n i≮iq' i≢iq' in
        ⊥-elim (j<i<Sj-impossible {card} {i} {idx q'} {h} i<iq iq'<i)
    
    -- #TODO: it is possbile to define a 'getWeakSubLog'
    -- where the input is i ≤ (idx q) and the output
    -- is q' ⊑ q (i.o., q' ⋤ q).
    getWeakSubLog
        : (q : Q)
        → (i : C)
        → (i ≤C idx q)
        → Σ[ q' ∈ Q ]( (q' ⋤ q) × (i ≡ idx q'))
    -- #TODO: just remove this function if never needed.
    -- Then also remove _≤C_ !!!
    getWeakSubLog = ? 

    -- #TODO: remove if this does not turn out to be needed,
    -- otherwise finish.
    -- The index-index of a ChoiceLog corresponds 
    -- to the enumeration-index of the last element added.
    elToIdx∘el≡idx
        : (q : Q)
        → elToIdx (el q) ≡ idx q
    elToIdx∘el≡idx (i , L , root h) = {! !}
    elToIdx∘el≡idx (i , L , choose q h lc) = {! !}
        

    -- This is FC-e in my notes.
    argSmallerIdx
        : (q : Q)
        → (x : A)
        → (x ⊂ el q)
        → elToIdx x <C elToIdx (el q)
    argSmallerIdx q x x⊂q = 
        Signoid.subrelat S x (el q) x⊂q

    -- Incrementing the index of a ChoiceLog gives the same index
    -- as adding a choice to the ChoiceLog and projecting the index.
    -- #TODO: remove? This is completely trivial, at type level
    -- Agda only allows me to write `idxSuc h` in the RHS and `idx` is just
    -- `proj₁`...
    nextIdxUnique
        : (q' : Q)
        → (h : IsNotMax (idx q'))
        → (lc : LegalChoices q')
        → idxSuc h ≡ idx (idxSuc h , UpdateNFList q' h lc , choose q' h lc)
    nextIdxUnique q' h lc = refl

    -- The enumeration-indices in a NFList of a choice-log
    -- are ≤ than the enum-idx of the last element added to the choice-log.
    -- This is FC-i in my notes (notes FC3(3)).
    nfsAre≤
        : (q : Q)
        → (j : C)
        → j ∈ nflist q
        → j ≡ (idx q) ⊎ (cardTo< j (idx q))
    --nfsAre≤ q j j∈L = ?
    nfsAre≤ q j j∈L = ?
    
--!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
-- #TODO: redefine nf. Define nfTransposed() and nf().
--!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

    -- #TODO: comment description...
    NFOUT : Q → Set _
    NFOUT q' = (q : Q) → q' ⋤ q → Indices (nflist q')

    nfTransposed 
        : (q' : Q)
        --^ Subchoicelog whose normal form we want.
        -- The complete ChoiceLog q is hidden in NFOUT
        -- (instead of being the first argument to this function)
        -- hence the name `nfTransposed`.
        → ((q'' : Q) → q'' ⋤ q' → NFOUT q'')
        --^ Ability to make recursive calls.
        → NFOUT q'
    --nfTransposed q' recurse q q'⋤q = ?
    -- The normal form of the root element is always the root
    -- element itself, and is always the first normal form in the ChoiceLog,
    -- so has index 0 in the NFList.
    nfTransposed (i' , L' , root h') recurse q q'⋤q = Fin.zero
    nfTransposed 
        q'@(i' , L' , choose q'' h'' (newNF s h x)) 
        recurse q q'⋤q = {! !}
    nfTransposed 
        q'@(i' , L' , choose q'' h'' (freeChoice s h x x₁)) 
        recurse q q'⋤q = {! !}
    nfTransposed 
        q'@(i' , L' , choose q'' h'' 
        lc''@(forcedChoice {i''} {L''} s'' h''' (ix , x⊂nextq'' , ix∉L') )) 
        recurse q q'⋤q =
        let x = idxToEl ix in
        --let h''' = proj₁ q'⋤q in
        let h'''≡h'' = IsNotMax-irrel i'' h''' h'' in
        -- There is h'' and h''', which are not judgementally equal
        -- but definitely propositionally equal since `IsNotMax i''` is a prop.
        let x⊂nextq''h'' = subst (λ v → (x ⊂ nextEl {q''} v)) (h'''≡h'') x⊂nextq'' in
        -- The LHS of the following term is actually 
        -- elToIdx (idxToEl ix), not ix. However, these functions are inverse!
        -- Same problem applies to the RHS.
        let ix<iq'-almost = Signoid.subrelat S x (el q') x⊂nextq''h'' in
        -- Remove the invese functions from the LHS:
        let ixInv = invIdxElIdx ix in
        let ix<iq'-2 = subst (λ i → cardTo< i _) ixInv ix<iq'-almost in
        -- Now from the RHS:
        let iq'Inv = invIdxElIdx (idxSuc h'') in
        let ix<iq'-3 = subst (λ i → cardTo< _ i) iq'Inv ix<iq'-2 in
        -- Get the subchoicelog corresponding to the element x.
        let (qx , qx⋤q' , ix≡idxqx) = getSubLog q' ix ix<iq'-3 in
        let idxqx : C
            idxqx = idx qx
        in
        -- Get the normal form of x for any desired superlog of qx
        -- (this is the type NFOUTx').
        let NFOUTx' = recurse qx qx⋤q' in
        -- Specialise to the superlog q', which will give us 
        -- ix' as in index in L' (where L' is the NFList of qx, the choice log
        -- with x as last choice).
        -- From here we can prove that ix' < ix, 
        -- which we need to call Signoid.coerc to coerce along NF(X) ≈ x.
        let Lx : NFList
            Lx = nflist qx
        in
        let ix'-in-Lx : Indices Lx
            ix'-in-Lx = NFOUTx' q' qx⋤q' 
        in 
        let ix' : C
            ix' = lookup Lx ix'-in-Lx
        in
        let ix'∈Lx : ix' ∈ Lx
            ix'∈Lx = ∈-lookup {xs = Lx} ix'-in-Lx 
        in
        -- This is `ix'≡ix ⊎ ix'<ix` (but using cardTo<)
        let ix'≤ix : (ix' ≡ ix) ⊎ (cardTo< ix' ix)
            ix'≤ix = subst (λ k → ix' ≡ k ⊎ cardTo< ix' k) (sym ix≡idxqx) (nfsAre≤ qx ix' ix'∈Lx)
        in
        -- ix' cannot be ix, because ix' ∈ Lx
        -- but x is not a normal form, which was proven via ix ∉ L'
        -- (and x is an element in q', 
        -- and qx the corresponding subchoicelog of q',  so Lx ≼ L')
        -- So ix' ≡ ix would give ix ∈ Lx, a contradiction.
        --let qx⊑q'' = sublogLastChoice {qx} {q''} h'' lc'' qx⋤q' in
        --let Lx≼L'' = multichoiceSuffix' {qx} {q''} qx⊑q'' in
        let Lx≼L' : Lx ≼ L'
            Lx≼:' = multichoiceSuffix' {qx} {q'} (inj₂ qx⋤q')
        in
        let ix∉Lx : ix ∉ Lx
            ix∉Lx = notInListThenNotInSuffix Lx≼L' ix∉L' 
        in
        let ix'≢ix : ix' ≢ ix
            ix'≢ix = λ ix'≡ix → ⊥-elim (ix∉Lx (subst (λ j → j ∈ Lx) ix'≡ix ix'∈Lx)) 
        in
        --let ix'≢idxqx = λ ix'≡ix → ⊥-elim (ix∉Lx (subst (λ j → j ∈ Lx) ix'≡ix ix'∈Lx)) in
        --let ix'≢ix = subst _ ix≡idxqx ix'≢idxqx in
        let ix'<ix : cardTo< ix' ix
            ix'<ix = elimCaseLeft ix'≤ix ix'≢ix 
        in
        --let ix'<idxqx : cardTo< ix' idxqx
        --    ix'<idxqx = subst (λ k → cardTo< ix' k) ix≡idxqx ix'<ix
        --in
        let invix' : C
            invix' = elToIdx (idxToEl ix')
        in
        --let invix'<idxqx : cardTo< invix' idxqx
        --    invix'<idxqx = subst (λ k → cardTo< k idxqx) (sym (invIdxElIdx ix')) ix'<idxqx
        --in
        -- Hole:
        -- Goal: cardTo< (S .Signoid.elToIdx (idxToEl ix')) (S .Signoid.elToIdx x)
        let ix'≡invix' : ix' ≡ invix'
            ix'≡invix' = sym (invIdxElIdx ix')
        in
        let invix'<ix : cardTo< invix' ix
            invix'<ix = subst (λ k  → cardTo< k ix) ix'≡invix' ix'<ix
        in
        let ix≡elToIdxx : ix ≡ (elToIdx x)
            ix≡elToIdxx = sym (invIdxElIdx ix)
        in
        let invix'<elToIdxx : cardTo< invix' (elToIdx x)
            invix'<elToIdxx = subst (λ k  → cardTo< invix' k) ix≡elToIdxx invix'<ix
        in
        let meh : Σ[ y' ∈ A ](cardTo< (elToIdx y') (elToIdx (nextEl h'')))
            meh = Signoid.coerc S (nextEl h'') x x⊂nextq''h'' (idxToEl ix') invix'<elToIdxx in
        let (q* , idxq*<idxnextq'') = meh in
        {! !}
    --nfTransposed q'@(i' , L' , choose q'' h'' lc) recurse q q'⋤q with lc
    --... | newNF s h₁ x = {! !}
    --... | freeChoice s h₁ x x₁ = {! !}
    --... | forcedChoice {i''} {L''} s'' h'' (ix , x⊂nextq'' , ix∉L') = 
    --    let x = idxToEl ix in
    --    --let h''' = proj₁ q'⋤q in
    --    let ix<iq' = Signoid.subrelat S x (el q') {! x⊂nextq'' !} in
    --    let (qx , qx⋤q' , ix≡idxqx) = getSubLog q' ix ? in
    --    let x' = recurse qx ? in
    --    --let q* = Signoid.coerc 
    --    {! !}

    --nf  : {i : C}
    --    → {L : NFList}
    --    → {s : SGState i L} 
    --    → (x : sElem (i , L , s)) 
    --    → Indices L
    ---- We know that L' is [ 0 ].
    ---- Prove that L' is a sublist of L, then we know that 0 ∈ L.
    ---- * (SomeLemma x⊑q) should give L' ⊆ L.
    ---- * (SomeOtherLemma (L' , root h)) should give L' = [ 0 ],
    ----      or even only 0 ∈ L' is enough.
    --nf {i} {L} {s} ((i' , L' , root h) , x⊑q) = ?    
    --nf {i} {L} {s} ((i' , L' , choose (i'' , L'' , s'') h (newNF s'' x)) , x⊑q) = {! !}
    --nf {i} {L} {s} ((i' , L' , choose (i'' , L'' , s'') h (freeChoice s'' x x₁)) , x⊑q) = {! !}
    --nf {i} {L} {s} ((i' , L' , choose (i'' , L'' , s'') h (forcedChoice s'' x)) , x⊑q) = {! !}
    --    where
    --        q : Q
    --        q = (i , L , s)

    ---- #TODO: better define this in terms of sElem first,
    ---- thereafter make iElem version (with type as below)
    ---- that
    ---- 1. Maps an iElem to an sElem.
    ---- 2. Calls the sElem version of nf().
    ---- #TODO: 'Inf' stands for iElem-nf, but sounds like "infinite" as well.
    ----  Find a better name.
    --Inf 
    --    : {i : C}
    --    → {L : NFList}
    --    → {s : SGState i L}
    --    → (x : C)
    --    → (x <C height (i , L , s))
    --    → Indices L
    --Inf {L} {s} x x∈s = {! !}



    
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

