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

{-# OPTIONS --allow-unsolved-metas #-}

module StreamGrids.ChoiceLog.NFListCore where

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

-- Certainly used local imports.
open import StreamGrids.NewSignoid
open import StreamGrids.Card

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
        card = Signoid.numEl S

        -- Existing indices in the enumeration of A.
        -- That's ℕ if A has infinitely many elements
        -- and Fin n otherwise.
        SIndices : Set
        SIndices = cardToSet card

        NFList : Set
        NFList = List SIndices

    -- These inductive types are defined via mutual induction,
    -- so we declare them all up front here.
    data SGState : NFList → Set ℓ
    Q : Set _
    Q = Σ[ L ∈ NFList ](SGState L)
    data LegalChoices : Q → Set ℓ
    UpdateNFList : (q : Q) → LegalChoices q → NFList
      
    -- `⊑` in Cornelis: `\sqsubseteq` or `\squb=`.
    data _⊑_ : Rel Q ℓ
    --record ForcedCoercion (q : SGState) : Set ℓ
    --record NoForcedCoercion (q : SGState ) : Set ℓ
    --NormalForms : SGState → Set ℓ
    --data _⊢_≈_ : SGState → A → A → Set ℓ

    data SGState where
        root 
            : (h : (fin ℕ.zero) <∞ card)
            --^ *If* at least one element exists,...
            → SGState ((nonzeroCardToZeroElem h) ∷ [])
            --^ ...then there is a canonical root state with only that
            -- element explored (and the reflexive congruence on it).
            -- The list of normal forms is [ 0 ].
        choose 
            : (q : Q)
            → (lc : LegalChoices q )
            → SGState (UpdateNFList q lc)


    -- Is-a-sub-ChoiceLog-of relation.
    -- A state/ChoiceLog q is a stack of choices,
    -- and q' ⊑ q denotes simply that q' is a substack of q.
    -- This relation forms a poset: reflexive, transitive, antisymmetric.
    data _⊑_ where
        refl : (q : Q) → q ⊑ q
        sub  : (q q' : Q)
             → (lc : LegalChoices q)
             → (q' ⊑ q)
             → q' ⊑ (UpdateNFList q lc , choose q lc)

    ⊑-refl : Reflexive _⊑_
    ⊑-refl {q} = refl q

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
    height : Q → SIndices
    height q = ?

    -- Convert from sElem-representation of an element to the A-term
    -- it represents.
    getEl : {q : Q} → sElem q → A
    getEl {q} q' = Signoid.enum S (height (getState (q')))

    -- The relation _⊂_, but slightly modified to work on the sElem
    -- representation of terms, rather than direct A terms.
    sElem⊂ : {q : Q} → Rel (sElem q) _
    sElem⊂ q' q'' = (getEl q') ⊂ (getEl q'')

    infix 30 sElem⊂
    syntax sElem⊂ q' q'' = q' ⊂* q''

    next : Q → A
    next q = ?

    data LegalChoices where
        newNF 
            : {L : NFList}
            → (s : SGState L)
            → (
                (x : sElem (L , s)) 
                → ((getEL x) ⊂ (next (L , s))) 
                → (getIdx (getEl x)) ∈ L
                )
            --^ Proof that no coercion constraint is at play:
            -- all arguments of the next-to-add element y ≔ next (L , s)
            -- are in normal f
        -- #TODO
    
    UpdateNFList (L , s) lc = ?

    --    forcedCoercion 
    --        : (q : SGState)
    --        --: (q q': SGState)
    --        --→ 
    --        --→ (choose q' (forcedCoercion q' 
    --        → (x : sElem q)
    --        → ((getEl x) ⊂ (next q))
    --        → (¬ (IsNF x))
    --        → LegalChoices q
    --    newEquiv
    --        : (q : SGState) 
    --        → (NoForcedCoercion q )
    --        → NormalForms q
    --        --^ Existing element we set the next element equal to.
    --        → LegalChoices q
    --    newNF 
    --        : (q : SGState) 
    --        → (NoForcedCoercion q )
    --        → LegalChoices q

    --IsNF : SGState → Set
    ---- The root element is always a normal form.
    --IsNF (root _)                     = ⊤
    --IsNF (choose q (coercion q fc))   = ⊥
    --IsNF (choose q (newEquiv q fc x)) = ⊥
    --IsNF (choose q (newNF q x))       = ⊤

    --NormalForms q = Σ[ x ∈  sElem q ]( IsNF (getState x))
    --NoForcedCoercion q = (x : sElem q) → (x ⊂* (next q)) → IsNF x
    ----^ All arguments of q are in normal form, so no congruence-coercion
    ---- is at play.

    ---- Compute the normal form of an sElem x.
    ---- The returned sElem is an sElem x' of `getState x`;
    ---- this is intentional since it proves that `x' « x`.
    ---- #TODO: add embedding into the super-choicelog.
    --nf  : {q : SGState} 
    --    → (x : sElem q) 
    --    → Σ[ x' ∈ sElem (getState x) ]( IsNF(getState x'))
    --nf {q} (root h , q'⊑q) = ((root h , ⊑-refl) , tt)
    --nf {q} (choose q' (coercion q' FC) , q'⊑q) = {! !}
    ---- If we equated x with some normal form x'', then return
    ---- just that normal form. Some overhead is needed to show that
    ---- x'' is also a normal form of getState(x).
    --nf {q} (choose q'' (newEquiv q'' noFC (x'' , isNFx'')) , q'⊑q) = 
    --    let q' = choose q'' (newEquiv q'' noFC (x'' , isNFx'')) in
    --    --^ State of the element of which we query the NF.
    --    let p = getState x'' in
    --    let q''⊑q' = sub q'' q'' (newEquiv q'' noFC (x'' , isNFx'')) (refl q'') 
    --    in
    --    let p⊑q' = ⊑-trans (proj₂ x'') q''⊑q' in
    --    ((proj₁ x'' , p⊑q') , isNFx'')
    ---- If x is a normal form, just return x itself!
    --nf {q} (choose q' (newNF q' noFC) , q'⊑q) = ((choose q' (newNF q' noFC) , ⊑-refl) , tt)


    
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

