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
{-# OPTIONS --allow-unsolved-metas #-}

module StreamGrids.ChoiceLog.SubSCore where

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

-- Certainly used local imports.
open import StreamGrids.Signoid
open import StreamGrids.Card

module SGStates
    {ℓ : Level}
    {A : Set ℓ}
    {_«_ _⊂_ : Rel A ℓ}
    (S : Signoid _«_ _⊂_)
    where

    -- Setting some abbreviations for some of the data of the Signoid
    -- for better readability.
    private 
        card : ℕ∞
        card = Signoid.numEl S

    -- These inductive types are defined via mutual induction,
    -- so we declare them all up front here.
    data SGState : Set ℓ
    data LegalChoices : SGState → Set ℓ
    -- `⊑` in Cornelis: `\sqsubseteq` or `\squb=`.
    data _⊑_ : Rel SGState ℓ
    record ForcedCoercion (q : SGState) : Set ℓ
    record NoForcedCoercion (q : SGState ) : Set ℓ
    NormalForms : SGState → Set ℓ
    --data _⊢_≈_ : SGState → A → A → Set ℓ

    data SGState where
        root 
            : (fin ℕ.zero) <∞ card
            --^ *If* at least one element exists,...
            → SGState 
            --^ ...then there is a canonical root state with only that
            -- element explored (and the reflexive congruence on it).
        choose 
            : (q : SGState) 
            → LegalChoices q 
            → SGState

    -- Is-a-sub-ChoiceLog-of relation.
    -- A state/ChoiceLog q is a stack of choices,
    -- and q' ⊑ q denotes simply that q' is a substack of q.
    -- This relation forms a poset: reflexive, transitive, antisymmetric.
    data _⊑_ where
        refl : (q : SGState) → q  ⊑ q
        sub  : (q q' : SGState)
             → (ℓ : LegalChoices q)
             → (q' ⊑ q)
             → q' ⊑ choose q ℓ

    ⊑-refl : Reflexive _⊑_
    ⊑-refl {q} = refl q

    ⊑-trans : Transitive _⊑_
    ⊑-trans {q} {q} {r} (refl q) q⊑r = q⊑r
    ⊑-trans {p} {q} {q} p⊑q (refl q) = p⊑q
    ⊑-trans {p} {q} {r} (sub q' p ℓq p⊑q') (sub r' (choose q' ℓq) ℓr q⊑r') =
        let q = choose q' ℓq in
        let q'⊑q = sub q' q' ℓq (refl q') in
        let p⊑q = ⊑-trans p⊑q' q'⊑q in
        let p⊑r' = ⊑-trans p⊑q q⊑r' in
        sub r' p ℓr p⊑r'

    ⊑-antisym : Antisymmetric _≡_ _⊑_
    ⊑-antisym {q} {q} (refl q) q⊑q = refl
    ⊑-antisym {q} {q} q⊑q (refl q) = refl
    ⊑-antisym {p} {q} (sub q' p ℓq p⊑q') (sub p' q ℓp q⊑p') = 
        let p'⊑p = sub p' p' ℓp (refl p') in
        let p'⊑q' = ⊑-trans p'⊑p p⊑q' in
        let q'⊑q = sub q' q' ℓq (refl q') in
        let q'⊑p' = ⊑-trans q'⊑q q⊑p' in
        let p'≡q' = ⊑-antisym p'⊑q' q'⊑p' in
        -- Still need ℓp = ℓq, given that we could
        -- apply cong pm p'≡q' with (λ x → choose x ℓp), and then subst the
        -- right occurrence of ℓp via ℓp=ℓq.
        --let pℓp≡qℓp = cong (λ x → choose x) p'≡q' (refl (choose p')) in
        {!  !}

    -- #TODO: conjecture: Totality and decidability of _⊑_ can also be proven.

    data LegalChoices where
        coercion 
            : (q : SGState) 
            → ForcedCoercion q 
            → LegalChoices q
        newEquiv
            : (q : SGState) 
            → (NoForcedCoercion q )
            → NormalForms q
            --^ Existing element we set the next element equal to.
            → LegalChoices q
        newNF 
            : (q : SGState) 
            → (NoForcedCoercion q )
            → LegalChoices q

    NormalForms q = ?

    record ForcedCoercion q where
        inductive
    --        i : iElem q
    --        i' : iElem q
    --        x'«x : iElemToTerm i' « iElemToTerm i 
    --        x⊂next : iElemToTerm i ⊂ next notMax
    --        x≈x' : q ⊢ i ≈ i'

    record NoForcedCoercion q where
        inductive
    --        notMax : IsNotMax n 
    --        i : iElem q
    --        i' : iElem q
    --        x'«x : iElemToTerm i' « iElemToTerm i 
    --        x⊂next : iElemToTerm i ⊂ next notMax
    --        x≉x' : ¬ (q ⊢ i ≈ i')

    
--------------------------------------------------------------------------------
-- Maybe keep, maybe move, maybe remove.
--------------------------------------------------------------------------------
    --next : {n : StateIndices} → IsNotMax n → A
    --next {n} notMax = Signoid.enum S (cardLower notMax)


