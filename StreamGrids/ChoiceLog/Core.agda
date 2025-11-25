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
-- States have an index, which is a number in 
-- the successor cardinality of the Signoid.
-- A state of index `n` encodes a congruence the first n elements
-- of the signoid (A_0, A_1, ..., A_{n-1}),
-- i.e., a partially completed construction of an congruence on A.
-- Later states never introduce new relations between those first n elements.
-- Going from a state of index n to a state of index n+1 involves
-- choosing which element A_{n} is equal to, or whether it is not equal
-- to any of the previous elements.
-- The possible choices are restricted at type level,
-- which ensures the resulting relation is a congruence.
-- For some states q of index n and elements A_{n} there might only be one
-- choice available due to the congruence constraint.
--
-- We index states not by the cardinality of the Signoid itself
-- (which would mean that a state of index n has the n+1 elements up to and
-- including the element with index n, i.e., A_0, A_1, ..., A_{n+1}),
-- since this would run into problems with Signoids of cardinality 0;
-- no SG state could then be defined (since A_0 doesn't exist),
-- not even an initial state.

module StreamGrids.ChoiceLog.Core where

-- Certainly used standard library imports.
open import Level
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Nat

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

        -- Existing indices in the enumeration of A.
        -- That's ℕ if A has infinitely many elements
        -- and Fin n otherwise.
        SIndices : Set
        SIndices = cardToSet card

        StateIndices : Set
        StateIndices = cardToSet (suc∞ card)

        StateIdxZero : StateIndices
        StateIdxZero = cardToZero card

        StateIdxSuc : StateIndices → StateIndices
        StateIdxSuc = cardToClipSuc {suc∞ card}

        -- The associated '<' relation on the indices of A.
        _<S_ : Rel SIndices 0ℓ
        _<S_ = cardTo< {Signoid.numEl S}

    -- These inductive types are defined via mutual induction,
    -- so we declare them all up front here.
    data SGState : StateIndices → Set _
    data LegalChoices : {n : StateIndices} → SGState n → Set _
    data ForcedCoercion : {n : StateIndices} → SGState n → Set _
    data NoForcedCoercion : {n : StateIndices} → SGState n → Set _
    data NormalForms : {n : StateIndices} → SGState n → Set _

    data SGState where
        empty : SGState StateIdxZero
        choose : {n : StateIndices} 
            → (q : SGState n) 
            → LegalChoices q 
            → SGState (StateIdxSuc n)


    --ForcedCoercion : {n : StateIndices} → SGState n → Set _
    _⊢_≈_ : {n : StateIndices} → SGState n → A → A → Set _
    next : {n : StateIndices} → IsNotMax n → A
    next {n} notMax = Signoid.enum S (cardLower notMax)

    q ⊢ x ≈ x' = ?

    data LegalChoices where
        coercion 
            : {n : StateIndices} 
            → (q : SGState n) 
            → ForcedCoercion q 
            → LegalChoices q
        newEquiv
            : {n : StateIndices} 
            → (q : SGState n) 
            → (NoForcedCoercion q )
            → NormalForms q
            --^ Existing element we set the next element equal to.
            → LegalChoices q
        newNF 
            : {n : StateIndices} 
            → (q : SGState n) 
            → (NoForcedCoercion q )
            → LegalChoices q

    data ForcedCoercion where
        forced 
            : {n : StateIndices}
            → (q : SGState n)
            → (h : IsNotMax n )
            → (x : A )
            → (x' : A )
            → (x' « x )
            → (x ⊂ next h)
            → (q ⊢ x ≈ x')
            → ForcedCoercion q

    data NoForcedCoercion where
        notforced 
            : {n : StateIndices}
            → (q : SGState n)
            → (h : IsNotMax n )
            → (x : A )
            → (x' : A )
            → (x' « x )
            → (x ⊂ next h )
            → ¬ (q ⊢ x ≈ x')
            → NoForcedCoercion q

    -- This does not work if (A : Set ℓ) and ℓ ≠ 0ℓ.
    --ForcedCoercion {n} q = 
    --    Σ[ h ∈ IsNotMax n ](
    --    Σ[ x ∈ A ](
    --    Σ[ x' ∈ A ](
    --    Σ[ x'«x ∈ x' « x ](
    --    Σ[ x⊂y ∈ x ⊂ next h q ](
    --    q ⊢ x ≈ x'
    --    )))))
        


    data NormalForms where
        root 
            : IsNotMax StateIdxZero 
            → (q : SGState (StateIdxSuc StateIdxZero)) 
            → NormalForms q
        --^ First element of the signoid.
        here 
            : {n : StateIndices} 
            → (q : SGState n) 
            → (h : NoForcedCoercion q)
            → NormalForms(choose q (newNF q h))
        --^ Topmost entry in the ChoiceLog is introduction of a new normal form,
        -- pick that normal form.
        there : ?
        --^ Pick a normal form from further down the choice log.
