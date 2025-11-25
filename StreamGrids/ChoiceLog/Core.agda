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
-- States have an index, which is a number in the cardinality of the Signoid.
-- A state of index `n` encodes a congruence on A_0, A_1, ..., A_n,
-- i.e., a partially completed construction of an congruence on A.
-- Later states never introduce new relations between those first n+1 elements.
-- Going from a state of index n to a state of index n+1 involves
-- choosing which element A_{n+1} is equal to, or whether it is not equal
-- to any of the previous elements.
-- The possible choices are restricted at type level,
-- which ensures the resulting relation is a congruence.
-- For some states q of index n and elements A_{n+1} there might only be one
-- choice available due to the congruence constraint.

module StreamGrids.ChoiceLog.Core where

-- Certainly used standard library imports.
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product

-- Certainly used local imports.
open import StreamGrids.Signoid
open import StreamGrids.Card

module SGStates
    {ℓ : Level}
    {A : Set ℓ}
    {_«_ _⊂_ : Rel A ℓ}
    (S : Signoid _«_ _⊂_)
    (numelNonzero : Σ[ m ∈ ℕ∞ ](Signoid.numEl S ≡ suc∞ m))
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

        Szero = cardToZero card
        Ssuc = cardToSet card

        -- The associated '<' relation on the indices of A.
        _<S_ : Rel SIndices 0ℓ
        _<S_ = cardTo< {Signoid.numEl S}

    -- These inductive types are defined via mutual induction,
    -- so we declare them all up front here.
    data SGState : SIndices → Set _
    data LegalChoices : {n : SIndices} → SGState n → Set _

    data SGState where
        root : SGState Szero
        choose : {n : SIndices} → (q : SGState n) → LegalChoices q → SGState 
