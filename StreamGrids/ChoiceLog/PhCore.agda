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

module StreamGrids.ChoiceLog.PhCore where

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
    data SGState : StateIndices → Set ℓ
    data LegalChoices : {n : StateIndices} → SGState n → Set ℓ
    record ForcedCoercion {n : StateIndices}  (q : SGState n) : Set ℓ
    data NoForcedCoercion : {n : StateIndices} → SGState n → Set ℓ
    data NormalForms : {n : StateIndices} → SGState n → Set ℓ
    data _⊢_≈_ : {n : StateIndices} → SGState n → A → A → Set ℓ

    data SGState where
        empty : SGState StateIdxZero
        choose : {n : StateIndices} 
            → (q : SGState n) 
            → LegalChoices q 
            → SGState (StateIdxSuc n)


    --ForcedCoercion : {n : StateIndices} → SGState n → Set _
    next : {n : StateIndices} → IsNotMax n → A
    next {n} notMax = Signoid.enum S (cardLower notMax)

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

    record ForcedCoercion {n} q where
        inductive
        field
            notMax : IsNotMax n 
            x : A 
            x' : A 
            x'«x : x' « x 
            x⊂next : x ⊂ next notMax
            x≈x' : q ⊢ x ≈ x'

    data NoForcedCoercion where
        notforced 
            : {n : StateIndices}
            → (q : SGState n)
            → (notMax : IsNotMax n )
            → (x : A )
            → (x' : A )
            → (x' « x )
            → (x ⊂ next notMax )
            → ¬ (q ⊢ x ≈ x')
            → NoForcedCoercion q

    -- #TODO: conjecture: 
    -- IsAProp(q ⊢ x ≈ x') for all q, x, x'.
    -- Proposition that the congruence encoded in q
    -- relates x to x'.
    data _⊢_≈_ where
        -- x is last element added to choice log, and a normal form, so related
        -- to only itself in the current state.
        hereNFRefl 
            : {n : StateIndices}
            → (notMax : IsNotMax n)
            → (q : SGState n)
            → (h : NoForcedCoercion q)
            → (choose q (newNF q h)) ⊢ (next notMax) ≈ (next notMax)
    --    -- x is last element added to the choice log via a forced coercion.
    --    hereForced
    --        : {n : StateIndices}
    --        → (notMax : IsNotMax n)
    --        → (q : SGState n)
    --        -- The next arguments are the data that witnesses a ForcedCoercion.
    --        -- It is the same data as the `forced` constructor of that type.
    --        → (x : A )
    --        → (x' : A )
    --        → (x'«x : x' « x )
    --        → (x⊂next :  x ⊂ next notMax)
    --        → (x≈x' : q ⊢ x ≈ x')
    --        -- #TODO: maybe make a getter for the coercion instead of writing
    --        -- proj₁ here, for readability!
    --        → (choose q (coercion q (forced q notMax x x' x'«x x⊂next x≈x')) ⊢ (next notMax) ≈ (
    --            proj₁ (Signoid.coercion S {next notMax} {x} {x'} x⊂next x'«x)
    --            ))
    --    -- x is last element added to the choice log, via a free choice.
    --    hereFreeChoice : ?
    --    -- x is not the last element added to the choice log,
    --    -- but a prefix of the choice log proves x ≈ x',
    --    -- which does not change when adding the subsequent choices
    --    -- to the choice log.
    --    there : ?

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
        -- First element of the signoid (with number 0 in the enumeration).
        root 
            : IsNotMax StateIdxZero 
            → (q : SGState (StateIdxSuc StateIdxZero)) 
            → NormalForms q
        -- Topmost entry in the ChoiceLog is introduction of a new normal form,
        -- pick that normal form.
        here 
            : {n : StateIndices} 
            → (q : SGState n) 
            → (h : NoForcedCoercion q)
            → NormalForms(choose q (newNF q h))
        -- Pick a normal form from further down the choice log.
        there
            : {n : StateIndices}
            → (q : SGState n)
            → (c : LegalChoices q)
            --^ Arbitrary topmost choice in the log we are not interested in.
            → NormalForms q
            --^ The normal form of the sub-choice-log.
            → NormalForms (choose q c)
