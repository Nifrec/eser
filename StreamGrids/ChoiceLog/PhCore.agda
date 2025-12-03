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
{-# OPTIONS --allow-unsolved-metas #-}

module StreamGrids.ChoiceLog.PhCore where

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
    record NoForcedCoercion {n : StateIndices} (q : SGState n) : Set ℓ
    data NormalForms : {n : StateIndices} → SGState n → Set ℓ
    --data _⊢_≈_ : {n : StateIndices} → SGState n → A → A → Set ℓ

    data SGState where
        root 
            : (fin ℕ.zero) <∞ card
            --^ *If* at least one element exists,...
            → SGState (cardToClipSuc StateIdxZero)
            --^ ...then there is a canonical root state with only that
            -- element explored (and the reflexive congruence on it).
        choose : {n : StateIndices} 
            → (q : SGState n) 
            → LegalChoices q 
            → SGState (StateIdxSuc n)


    -- Indices of elements that occur in q.
    -- q : SGState n has the elements A_0, A_1, ..., A_{n-1},
    -- so the indices are {0, 1, ..., n-1}.
    iElem : {n : StateIndices} → (q : SGState n) → Set _
    iElem {n} q = Σ[ i ∈ SIndices ](cardTo< (cardInject i) n)

    -- Mapping an index existing in q 
    iElemToTerm : {n : StateIndices} → {q : SGState n} → (i : iElem q) → A
    iElemToTerm (i , _) = Signoid.enum S i

    PredSucIsID
        : {c : ℕ} 
        → (n : cardToSet (fin (ℕ.suc c))) 
        → cardToPred (Fin.suc n) ≡ inject₁ n
    PredSucIsID {c} n = refl

    sucpredsuc≡suc
        : {c : ℕ} 
        → (n : Fin c) --^ Same as `cardToSet c` if `c > 0`.
        → ℕ.suc (toℕ (cardToPred {fin (ℕ.suc c)} (Fin.suc n))) ≡ toℕ (Fin.suc n)
    sucpredsuc≡suc {c} n = 
        let sn≡sn = refl {x = toℕ (Fin.suc n)} in
        let P = (λ x → x ≡ toℕ (Fin.suc n)) in
        subst P (sym (toℕ-inject₁ (Fin.suc n))) sn≡sn
        
    -- A number that is the predecessor of another number is never the maximum
    -- in a finite set.
    aPredecIsNotMax 
        : {c : ℕ∞}
        → {n : cardToSet c}
        → (cardTo< (cardToPred n) n)
        --^ This expresses that 0<n, in a convenient way!
        → IsNotMax (cardToPred n)
    -- To show, by def of IsNotMax:
    --  (cardToPred (Fin.suc n)) Data.Fin.< (fromℕ c)
    --  I.e., suc n ≤ c. Up to some type conversions.
    aPredecIsNotMax {fin (ℕ.suc c)} {Fin.suc n} (s≤s pn<n) =
        let sn≤c' = toℕ≤pred[n] {ℕ.suc c} (Fin.suc n) in
        let P = λ x → toℕ (Fin.suc n) Data.Nat.≤ x in
        let sn≤c = subst P (sym(toℕ-fromℕ c)) sn≤c' in
        --^ (suc n) : Fin (suc c) so (suc n) ≤ c.
        -- This actually already expresses that `suc n ≤ c`,
        -- but we need help Agda telling that the type conversions work out.
        let spsn≡sn = sym(sucpredsuc≡suc n) in
        subst (λ x → x Data.Nat.≤ toℕ (fromℕ c)) spsn≡sn sn≤c 
    aPredecIsNotMax {∞} {n} pn<n = tt

    -- #TODO: this only makes sense if n>0 right?
    SIndexToLastStateIndex 
        : {n : StateIndices} 
        → (cardTo< (cardToPred n) n)
        --^ This expresses that 0<n, in a convenient way!
        → Σ[ i ∈ SIndices ](cardToSuc i ≡ n)
    SIndexToLastStateIndex {n} = 
        let i = cardLower (cardToPred ?) in
        let si≡n = ? in
        {! (i , si≡n) !}
        --where
        --    pnNotMax : IsNotMax {suc∞ card} (n)
        --    pnNotMax = ?

    -- Get the last chosen element from a choicelog.
    lastIdx 
        : {n : StateIndices} 
        → (q : SGState n) 
        → Σ[ i' ∈ iElem q ](cardToSuc (proj₁ i') ≡ n)
    lastIdx {n} q =
        -- #TODO: lemma that SGState n inhabited -> n>0?
        let i' = (proj₁ (SIndexToLastStateIndex ?) , ?) in
        let iIsLast = ? in
        (i' , iIsLast)
    
    -- Trip a choice log down to the prefix of choices up to and
    -- including the point where A_i was chosen,
    -- discard the choices for A_{i+1}, A_{i+2}, ..., A_{n-1}.
    stripDownTo 
        : {n : StateIndices} 
        → (q : SGState n) 
        → (i : iElem q) 
        → (SGState (cardToSuc (proj₁ i)))
    stripDownTo {n} q (i , i<n) = ?

    -- Look up the normal form of the last chosen element,
    -- i.e., A_{n-1}, given a q state of index n.
    -- The normal form is the least representative of the equivalence
    -- class containing A_{n-1} according to the congruence encoded in q.
    -- #TODO: make `(cardTo< (proj₁ j) (proj₁ i))` more readable by defining
    -- a nice macro `S ⊢ j < i` or something like that.
    nfTop
        : {n : StateIndices}
        → (q : SGState n)
        → Σ[ j ∈ iElem q ](
            proj₁ j ≡  proj₁ (proj₁ (lastIdx q) )
            ⊎ 
            (cardTo< (proj₁ j) (proj₁ (proj₁ (lastIdx q))))
            )
    -- Agda has a really hard time with the root case.
    -- The problem is probably that `card` is a module variable 
    -- -- we cannot pattern match on it. 
    -- Consequently we can also not pattern-match `0<1` with a normal form.
    -- The best solution I found is prove a lot of sublemmas in which
    -- pattern-matching is possible.
    nfTop {n} (root 0<1) = 
        let i = nonzeroCardToZeroElem {card} 0<1 in
        let i∈root' = cardTo0<1 i in
        let P = (λ x → cardTo< (cardInject x) (cardToClipSuc StateIdxZero)) in
        let zeroRewr = thereIsOneZero (nonzeroCardToZeroElem 0<1) 0<1 in
        let i∈root = subst P zeroRewr i∈root' in
        (i , i∈root) , inj₁ {!refl !}
    nfTop {n} (choose q x) = {! !}

    isInState : {n : StateIndices} → (i : SIndices) → (q : SGState n) → Set _
    isInState {n} i q = cardTo< (cardToSuc i) n
    syntax isInState i q = i ∈ q 

    lemma4'
        : {n : StateIndices}
        → (q : SGState n)
        → (i' : iElem q)
        → (j : SIndices)
        → (h : (
            j ≡ (proj₁ (proj₁ (lastIdx (stripDownTo q i'))))
            ⊎
            (cardTo< j  (proj₁ (proj₁ (lastIdx (stripDownTo q i'))))))
            )
        → ((j ≡ proj₁ i') ⊎ (cardTo< (j) (proj₁ i')))

    lemma5
        : {n : StateIndices}
        → (q : SGState n)
        → (i' : iElem q)
        → (j' : iElem (stripDownTo q i'))
        → cardTo< (cardInject (proj₁ j')) n

    -- Look up the normal form of an already chosen term x in a state q.
    -- The normal form is the least representative of the equivalence
    -- class containing x according to the congruence encoded in q.
    -- x is represented by its index i in the enumeration of A.
    nfIdx
        : {n : StateIndices}
        → (q : SGState n)
        → (i' : iElem q)
        → Σ[ j' ∈ iElem q ](
            proj₁ j' ≡  proj₁ i'
            ⊎ 
            (cardTo< (proj₁ j') (proj₁ i'))
            )
    nfIdx {n} q i' = 
        (jLifted , (lemma4' q i' (proj₁ j) j≤i))
            where
                q' = stripDownTo q i'
                j' = nfTop q'
                j =  proj₁ j'
                j≤i = proj₂ j'
                jLifted : iElem q
                jLifted = (proj₁ j , lemma5 q i' j)
                

    -- Look up the normal form of an already chosen term x in a state q.
    -- The normal form is the least representative of the equivalence
    -- class containing x according to the congruence encoded in q.
    nf
        : {n : StateIndices}
        → (q : SGState n)
        → (x : A)
        → (idxx<n : cardTo< (cardInject (Signoid.getIdx S x)) n)
        --^ q has elements A_0, A_1, ..., A_{n-1}.
        -- So if the index of x is smaller than n, it is in q.
        → A
    nf {n} q x h = ?


    _⊢_≈_ : {n : StateIndices} → (q : SGState n) → (ix ix' : iElem q) → Set _
    q ⊢ ix ≈ ix' = (nf q x ?) ≡ (nf q x' ?)
        where
            x = iElemToTerm ix
            x' = iElemToTerm ix'


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
            i : iElem q
            i' : iElem q
            x'«x : iElemToTerm i' « iElemToTerm i 
            x⊂next : iElemToTerm i ⊂ next notMax
            x≈x' : q ⊢ i ≈ i'

    record NoForcedCoercion {n} q where
        inductive
        field
            notMax : IsNotMax n 
            i : iElem q
            i' : iElem q
            x'«x : iElemToTerm i' « iElemToTerm i 
            x⊂next : iElemToTerm i ⊂ next notMax
            x≉x' : ¬ (q ⊢ i ≈ i')
        --notforced 
        --    : {n : StateIndices}
        --    → (q : SGState n)
        --    → (notMax : IsNotMax n )
        --    → (x : A )
        --    → (x' : A )
        --    → (x' « x )
        --    → (x ⊂ next notMax )
        --    → ¬ (q ⊢ x ≈ x')
        --    → NoForcedCoercion q

    

    ---- #TODO: conjecture: 
    ---- IsAProp(q ⊢ x ≈ x') for all q, x, x'.
    ---- Proposition that the congruence encoded in q
    ---- relates x to x'.
    --data _⊢_≈_ where
    --    -- x is last element added to choice log, and a normal form, so related
    --    -- to only itself in the current state.
    --    hereNFRefl 
    --        : {n : StateIndices}
    --        → (notMax : IsNotMax n)
    --        → (q : SGState n)
    --        → (h : NoForcedCoercion q)
    --        → (choose q (newNF q h)) ⊢ (next notMax) ≈ (next notMax)
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

    module Lemmas where
        -- #TODO: rename and move those lemmas to right files/modules.

        -- If i < j then (suc i) ≤ j.
        -- j must be in a set with cardinality 1 greater than the set i is in.
        cardTo<→s≤ 
            : {n : ℕ∞} 
            → (i : cardToSet n) 
            → (j : cardToSet (suc∞ n)) 
            → (cardTo< (cardInject i) j) 
            → (cardTo≤ (cardToSuc i) j)
        cardTo<→s≤ {fin (ℕ.suc n)} i j i<j = 
            let h = sym (ℕSucCardToSucComm i) in
            subst (λ x → x Data.Nat.≤ toℕ j) h i<j
        cardTo<→s≤ {∞} i j i<j = i<j
       
        -- A term (i , p) : iElem q comes with a proof p : i < n.
        -- It follows that (i+1 ≤ n). 
        -- Regardless of the cardinality of StateIndices.
        lemma1 
             : {n : StateIndices} 
             → (q : SGState n) 
             → (i : iElem q) 
             → cardTo≤ (cardToSuc (proj₁ i)) n
        lemma1 {n} q (i , i<n) = cardTo<→s≤ i n i<n


        -- Proof that stripDownTo i' really strips down to the choice
        -- log where i' is the top element.
        lemma3
            : {n : StateIndices}
            → (q : SGState n)
            → (i' : iElem q)
            → (proj₁ (proj₁ (lastIdx (stripDownTo q i'))) ≡ proj₁ i')
        lemma3 {n} q (i , _) = ? -- refl should work AFTER implementing stripDownTo

        cardTo<→≤→<
            : {n : ℕ∞}
            → {x y z : cardToSet n}
            → (cardTo< x y)
            → (cardTo≤ y z)
            → (cardTo< x z)
        cardTo<→≤→< {fin (suc n)} = Data.Nat.Properties.<-≤-trans
        --^ Works because < and ≤ in finite sets are defined via ℕ.< and ℕ.≤.
        cardTo<→≤→< {∞} = Data.Nat.Properties.<-≤-trans

    open Lemmas

    lemma4' q i' j h = subst P (lemma3 q i') h
        where
            P = (λ x → (j ≡ x) ⊎ (cardTo< (j ) x))

    -- This can be used to prove that iElem of a stipped-down version
    -- of q, are also iElem of q itself.
    -- The iElem is then (proj₁ j' , lemma5 q j').
    lemma5 {n} q i' (j , hj) = 
        let i≤n = lemma1 {n} q i' in 
        let j<n = cardTo<→≤→< {suc∞ card} hj i≤n in
        j<n
