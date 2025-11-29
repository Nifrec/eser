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
open ≡-Reasoning
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Fin
open import Data.Fin.Properties

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

    -- Indices of elements that occur in q.
    -- q : SGState n has the elements A_0, A_1, ..., A_{n-1},
    -- so the indices are {0, 1, ..., n-1}.
    iElem : {n : StateIndices} → (q : SGState n) → Set _
    iElem {n} q = Σ[ i ∈ SIndices ](cardTo< (cardInject i) n)

    -- Mapping an index existing in q 
    iElemToTerm : {n : StateIndices} → {q : SGState n} → (i : iElem q) → A
    iElemToTerm (i , _) = Signoid.enum S i

    SIndexToLastStateIndex 
        : (n : StateIndices) 
        → Σ[ i ∈ SIndices ](cardToSuc i ≡ n)
    SIndexToLastStateIndex n = ?

    lastIdx : {n : StateIndices} → (q : SGState n) → iElem q
    lastIdx {n} q = (proj₁ (SIndexToLastStateIndex n) , ?)
    
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
            proj₁ j ≡  proj₁ (lastIdx q) 
            ⊎ 
            (cardTo< (proj₁ j) (proj₁ (lastIdx q)))
            )
    nfTop {n} q = ?

    isInState : {n : StateIndices} → (i : SIndices) → (q : SGState n) → Set _
    isInState {n} i q = cardTo< (cardToSuc i) n
    syntax isInState i q = i ∈ q 

    iElemLift 
        : {n m : StateIndices} 
        → (cardTo< m n) 
        → {q : SGState n}
        → {q' : SGState m}
        → {i : SIndices}
        → (i ∈ q')
        → (i ∈ q)
    iElemLift = ?

    lemma4
        : {n : StateIndices}
        → (q : SGState n)
        → (i' : iElem q)
        → (j' : iElem (stripDownTo q i'))
        → (h : (proj₁ j' ≡ proj₁ (lastIdx (stripDownTo q i')))
            ⊎
            (cardTo< (proj₁ j' ) (proj₁ (lastIdx (stripDownTo q i'))))
            )
        → ((proj₁ j' ≡ proj₁ i') ⊎ (cardTo< (proj₁ j') (proj₁ i')))

    lemma4'
        : {n : StateIndices}
        → (q : SGState n)
        → (i' : iElem q)
        → (j : SIndices)
        → (h : (j ≡ proj₁ (lastIdx (stripDownTo q i')))
            ⊎
            (cardTo< (j ) (proj₁ (lastIdx (stripDownTo q i'))))
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
        --let q' = stripDownTo q i' in
        -- TODO: need define q' < q and prove (i ∈ q') → (i ∈ q).
        -- The latter should be trivial.
        --let (j , j≤i ) =  nfTop q' 
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

        cardTo≤ : {n : ℕ∞} → Rel (cardToSet n) 0ℓ
        cardTo≤ {fin 0} ()
        cardTo≤ {fin (suc n)} = Data.Fin._≤_
        cardTo≤ {∞} = Data.Nat._≤_

        ℕSucCardToSucComm 
            : {n : ℕ}
            → (i : cardToSet (fin n)) 
            → toℕ (cardToSuc i) ≡ ℕ.suc (toℕ (cardInject i))
        ℕSucCardToSucComm {ℕ.suc n} i = begin
              toℕ (cardToSuc i) 
                ≡⟨ refl ⟩
              ℕ.suc (toℕ i) 
                ≡⟨ cong ℕ.suc (sym (toℕ-inject₁ i)) ⟩
              ℕ.suc (toℕ (cardInject i))
              ∎

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

        -- If j < (suc i) then j ≤ i.
        card<s→≤ 
            : {n : ℕ∞} 
            → {i j : cardToSet n} 
            → (cardTo< (cardInject j) (cardToSuc i) )
            --^ Note: this < lives in `cardToSet (suc∞ n)`.
            → (cardTo≤ j i)
            --^ Note: this ≤ lives in `cardToSet n`.
        card<s→≤ {fin (ℕ.suc n)} {i} {j} j<si = 
            let h = ℕSucCardToSucComm i in
            let P = (λ x → ℕ.suc (toℕ (cardInject j)) Data.Nat.≤ x) in
            let sjℕ≤si = subst P h j<si in
            -- Let's first strip away the ℕ.suc from both sides.
            let jℕ≤i = ≤-pred sjℕ≤si in
            -- Next, strip away the toℕ ∘ inject₁ from both sides.
            --let j≤i = toℕ-cancel-≤ jℕ≤i in -- That doesn't help
            let hj = toℕ-inject₁ j in
            let hi = toℕ-inject₁ i in
            let j≤i' = subst (λ x → x Data.Nat.≤ (toℕ (inject₁ i))) hj jℕ≤i in
            let j≤i = subst (λ x → toℕ j Data.Nat.≤ x) hi j≤i' in
            j≤i
        card<s→≤ {∞} {i} {j} i<j = ≤-pred i<j

        -- In my use case: q' = stripDownTo q i'.
        lemma2
            : {n : StateIndices}
            → (i : SIndices)
            → (q' : SGState (cardToSuc i))
            → (j' : iElem q')
            → cardTo≤ {card} (proj₁ j') i
        lemma2 i q' (j , h) = card<s→≤ {card} {i} {j} h

        -- Proof that stripDownTo i' really strips down to the choice
        -- log where i' is the top element.
        lemma3
            : {n : StateIndices}
            → (q : SGState n)
            → (i' : iElem q)
            → (proj₁ (lastIdx (stripDownTo q i')) ≡ proj₁ i')
        lemma3 {n} q (i , _) = ? -- refl should work AFTER implementing stripDownTo

        cardTo<Trans
            : {n : ℕ∞}
            → Transitive (cardTo< {n})
        cardTo<Trans {fin (ℕ.suc n)} = Data.Fin.Properties.<-trans
        cardTo<Trans {∞} = Data.Nat.Properties.<-trans

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

    lemma4 q i' j' h = subst P (lemma3 q i') h
        where
            P = (λ x → (proj₁ j' ≡ x) ⊎ (cardTo< (proj₁ j' ) x))

    lemma4' q i' j h = subst P (lemma3 q i') h
        where
            P = (λ x → (j ≡ x) ⊎ (cardTo< (j ) x))
    cardTo<s
        : {n : ℕ∞}
        → (i : cardToSet n)
        → cardTo< {suc∞ n} (cardInject i) (cardToSuc i)
    cardTo<s i = ?

    cardTo≤Lift
        : {n : ℕ∞}
        → {j i : cardToSet n}
        → (cardTo≤ {n} j i)
        → (cardTo≤ {suc∞ n} (cardInject j) (cardInject i))
    cardTo≤Lift {n} {j} {i} j≤i = ?
    
    -- If j < (suc i) then j ≤ i.
    card<s→≤Lifted
        : {n : ℕ∞} 
        → {i j : cardToSet n} 
        → (cardTo< {suc∞ n} (cardInject j) (cardToSuc i) )
        --^ Note: this < lives in `cardToSet (suc∞ n)`.
        → (cardTo≤ {suc∞ n} (cardInject j) (cardInject i))
    card<s→≤Lifted {n} {i} {j} j<si = ?

    -- This can be used to prove that iElem of a stipped-down version
    -- of q, are also iElem of q itself.
    -- The iElem is then (proj₁ j' , lemma5 q j').
    lemma5 {n} q i' (j , hj) = 
        let q' = (stripDownTo q i') in
        let j≤i = (lemma2 {n} (proj₁ i') q' (j , hj)) in
        let injj≤inji = cardTo≤Lift {card} j≤i in
        let injj<suci = card<s→≤Lifted {card} {proj₁ i'} {j} hj in
        --let injj<sucinji = cardTo<Trans {suc∞ card} injj<inji (cardTo<s {card} (proj₁ i')) in
        --let j<i = cardTo<Lift {card} (lemma2 {n} (proj₁ i') q' (j , hj)) in
        let i≤n = lemma1 {n} q i' in 
        let j<n = cardTo<→≤→< {suc∞ card} hj i≤n in
        j<n
        --j<n
