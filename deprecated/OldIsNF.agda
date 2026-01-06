-- Module      : StreamGrids.Construction
-- Description : Alternative definitions of normality
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : broken
--------------------------------------------------------------------------------

module deprecated.OldIsNF where

module DeprecatedIsNFDefs where
    {ℓ : Level}
    {A : Set ℓ}
    {_⊂_ : Rel A ℓ}
    (S : Signoid _⊂_)
    where

    -- Predicate whether the most recent element is a normal form,
    -- which it is iff constructed via the `root _` or `choose ... newNf ...`
    -- constructors.
    IsNFState : Q → Set
    IsNFState (_ , _ , root h) = ⊤
    IsNFState (_ , _ , choose _ _ (newNF _ _ _)) = ⊤
    IsNFState (_ , _ , choose _ _ (freeChoice _ _ _ _)) = ⊥
    IsNFState (_ , _ , choose _ _ (forcedChoice _ _ _)) = ⊥

    IsNFInState
        : (q : Q)
        → (i : C)
        → (i<idxq : i <C q)
        → Set
    IsNFInState q i i<idxq = IsNFState (proj₁ (SGStates.getSubLog q i i<idxq))

    -- Check if an element becomes a normal form in the choice log
    -- generated inductively from the empty choice log by the given decider.
    -- Construct the choice log up to the point where x is the most recent
    -- added, then check if it uses the `root` or `choose ... newNf ...`
    -- constructors.
    IsNFInSG : Decider → A → Set
    IsNFInSG D x = IsNFState (iterTill S D (elToIdx x))

    -- #TODO: rename, maybe move
    sublemma
        : (i : C)
        → (j : Indices (nflist (iterTill i))
        → IsNF ( lookup (nflist (iterTill i)) j)
    sublemma = ? -- This was never finished

    -- The next theorem asserts that the output of nfGlobalIdx (and hence
    -- nfGlobal as well) is indeed always a normal form.
    --
    -- It is very specific to this way of computing the normal form,
    -- since nfGlobal assumes no choice log has been given in advance,
    -- and builds up a new choicelog from an empty start.
    -- #TODO: it would also be convenient to prove that all elements
    -- of the nflist of any given preexisting choicelog are normal 
    -- -- but then cannot be normal w.r.t.
    -- to a Decider cuz the choicelog might have been build by multiple deciders
    -- alternatingly. 
    -- This would require a strip-down definition of `IsNF` that digs into a
    -- given choicelog until it finds the desired element,
    -- and checks there how it has been constructed.
    nfGlobalIsNF
        : ( i : C)
        → IsNF (nfGlobalIdx i)
    nfGlobalIsNF i = ?
