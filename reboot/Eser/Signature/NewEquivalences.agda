-- Description : Equivalence between two representations of term algebras.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Correspondence theorems:
--
-- 1. ClosedTerms and RoundedTerms are in bijection, i.e., represent the same
--  term algebra (up to renaming elements).
-- 2. All `Round i` are finite sets; RoundedTerms is their disjoined union
--  (i.e., Σ[ i ∈ ℕ ](Round i) ), so a ℕ-indexed union of finite sets.
--  Hence it is equivalent to ℕ.
-- 3. Corollary of 1. and 2.: ClosedTerms ≃ RoundedTerms ≃ ℕ
--------------------------------------------------------------------------------
open import Data.List.Relation.Unary.Any using (here ; there)
open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties using (¬-not ; not-¬)
open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Unit
open import Data.Empty
open import Relation.Unary using (Decidable)
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Data.Fin hiding (_≤_ ; _≤?_ ; _<_ ; _>_ ; _+_)
open import Data.List
open import Data.List.Properties using (map-∘ ; length-map)
open import Data.Vec hiding (restrict ; length ; map)
open import Induction.WellFounded
open import Data.Nat.Induction using (<-Rec)
open import Data.Nat.Properties using (≤-refl ; n<1+n ; <-trans ; m<n⇒0<n ; <⇒≢
    ; ≤-trans ; n∸n≡0 ; pred[m∸n]≡m∸[1+n] ; suc-pred) 
open import Data.Vec.Properties using (length-toList) 
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Function hiding (_↔_)
open ≡-Reasoning
open import Data.List.Membership.Propositional using (_∈_ ; _∉_ )
open import Data.List.Membership.Propositional.Properties using (∈-length)
open import Data.List.Extrema.Nat

open import Eser.Logic using (elimCaseRight)
open import Eser.Definitions using (_≈_ ; indices ; _≃_ ; HomotEquivalence)
open HomotEquivalence
open import Eser.Mergings using (Merging ; unmergeMax ; UnmergeMaxOutp 
    ; mergelenLemma ; VMerging ; compileMerging ; compileMembership
    ; compileMembershipMapCongr)
open import Eser.ListMaxima using (nonemptyThenHasMax)
open import Eser.Signature.Definitions hiding (getArity)
open TerseSignature
open import Eser.Signature.Subterm
open import Eser.Aux

module Eser.Signature.NewEquivalences where

-- Auxiliary lemma.
-- Given a list of tuples (x , qx , ...) where qx proves that f x ≢ M
-- then we know that the f-map of the first projections of the list does not
-- contain M.
not∈lemma 
    : {A C : Set}
    → {B : A → Set}
    → (L : List (Σ[ a ∈ A ] B a))
    → (f : A → C)
    → (M : C)
    → (z : (x : Σ[ a ∈ A ] B a) → f (proj₁ x) ≢ M)
    → (M ∉ map (f ∘ proj₁) L)
not∈lemma (x ∷ L) f M z (here px) = z x (sym px)
not∈lemma (x ∷ L) f M z (there M∈mapL) = not∈lemma L f M z M∈mapL

-- If a number is bigger than 0 and ≤ than ℓ,
-- then it is the successor of a number in [0, ..., ℓ-1].
getPredec
    : {k ℓ : ℕ}
    → k ≤ ℓ
    → 0 < k
    → Σ[ m ∈ Fin ℓ ](ℕ.suc (toℕ m) ≡ k)
getPredec {ℕ.suc k} {ℓ} k≤ℓ 0<k = 
    let m = fromℕ< (≤-trans ≤-refl k≤ℓ)
    in
    let toℕm≡k = toℕ-fromℕ< (≤-trans ≤-refl k≤ℓ)
    in
    (m , cong ℕ.suc toℕm≡k)

--------------------------------------------------------------------------------
-- Auxiliary functions to extract some data out of a term
--------------------------------------------------------------------------------

-- Get fundamental constructor 'kind' of the term: 
-- nullary/multiary and pure/external-ℕ-arg.
getConstrKind
    : {S : TerseSignature}
    → {n : ℕ}
    → (t : OpenTerms S n)
    → ConstrKind
getConstrKind (mk-pure-nullary _) = c-pure-nullary
getConstrKind (mk-ℕ-nullary _ _) = c-ℕ-nullary
getConstrKind (argless-pure-multiary _) = c-pure-multiary
getConstrKind (argless-ℕ-multiary _ _) = c-ℕ-multiary
getConstrKind (giveArg t _) = getConstrKind t

kindToIndexSet
    : (S : TerseSignature)
    → ConstrKind
    → Set
kindToIndexSet S c-pure-nullary = Fin (pure-nullary S)
kindToIndexSet S c-ℕ-nullary = Fin (ℕ-nullary S)
kindToIndexSet S c-pure-multiary = indices (pure-multiary S)
kindToIndexSet S c-ℕ-multiary = indices (ℕ-multiary S)

-- Get index of constructor in signature.
-- Note that the type of the index depends on the kind of the constructor.
getConstrIdx
    : {S : TerseSignature}
    → {n : ℕ}
    → (t : OpenTerms S n)
    → kindToIndexSet S (getConstrKind t)
getConstrIdx {S} (mk-pure-nullary c) = c
getConstrIdx {S} (mk-ℕ-nullary c _) = c
getConstrIdx {S} (argless-pure-multiary c) = c
getConstrIdx {S} (argless-ℕ-multiary c _) = c
getConstrIdx {S} (giveArg t _) = getConstrIdx t

getArity 
    : {S : TerseSignature}
    → {n : ℕ}
    → (t : OpenTerms S n)
    → ℕ
getArity {S} (mk-pure-nullary _) = 0
getArity {S} (mk-ℕ-nullary _ _) = 0
getArity {S} (argless-pure-multiary c) = 
    ℕ.suc (Data.List.lookup (pure-multiary S) c)
getArity {S} (argless-ℕ-multiary c x) = 
    ℕ.suc (Data.List.lookup (ℕ-multiary S) c)
getArity {S} (giveArg t _) = getArity t

Sn∸n≡1
    : (n : ℕ)
    → ℕ.suc n ∸ n ≡ 1
Sn∸n≡1 n = 
    begin 
        ℕ.suc n ∸ n 
    ≡⟨ ∸-suc {n} {n} (≤-refl) ⟩
        ℕ.suc (n ∸ n)
    ≡⟨ cong ℕ.suc (n∸n≡0 n) ⟩
        ℕ.suc (ℕ.zero)
    ≡⟨⟩
        1
    ∎
    

-- Auxiliary lemma proving that terms of the form `giveArg t a`
-- always have at least one argument.
nonzeroArgsLemma
    : {S : TerseSignature}
    → {n : ℕ}
    → (t : OpenTerms S (ℕ.suc n))
    → (a : ClosedTerms S)
    → 1 ≤ getArity (giveArg t a) ∸ n
nonzeroArgsLemma {S} {n} (argless-pure-multiary c) a = 
    let 1≤1 : 1 ≤ 1
        1≤1 = ≤-refl
    in
    subst (λ x → 1 ≤ x) (sym (Sn∸n≡1 (Data.List.lookup (pure-multiary S) c))) 1≤1
nonzeroArgsLemma {S} {n} (argless-ℕ-multiary c x) a =
    let 1≤1 : 1 ≤ 1
        1≤1 = ≤-refl
    in
    subst (λ x → 1 ≤ x) (sym (Sn∸n≡1 (Data.List.lookup (ℕ-multiary S) c))) 1≤1
nonzeroArgsLemma {S} {n} (giveArg t' a') a =
    let IH : 1 ≤ getArity (giveArg t' a') ∸ (ℕ.suc n)
        IH = nonzeroArgsLemma t' a'
    in
    ≤-trans IH (m∸Sn≤m∸n n (getArity (giveArg t' a'))) 

getArgs
    : {S : TerseSignature}
    → {n : ℕ}
    → (t : OpenTerms S n)
    → Vec (ClosedTerms S) (getArity t ∸ n)
getArgs (mk-pure-nullary x) = []
getArgs (mk-ℕ-nullary x x₁) = []
getArgs {S} (argless-pure-multiary c) = 
    subst (λ m → Vec (ClosedTerms S) m) 
          (sym (n∸n≡0 (ℕ.suc (Data.List.lookup (pure-multiary S) c))))  
          []
getArgs {S} (argless-ℕ-multiary c x) =
    subst (λ m → Vec (ClosedTerms S) m) 
          (sym (n∸n≡0 (ℕ.suc (Data.List.lookup (ℕ-multiary S) c))))  
          []
getArgs {S} {n} (giveArg t a) = 
    --let NZ : 
    let H : ℕ.suc (getArity t ∸ ℕ.suc n) ≡ getArity (giveArg t a) ∸ n
        H = 
            begin 
                ℕ.suc (getArity t ∸ ℕ.suc n)
            ≡⟨ cong ℕ.suc (sym (pred[m∸n]≡m∸[1+n] (getArity t) n)) ⟩
                ℕ.suc (Data.Nat.pred (getArity t ∸ n))
            ≡⟨ suc-pred (getArity t ∸ n) ⦃ >-nonZero (nonzeroArgsLemma t a) ⦄ ⟩
                getArity t ∸ n
            ≡⟨⟩
                getArity (giveArg t a) ∸ n
            ∎
    in
    subst (λ m → Vec (ClosedTerms S) m) H (getArgs t Data.Vec.∷ʳ a)

ℕ-argType : ConstrKind → Set
ℕ-argType c-pure-nullary    = ⊤
ℕ-argType c-ℕ-nullary       = ℕ
ℕ-argType c-pure-multiary   = ⊤
ℕ-argType c-ℕ-multiary      = ℕ

-- Get external ℕ-argument, if any.
get-ℕ-arg
    : {S : TerseSignature}
    → {n : ℕ}
    → (t : OpenTerms S n)
    → ℕ-argType (getConstrKind t)
get-ℕ-arg (mk-pure-nullary _) = tt
get-ℕ-arg (mk-ℕ-nullary _ n) = n
get-ℕ-arg (argless-pure-multiary _) = tt
get-ℕ-arg (argless-ℕ-multiary _ n ) = n
get-ℕ-arg (giveArg t _) = get-ℕ-arg t
--------------------------------------------------------------------------------
-- Decomposing a closed term into a rounded term
--------------------------------------------------------------------------------

record SplitArgsOutp 
    {S : TerseSignature}
    (arity-1 : ℕ) 
    (args : Vec (ClosedTerms S) (ℕ.suc arity-1))
    (decompose : ClosedTerms S → Σ[ i ∈ ℕ ](Round S i))
    : Set
    where
    constructor splitOutp
    field
        m : Fin (ℕ.suc arity-1)
        -- The next two are a bit hard to read because
        -- n ≔ max 0 (map (proj₁ ∘ decompose) args) cannot be abbreviated here.
        α : Vec (Round S (max 0 (map (proj₁ ∘ decompose) (toList args) ))) 
                (ℕ.suc (toℕ m))
        β : Vec (Σ[ ℓ ∈ ℕ ] (
                    (ℓ < (max 0 (map (proj₁ ∘ decompose) (toList args) ))) 
                    × 
                    Round S ℓ)
                ) 
                ((ℕ.suc arity-1) ∸ (ℕ.suc (toℕ m)))
        merging : VMerging α β
        todo : ⊤ 
        -- #TODO later extend this record with other data
        -- needed to prove inversity of decomposeTerm.
        -- Problably maxes, others, merging of them,
        -- and proof that that merging compiles to the original args.
        -- Or a proof that α ≡ map decompose maxes
        -- from which one can infer map recompose α ≡ maxes,
        -- or so.

-- Subroutine of `decomposeTerm`.
-- Split the vector of arguments of a constructor into
-- the arguments attaining the maximum round
-- and the arguments 
splitArgs 
    : {S : TerseSignature}
    → (arity-1 : ℕ)
    → (args : Vec (ClosedTerms S) (ℕ.suc arity-1))
    → (decompose : ClosedTerms S → Σ[ i ∈ ℕ ](Round S i))
    → SplitArgsOutp arity-1 args decompose
splitArgs {S} arity-1 args decompose = 
    let arity : ℕ
        arity = ℕ.suc arity-1
    in
    let L : List (ClosedTerms S)
        L = toList args
    in
    let getRound : ClosedTerms S → ℕ
        getRound = proj₁ ∘ decompose
    in
    let unmergeMaxOutp : UnmergeMaxOutp L getRound
        unmergeMaxOutp = unmergeMax L getRound
    in
    let rawMerge = UnmergeMaxOutp.m unmergeMaxOutp
    in
    let H-rawMerge : compileMerging rawMerge ≡ L
        H-rawMerge = UnmergeMaxOutp.H-m unmergeMaxOutp
    in
    let maxRound : ℕ
        maxRound = max 0 (map getRound L)
    in
    let maxes : List ( Σ[ t ∈ (ClosedTerms S) ] (
            getRound t ≡ maxRound
            ×
            t ∈ L))
        maxes = UnmergeMaxOutp.maxes unmergeMaxOutp
    in
    let others = UnmergeMaxOutp.others unmergeMaxOutp
    in
    let lenL≡arity : length L ≡ arity
        lenL≡arity = length-toList args
    in
    let lenGetRoundL≡arity : length (map getRound L) ≡ arity
        lenGetRoundL≡arity = 
                subst (λ v → v ≡ arity) (sym (length-map getRound L)) lenL≡arity
    in
    let 0<lenMaxes : 0 < Data.List.length maxes
        0<lenMaxes = 
            let M = max 0 (map getRound L)
            in
            let M∈L : M ∈ (map getRound L)
                M∈L = 
                    let 0<arity : 0 < arity
                        0<arity = z<s
                    in
                    nonemptyThenHasMax (subst (λ v → 0 < v) 
                                              (sym lenGetRoundL≡arity) 
                                              0<arity)
            in
            let M∈compile : M ∈ map getRound (compileMerging rawMerge)
                M∈compile = subst (λ v → M ∈ map getRound v) (sym H-rawMerge) M∈L
            in
            let M∈maxes⊎M∈others : M ∈ (map (getRound ∘ proj₁) maxes) 
                                   ⊎ 
                                   M ∈ (map (getRound ∘ proj₁) others)
                M∈maxes⊎M∈others = 
                    let almost = compileMembershipMapCongr rawMerge getRound 
                                                           M M∈compile 
                    -- This gives 
                    -- M ∈ map getRound (map proj₁ maxes) ⊎ ...
                    -- but we need
                    -- M ∈ map (getRound ∘ proj₁) maxes ⊎ ...
                    in
                    subst (λ x → M ∈ map (getRound ∘ proj₁) maxes ⊎ M ∈ x) 
                          (sym (map-∘ {g = getRound} {f = proj₁} others)) 
                          (subst (λ x → M ∈ x ⊎ M ∈ map getRound 
                                 (map (λ r → proj₁ r) others)) 
                                 (sym (map-∘ {g = getRound} {f = proj₁} maxes)) 
                                 almost
                          )
            in
                -- Elements of 'others' come with proofs that their first
                -- components' getRound images are
                -- are smaller than the max. 
                -- So obviously the pre-image of the max 
                -- itself cannot be in others! 
            let M∉others : M ∉ (map (getRound ∘ proj₁) others)
                M∉others M∈others = 
                        let z (t , getRoundT<M , _) = <⇒≢ getRoundT<M
                        in
                        not∈lemma others getRound M z M∈others
            in
            let M∈maxes : M ∈ (map (getRound ∘ proj₁) maxes)
                M∈maxes = elimCaseRight M∈maxes⊎M∈others M∉others
            in
            -- #TODO: simplification?:
            -- in the above I went through quite some fuss to rewrite
            -- map getRound (map proj₁ ...) into map (getRound ∘ proj₁),
            -- but now I am undoing it again. Was this earlier rewrite not just
            -- a confusing detour?
            subst (λ x₁ → 0 < x₁) (length-map (getRound ∘ proj₁) maxes) (∈-length M∈maxes)
    in
    let lenMaxes≤lenMerge : 
            length maxes ≤ length (compileMerging rawMerge)
        lenMaxes≤lenMerge = subst (λ v → v ≤ length (compileMerging rawMerge))
                                  (length-map proj₁ maxes)
                                  (mergelenLemma rawMerge)
    in
    let lenMaxes≤lenL : length maxes ≤ arity
        lenMaxes≤lenL = 
            subst 
            (λ v → length maxes ≤ v) 
            (trans (cong length H-rawMerge) lenL≡arity)
            lenMaxes≤lenMerge
    in
    let m : Fin arity
        m = proj₁ (getPredec lenMaxes≤lenL 0<lenMaxes)
    in
    ----------------------------------------------------------------------------
    -- Mapping maxes to α
    -- Essentially just applying `decompose` to every element,
    -- but we need some some boilerplate to show:
    --  (1) the round-indices are all maxRound,
    --  and
    --  (2) that the length of α is correct.
    ----------------------------------------------------------------------------
    let maxesToα : Σ[ t  ∈ ClosedTerms S ]( 
            ((proj₁ ∘ decompose) t ≡ maxRound) × (t ∈ L))
            → Round S maxRound
        maxesToα (t , pt , t∈L) = subst (Round S) pt (proj₂ (decompose t))
    in
    let lenMaxes≡Sm : length (map (maxesToα) maxes) ≡ ℕ.suc (toℕ m)
        lenMaxes≡Sm =  
                begin 
                    length (map (maxesToα) maxes)
                ≡⟨ length-map (maxesToα) maxes ⟩
                    length maxes
                ≡⟨ sym (proj₂ (getPredec lenMaxes≤lenL 0<lenMaxes)) ⟩
                    ℕ.suc (toℕ m) 
                ∎
    in                    
    let α' : Vec (Round S maxRound) (length (map maxesToα maxes))
        α' = fromList ( map maxesToα maxes ) 
    in
    let α : Vec (Round S maxRound) (ℕ.suc (toℕ m))
        α = subst (λ x → Vec (Round S maxRound) x) 
            lenMaxes≡Sm α'
    in
    ----------------------------------------------------------------------------
    -- Mapping others to β
    --
    -- Similar as mapping maxes to α,
    -- only the length is a bit more involved.
    ----------------------------------------------------------------------------
    let othersToβ : Σ[ t  ∈ ClosedTerms S ]( 
            ((proj₁ ∘ decompose) t < maxRound) × (t ∈ L))
            → Σ[ ℓ ∈ ℕ ] ((ℓ < maxRound) × (Round S ℓ))
        othersToβ (t , pt , t∈L) = 
            (proj₁ (decompose t) , pt , proj₂ (decompose t))
    in
    let βType = Σ[ ℓ ∈ ℕ ]((ℓ < maxRound) × (Round S ℓ))
    in
    let β' : Vec βType (length (map othersToβ others))
        β' = fromList ( map othersToβ others)
    in
    let fixβ'len : length (map othersToβ others) ≡ (arity ∸ (ℕ.suc (toℕ m)))
        fixβ'len = ?
    in
    let β = subst (λ x → Vec βType x) fixβ'len β'
    in
    splitOutp m α β {! !} {! !}

-- Decomposing a closed term into a rounded term,
-- making the choices in constructing the term explicit.
-- Since closed terms take other terms as arguments,
-- which we need to decompose in other to compute their rounds
-- (to find the maximum round over all arguments,
-- from which we infer the round of the outer closed term itself).
-- we needed to define this via Well-Founded induction on subterms
-- («-rec).
decomposeTerm : {S : TerseSignature} → ClosedTerms S → RoundedTerms S
decomposeTermRec 
    : {S : TerseSignature}
    → (t : ClosedTerms S)
    → ({a : ClosedTerms S} → a « t → RoundedTerms S)
    → RoundedTerms S

decomposeTerm {S} = «-rec (λ t → RoundedTerms S) decomposeTermRec

decomposeTermRec {S} (mk-pure-nullary c) decomposeSubterm = 
    (0 , pure-atomic c)
decomposeTermRec {S} (mk-ℕ-nullary c n) decomposeSubterm =
    (ℕ.suc n , ℕ-atomic n c)
decomposeTermRec {S} (giveArg t a) decomposeSubterm = 
    let constrKind : ConstrKind
        constrKind = getConstrKind t in 
    let constrIdx : kindToIndexSet S constrKind
        constrIdx = getConstrIdx t
    in
    let arity : ℕ
        arity = getArity t
    in
    let args : Vec (ClosedTerms S) (getArity t)
        args = getArgs (giveArg t a)
    in
    let ℕ-arg : ℕ-argType constrKind
        ℕ-arg = get-ℕ-arg t
    in
    --------------------------------------------------------------------------------
    -- Above this line is new stuff. Below this line is old stuff.
    -- Let's try to fit the new stuff into the old stuff.
    --------------------------------------------------------------------------------
    
    -- #TODO: assembly will require a case distinction on the constrKind.
    ?

--decomposeTerm {S} (mk-pure-nullary x) = (0 , c-pure-nullary , x , refl {x = 0})
--decomposeTerm {S} (mk-ℕ-nullary x n) = 
--    let round = ℕ.suc n
--    in
--    (round , c-ℕ-nullary , x , n , n<1+n n)
--decomposeTerm {S} (mk-pure-multiary x args) = 
--    let arity : ℕ
--        arity = ℕ.suc (Data.List.lookup (pure-multiary S) x)
--    in
--    let getRound = λ t → proj₁ (decomposeTerm t)
--    in
--    let argRounds : Vec ℕ (Data.Vec.length args)
--        argRounds = Data.Vec.map getRound args
--    in
--    -- 0 is default value when list is empty (I tested),
--    -- but we know it is not empty anyway.
--    let round∸1 : ℕ
--        round∸1 = max 0 (toList argRounds)
--    in
--    let round = ℕ.suc round∸1
--    in
--    let hᵢ : 0 < round
--        hᵢ = Data.Nat.z<s {round∸1}
--    in
--    let P : TerseFreeTerms S → Set
--        P = λ a → getRound a ≡ round∸1
--    in
--    -- #TODO: Agda will probably compain here about termination.
--    -- An idea to fix it:
--    -- Define P on terms t that come with (t << t') where
--    --  << is the subterm relation and t' is our input.
--    --  Prove << is well-founded and use well-founded recursion.
--    let Pdec : Relation.Unary.Decidable P
--        Pdec t = getRound t Data.Nat.≟ round∸1
--    in
--    let L : List (TerseFreeTerms S)
--        L = toList args
--    in
--    let unmergeMaxOutp : UnmergeMaxOutp L getRound
--        unmergeMaxOutp = unmergeMax L getRound
--    in
--    let rawMerge = UnmergeMaxOutp.m unmergeMaxOutp
--    in
--    let H-rawMerge : compileMerging rawMerge ≡ L
--        H-rawMerge = UnmergeMaxOutp.H-m unmergeMaxOutp
--    in
--    let maxes : List ( Σ[ t ∈ (TerseFreeTerms S) ] (
--            proj₁ (decomposeTerm t) ≡ max 0 (map getRound L)
--            ×
--            t ∈ L))
--        maxes = UnmergeMaxOutp.maxes unmergeMaxOutp
--    in
--    let others = UnmergeMaxOutp.others unmergeMaxOutp
--    in
--    let lenL≡arity : length L ≡ arity
--        lenL≡arity = length-toList args
--    in
--    let lenGetRoundL≡arity : length (map getRound L) ≡ arity
--        lenGetRoundL≡arity = 
--                subst (λ v → v ≡ arity) (sym (length-map getRound L)) lenL≡arity
--    in
--    let 0<lenMaxes : 0 < Data.List.length maxes
--        0<lenMaxes = 
--            let M = max 0 (map getRound L)
--            in
--            let M∈L : M ∈ (map getRound L)
--                M∈L = 
--                    let 0<arity : 0 < arity
--                        0<arity = z<s
--                    in
--                    nonemptyThenHasMax (subst (λ v → 0 < v) 
--                                              (sym lenGetRoundL≡arity) 
--                                              0<arity)
--            in
--            let M∈compile : M ∈ map getRound (compileMerging rawMerge)
--                M∈compile = subst (λ v → M ∈ map getRound v) (sym H-rawMerge) M∈L
--            in
--            let M∈maxes⊎M∈others : M ∈ (map (getRound ∘ proj₁) maxes) 
--                                   ⊎ 
--                                   M ∈ (map (getRound ∘ proj₁) others)
--                M∈maxes⊎M∈others = 
--                    let almost = compileMembershipMapCongr rawMerge getRound 
--                                                           M M∈compile 
--                    -- This gives 
--                    -- M ∈ map getRound (map proj₁ maxes) ⊎ ...
--                    -- but we need
--                    -- M ∈ map (getRound ∘ proj₁) maxes ⊎ ...
--                    in
--                    subst (λ x → M ∈ map (getRound ∘ proj₁) maxes ⊎ M ∈ x) 
--                          (sym (map-∘ {g = getRound} {f = proj₁} others)) 
--                          (subst (λ x → M ∈ x ⊎ M ∈ map getRound 
--                                 (map (λ r → proj₁ r) others)) 
--                                 (sym (map-∘ {g = getRound} {f = proj₁} maxes)) 
--                                 almost
--                          )
--            in
--                -- Elements of 'others' come with proofs that their first
--                -- components' getRound images are
--                -- are smaller than the max. 
--                -- So obviously the pre-image of the max 
--                -- itself cannot be in others! 
--            let M∉others : M ∉ (map (getRound ∘ proj₁) others)
--                M∉others M∈others = 
--                        let z (t , getRoundT<M , _) = <⇒≢ getRoundT<M
--                        in
--                        not∈lemma others getRound M z M∈others
--            in
--            let M∈maxes : M ∈ (map (getRound ∘ proj₁) maxes)
--                M∈maxes = elimCaseRight M∈maxes⊎M∈others M∉others
--            in
--            -- #TODO: simplification?:
--            -- in the above I went through quite some fuss to rewrite
--            -- map getRound (map proj₁ ...) into map (getRound ∘ proj₁),
--            -- but now I am undoing it again. Was this earlier rewrite not just
--            -- a confusing detour?
--            subst (λ x₁ → 0 < x₁) (length-map (getRound ∘ proj₁) maxes) (∈-length M∈maxes)
--    in
--    let lenMaxes≤lenMerge : 
--            length maxes ≤ length (compileMerging rawMerge)
--        lenMaxes≤lenMerge = subst (λ v → v ≤ length (compileMerging rawMerge))
--                                  (length-map proj₁ maxes)
--                                  (mergelenLemma rawMerge)
--    in
--    let lenMaxes≤lenL : length maxes ≤ arity
--        lenMaxes≤lenL = 
--            subst 
--            (λ v → length maxes ≤ v) 
--            (trans (cong length H-rawMerge) lenL≡arity)
--            lenMaxes≤lenMerge
--    in
--    let m : Fin arity
--        m = proj₁ (getPredec lenMaxes≤lenL 0<lenMaxes)
--    in
--    let lenMaxes≡Sm : length (map (decomposeTerm ∘ proj₁) maxes) ≡ ℕ.suc (toℕ m)
--        lenMaxes≡Sm =  
--                begin 
--                    length (map (decomposeTerm ∘ proj₁) maxes)
--                ≡⟨ length-map (decomposeTerm ∘ proj₁) maxes ⟩
--                    length maxes
--                ≡⟨ sym (proj₂ (getPredec lenMaxes≤lenL 0<lenMaxes)) ⟩
--                    ℕ.suc (toℕ m) 
--                ∎
--    in                    
--    let α = let α' = fromList (map (decomposeTerm ∘ proj₁) maxes)
--            in
--            -- #TODO: I can prove that the length is right, but I don't think
--            -- this will give the right elements yet...
--            let α'' = subst (λ x → Vec _ x) lenMaxes≡Sm α'
--            in
--            α''
--    in
--    let β = {! UnmergeMaxOutp.others unmergeMaxOutp !}
--    in
--    let merging = {! UnmergeMaxOutp.m unmergeMaxOutp !}
--    in
--    (round , c-pure-multiary , hᵢ , x , m , α , β , merging)
--decomposeTerm {S} (mk-ℕ-multiary c x x₁) = {! !}

--FreeTerms≃TeleTerms 
--    : (S : TerseSignature)
--    → TerseFreeTerms S ≃ TeleTerms S
--FreeTerms≃TeleTerms S .LR = {! !}
--FreeTerms≃TeleTerms S .RL = {! !}
--FreeTerms≃TeleTerms S .homotLRL = {! !}
--FreeTerms≃TeleTerms S .homotRLR = {! !}
