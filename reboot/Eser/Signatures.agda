-- Module      : Eser.Signatures
-- Description : Tools for enumerating term algebras over signatures
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
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
--open import Relation.Binary.Structures
open import Data.Fin hiding (_≤_ ; _≤?_ ; _<_ ; _>_ ; _+_)
open import Data.List
open import Data.List.Properties using (map-∘ ; length-map)
open import Data.Vec hiding (restrict ; length ; map)
open import Induction.WellFounded
open import Data.Nat.Induction using (<-Rec)
open import Data.Nat.Properties using (≤-refl ; n<1+n ; <-trans ; m<n⇒0<n ; <⇒≢
    ; ≤-trans ) -- ; ≤-<-trans ; n≤0⇒n≡0 
open import Data.Vec.Properties using (length-toList) 
--                                       ; n≤1+n ; m≤n⇒m<n∨m≡n ; _≤?_ ; ≰⇒≥)
open import Data.Fin.Properties using (toℕ-fromℕ<)
--open import Relation.Nullary -- Needed for with-abstractions on decidable ≡.
open import Function hiding (_↔_)

--open import Eser.Logic using (elimCaseLeft ; elimCaseRight)
--open import Relation.Nullary
--open ≡-Reasoning
--open import Data.Nat.Properties
--open import Data.Fin
--open import Data.Fin.Properties
--open import Data.Fin.Induction
--open import Data.Empty
--open import Data.List
--open import Data.List.Relation.Unary.AllPairs using (AllPairs)
--open import Data.List.Relation.Unary.All using (All)
--open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix)
open import Data.List.Membership.Propositional using (_∈_ ; _∉_ )
open import Data.List.Membership.Propositional.Properties using (∈-length)
--open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Extrema.Nat

open import Eser.Logic using (elimCaseRight)
open import Eser.Definitions using (_≈_ ; indices ; _≃_ ; HomotEquivalence)
open HomotEquivalence
open import Eser.Mergings using (Merging ; unmergeMax ; UnmergeMaxOutp 
    ; mergelenLemma ; VMerging ; compileMerging ; compileMembership
    ; compileMembershipMapCongr)
open import Eser.ListMaxima using (nonemptyThenHasMax)

module Eser.Signatures where

--------------------------------------------------------------------------------
-- Signature representations
--------------------------------------------------------------------------------
-- Very terse representation of signatures.
-- Constructors either have arity 0 or suc a
-- (for inductive arguments of their own type;
-- for each multiary constructor with arity `suc a`,
-- the value `a` should be stored in the List ℕ).
-- Constructors either take one external argument from ℕ,
-- or no external arguments.
record TerseSignature : Set where
   field 
        pure-nullary : ℕ
        ℕ-nullary    : ℕ
        pure-multiary : List ℕ
        ℕ-multiary : List ℕ
open TerseSignature

data ConstrKind : Set where
    c-pure-nullary   : ConstrKind
    c-ℕ-nullary      : ConstrKind
    c-pure-multiary  : ConstrKind
    c-ℕ-multiary     : ConstrKind

-- Lookup the arity of a non-nullary constructor in a signature.
getArity 
    : (S : TerseSignature) 
    → (indices (pure-multiary S)) ⊎ (indices (ℕ-multiary S))
    → ℕ
getArity S (inj₁ idx) = ℕ.suc (Data.List.lookup (pure-multiary S) idx )
getArity S (inj₂ idx) = ℕ.suc (Data.List.lookup (ℕ-multiary S)    idx )

-- Term algebra over a TerseSignature.
data TerseFreeTerms (S : TerseSignature) : Set where
    mk-pure-nullary : Fin (pure-nullary S) → TerseFreeTerms S
    mk-ℕ-nullary : Fin (ℕ-nullary S) → ℕ → TerseFreeTerms S
    mk-pure-multiary 
        : (c : indices (pure-multiary S)) 
        → (Vec (TerseFreeTerms S) (ℕ.suc (Data.List.lookup (pure-multiary S) c)))
        → TerseFreeTerms S 
    mk-ℕ-multiary 
        : (c : indices (pure-multiary S)) 
        → (Vec (TerseFreeTerms S) (ℕ.suc (Data.List.lookup (pure-multiary S) c)))
        → ℕ
        → TerseFreeTerms S 

--------------------------------------------------------------------------------
-- Representation of term algebras that reveals much more about the choices
-- one needs to make when constructing a term.
--------------------------------------------------------------------------------

-- `<-Rec` in Data.Nat.Induction should do the same, but it confused me how to
-- apply it.
<-rec : {ℓ : Level} → (P : ℕ → Set ℓ)
    → ((n : ℕ) → ((m : ℕ) → (m < n) → P m) → P n)
    → (n : ℕ) → P n
<-rec {ℓ} P rec n = lemma n (Data.Nat.Induction.<-wellFounded n)
    where
        lemma : (n : ℕ) → Acc _<_ n → P n
        lemma n (acc Accn) = rec n (λ m → λ m<n → lemma m (Accn m<n) )
        
0<n⇒pred[n]<n
    : {n : ℕ}
    → 0 < n
    → Data.Nat.pred n < n
0<n⇒pred[n]<n {0} ()
0<n⇒pred[n]<n {suc n} 0<n = s≤s (≤-refl {n})

ssn<m⇒n<m
    : {n m : ℕ}
    → ℕ.suc (ℕ.suc n) < m
    → n < m
ssn<m⇒n<m {n} {ℕ.suc 0} (s≤s ()) 
ssn<m⇒n<m {n} {ℕ.suc (ℕ.suc m)} SSn<SSm = 
    let n<m : n < m
        n<m = s<s⁻¹ (s<s⁻¹ SSn<SSm)
    in
    let m<SSm : m < ℕ.suc (ℕ.suc m)
        m<SSm = <-trans (n<1+n m) (n<1+n (ℕ.suc m))
    in
    <-trans n<m m<SSm


TeleTerms : (S : TerseSignature) → Set
TeleTerms S = Σ[ i ∈ ℕ ] ( round S i )
    where
        kindCaseDistinction : (S : TerseSignature) 
            → (n : ℕ) 
            → ConstrKind 
            → ((m : ℕ) → (m < n) → Set)
            → Set
        round : TerseSignature → ℕ → Set
        round S = <-rec (λ i → Set) 
            (λ i → λ rec → 
            Σ[ ck ∈ ConstrKind ] kindCaseDistinction S i ck rec)

        kindCaseDistinction S i c-pure-nullary rec
            = Σ[ c ∈ Fin (pure-nullary S) ] i ≡ 0
        kindCaseDistinction S i c-ℕ-nullary rec
            = Σ[ c ∈ Fin (ℕ-nullary S) ] Σ[ n ∈ ℕ ] (n < i)
            --^ n < i : value n may only be used in round (suc n).
            -- Note: this forces i > 0, 
            -- so we do not need to store this explicitly.
        kindCaseDistinction S i c-pure-multiary rec 
            = 
            Σ[ hᵢ ∈ i > 0 ] 
            --^ To avoid an α in round 0 constisting of
            -- round 0 elements.
            Σ[ c ∈ indices (pure-multiary S) ]
            Σ[ m ∈ Fin (getArity S (inj₁ c)) ]
            -- α is a vector whose length is ℕ.suc m
            -- which is in the range [1, ..., arity S (inj₁ c)],
            -- whose elements are terms from round (i ∸ 1). 
            -- We use Well-Founded recursion to define `round (i - 1)`.
            Σ[ α ∈ Vec 
                    (rec (Data.Nat.pred i) (0<n⇒pred[n]<n hᵢ) ) -- round (i - 1)
                    (ℕ.suc (toℕ m))
            ] 
            -- β is a vector of length m - |α| (so |α| + |β| ≡ m)
            -- with elements from `round 0 ⊎ round 1 ⊎ ... ⊎ round (i ∸ 2).
            -- Note that α and β do not share elements,
            -- and their union always contains at least one element
            -- from round (i ∸ 1). β can be empty.
            Σ[ β ∈ Vec 
                (Σ[ j ∈ ℕ ] Σ[ hⱼ ∈ ℕ.suc (ℕ.suc j) < i ] rec j (ssn<m⇒n<m hⱼ)) 
                (getArity S (inj₁ c) ∸ Data.Vec.length α) 
            ]
            VMerging α β
        -- Same as previous case, but now also an n < i,
        -- which in turn makes hᵢ redundent (it guarrantees i > 0
        -- otherwise no such n exists).
        kindCaseDistinction S i c-ℕ-multiary rec
            = 
            Σ[ n ∈ ℕ ] 
            Σ[ hₙ ∈ n < i ] 
            Σ[ c ∈ indices (ℕ-multiary S) ]
            Σ[ m ∈ Fin (getArity S (inj₂ c)) ]
            Σ[ α ∈ Vec 
                (rec (Data.Nat.pred i) (0<n⇒pred[n]<n (m<n⇒0<n {n} {i} hₙ)) ) 
                (ℕ.suc (toℕ m)) 
            ]
            Σ[ β ∈ Vec 
                (Σ[ j ∈ ℕ ] Σ[ hⱼ ∈ ℕ.suc (ℕ.suc j) < i ] rec j (ssn<m⇒n<m hⱼ))
                ((getArity S (inj₂ c)) ∸ Data.Vec.length α)
            ]
            VMerging α β

--------------------------------------------------------------------------------
-- Correspondence theorems:
--
-- 1. TerseFreeTerms and TeleTerms are in bijection, i.e., represent the same
--  term algebra (up to renaming elements).
-- 2. All nested Σs in TeleTerms are finite sets, only the outermost quantifies
--  over ℕ. That is, for all S and i, we have: round S i ≃ Fin k for some k.
-- 3. Corollary of 1. and 2.: TerseFreeTerms ≃ TeleTerms ≃ ℕ
--------------------------------------------------------------------------------
open import Data.List.Relation.Unary.Any using (here ; there)

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


decomposeTerm : {S : TerseSignature} → TerseFreeTerms S → TeleTerms S
decomposeTerm {S} (mk-pure-nullary x) = (0 , c-pure-nullary , x , refl {x = 0})
decomposeTerm {S} (mk-ℕ-nullary x n) = 
    let round = ℕ.suc n
    in
    (round , c-ℕ-nullary , x , n , n<1+n n)
decomposeTerm {S} (mk-pure-multiary x args) = 
    let arity : ℕ
        arity = ℕ.suc (Data.List.lookup (pure-multiary S) x)
    in
    let getRound = λ t → proj₁ (decomposeTerm t)
    in
    let argRounds : Vec ℕ (Data.Vec.length args)
        argRounds = Data.Vec.map getRound args
    in
    -- 0 is default value when list is empty (I tested),
    -- but we know it is not empty anyway.
    let round∸1 : ℕ
        round∸1 = max 0 (toList argRounds)
    in
    let round = ℕ.suc round∸1
    in
    let hᵢ : 0 < round
        hᵢ = Data.Nat.z<s {round∸1}
    in
    let P : TerseFreeTerms S → Set
        P = λ a → getRound a ≡ round∸1
    in
    -- #TODO: Agda will probably compain here about termination.
    -- An idea to fix it:
    -- Define P on terms t that come with (t << t') where
    --  << is the subterm relation and t' is our input.
    --  Prove << is well-founded and use well-founded recursion.
    let Pdec : Relation.Unary.Decidable P
        Pdec t = getRound t Data.Nat.≟ round∸1
    in
    let L : List (TerseFreeTerms S)
        L = toList args
    in
    let unmergeMaxOutp : UnmergeMaxOutp L getRound
        unmergeMaxOutp = unmergeMax L getRound
    in
    let rawMerge = UnmergeMaxOutp.m unmergeMaxOutp
    in
    let H-rawMerge : compileMerging rawMerge ≡ L
        H-rawMerge = UnmergeMaxOutp.H-m unmergeMaxOutp
    in
    let maxes : List ( Σ[ t ∈ (TerseFreeTerms S) ] (
            proj₁ (decomposeTerm t) ≡ max 0 (map getRound L)
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
    let α = {!  !}
    in
    let β = {! UnmergeMaxOutp.others unmergeMaxOutp !}
    in
    let merging = {! UnmergeMaxOutp.m unmergeMaxOutp !}
    in
    (round , c-pure-multiary , hᵢ , x , m , α , β , merging)
decomposeTerm {S} (mk-ℕ-multiary c x x₁) = {! !}

FreeTerms≃TeleTerms 
    : (S : TerseSignature)
    → TerseFreeTerms S ≃ TeleTerms S
FreeTerms≃TeleTerms S .LR = {! !}
FreeTerms≃TeleTerms S .RL = {! !}
FreeTerms≃TeleTerms S .homotLRL = {! !}
FreeTerms≃TeleTerms S .homotRLR = {! !}
