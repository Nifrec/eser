-- Module      : Eser.Definitions
-- Description : Definitions of relation representations, mappings between, etc.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
open import Level
open import Data.Bool hiding (_≤_ ; _<_)
open import Data.Bool.Properties using (¬-not ; not-¬)
open import Data.Nat
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_≤_)
open import Data.Vec hiding (restrict)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; ≤-<-trans ; n≤0⇒n≡0 
                                       ; n≤1+n ; m≤n⇒m<n∨m≡n)
open import Data.Fin.Properties using (toℕ<n)
open import Relation.Nullary -- Needed for with-abstractions on decidable ≡.

open import Eser.Logic using (elimCaseLeft)
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
--open import Data.List.Membership.Propositional using (_∈_ ; _∉_ )
--open import Data.List.Membership.Propositional.Properties using (∈-lookup)
--open import Data.List.Relation.Unary.Any using (Any)

module Eser.Definitions where

--------------------------------------------------------------------------------
-- Relations on ℕ
--------------------------------------------------------------------------------

-- Relations as functions. 
-- This Bool-valued representation is always proof-irrelevant
-- and decidable, and more convenient when proving homotopy between relations.
-- The Agda stdlib lets a relation output a Set, which is annoying when
-- trying to show a homotopy that does not care about proof implementations.
-- See below `_ ⊢ _ ~ _` for a conversion to the stdlib's representation.
DecRel : Set
DecRel = ℕ → ℕ → Bool

_⊢_~_ : DecRel → Rel ℕ 0ℓ
R ⊢ n ~ m = R n m ≡ true

-- Decidable equivalence relations.
DecEquiv : Set
DecEquiv = Σ[ R ∈ DecRel ]( IsEquivalence (R ⊢_~_) )

-- Type of properties relation may have
-- (Proposition on a relation, but not necessarily proof irrelevant
-- since that's simply a bit inconvenient to implement in Agda --
-- the `Prop` sort is not vanilla and experimental,
-- and adding proofs of proof-irrelevance via Σ is overcomplicating things).
RelProp : Set₁
RelProp = DecRel → Set

-- Equivalence relations that also have a given property.
DecEquivWithProp : RelProp → Set
DecEquivWithProp P = Σ[ R ∈ DecRel ] (IsEquivalence (R ⊢_~_) × P R)

--------------------------------------------------------------------------------
-- Normal-form functions and globally-defined properties of them.
--------------------------------------------------------------------------------
-- Property of a function.
FunProp : Set₁
FunProp = (ℕ → ℕ) → Set

-- Coherence constraint on normal form functions: 
-- the normal form of n is always smaller or equal to n,
-- i.e., has been explored earlier.
-- This is necessary when building equivalence relations by inductively
-- assigning each n ∈ ℕ to its normal form.
NLeq : FunProp
NLeq f = (n : ℕ) → f n ≤ n

-- Coherence constraint on normal form functions: 
-- the normal form of a normal form is itself.
NFix : FunProp
NFix f = (n : ℕ) → f (f n) ≡ f n

-- Functions ℕ → ℕ that encode an equivalence relation,
-- i.e., functions that satisfy the coherence conditions that allow
-- them to be used as a normal-form function.
NFFun : Set
NFFun = Σ[ f ∈ (ℕ → ℕ) ]( NLeq f × NFix f)

-- #TODO: remove?
NFFunWithProp : FunProp → Set
NFFunWithProp P = Σ[ f ∈ (ℕ → ℕ) ] ( NLeq f × NFix f × P f)


--------------------------------------------------------------------------------
-- Normal-form functions and locally-defined properties of them.
--------------------------------------------------------------------------------
-- Get the first n outputs of a function ℕ → ℕ as a vector.
-- Equivalently, restrict the domain to {0, 1, ..., n-1}.
restrict : (n : ℕ) → (ℕ → ℕ) → Vec ℕ n
restrict 0 f = []
restrict (suc n) f = (f n) ∷ (restrict n f)

-- Decidable locally defined property.
-- For each n, judge whether the restriction of a function ℕ → ℕ
-- to {0, ..., n} satisfies the property.
LocProp : Set₁
LocProp = (n : ℕ) → Vec ℕ n → Set

-- Proposition that all restrictions of a function satisfy a
-- locally defined property.
AllRestr : (ℕ → ℕ) → LocProp → Set
AllRestr f P = (n : ℕ) → P n (restrict n f)

-- #TODO: remove?
-- Local version of NLeq: f m ≤ m for all m,
-- where f m is encoded as the value of a vector at index 0.
NFLeqLoc : LocProp
NFLeqLoc n v = (m : Fin n) → lookup v m ≤ toℕ m

-- #TODO: remove?
-- Local version of NFix : f (f m) ≡ f m for all m.
-- Technical issue: when not assuming f m ≤ m, then f m > n is possible,
-- which means that we cannot lookup `f m` as vector index.
-- If AllRestr f NFLeqLoc then this can, of course, never happen.
-- But I wanted to define NFFixLoc independently from NFLeqLoc,
-- so it has the conditional form:
--      "if f m is an index of the vector then f (f m) ≡ f m".
NFFixLoc : LocProp
NFFixLoc n v = (m : Fin n) 
             → (q : (lookup v m ≤ toℕ m)) 
             → lookup v (fromℕ< (≤-<-trans q (toℕ<n m))) ≡ lookup v m

NFFunWithLocProp : LocProp → Set
NFFunWithLocProp P = Σ[ f ∈ (ℕ → ℕ) ] (
      AllRestr f NFLeqLoc 
    × AllRestr f NFFixLoc 
    × AllRestr f P)

--------------------------------------------------------------------------------
-- Correspondences 
--------------------------------------------------------------------------------

FunToRel : NFFun → DecEquiv
FunToRel (f , nleq , nfix) = 
    (R , isequiv)
    where
        R : ℕ → ℕ → Bool
        R n m = f n ≡ᵇ f m
        isequiv : IsEquivalence (R ⊢_~_)
        isequiv = ?

--RelToFun : DecEquiv → NFFun
--RelToFun (R , isequiv) 0 = 0
--RelToFun (R , isequiv) (suc n) = {!  !}

-- "n is the minimum number that satisfies proposition P".
IsMin : (n : ℕ) → (P : ℕ → Bool) → Set
IsMin n P = (x : ℕ) → (x ≤ n) → (P x ≡ true) → x ≡ n

-- Find the smallest number m ≤ n such that P m ≡ true,
-- xor return a proof that no such number exists.
-- (Note: n itself may also be returned!)
FindMin : (n : ℕ) → (P : ℕ → Bool) → 
    ((Σ[ ℓ ∈ ℕ ](ℓ ≤ n × IsMin ℓ P))
    ⊎
    ((ℓ : ℕ) → (ℓ ≤ n) → (P ℓ ≡ false))
    )
FindMin 0 P with ((P 0) Data.Bool.≟ true)
... | yes P0 = 
    let f : IsMin 0 P
        f x x≤0 _ = n≤0⇒n≡0 x≤0
    in
    inj₁ (0 , ≤-refl , f)
... | no ¬P0 = 
    inj₂ (λ x x≤0 → subst (λ ℓ → P ℓ ≡ false) (sym (n≤0⇒n≡0 x≤0)) (¬-not ¬P0))
FindMin (suc n) P with (FindMin n P)
-- Case 1 : there exist a m ≤ n that satisfies P. 
-- Then return that m, regardless of whether P (suc n) is true.
... | (inj₁ (m , m≤n , isminPm )) = 
        let m≤Sn : m ≤ ℕ.suc n
            m≤Sn = ≤-trans m≤n (n≤1+n n)
        in inj₁ (m , m≤Sn , isminPm)
-- Case 2 : there is no m ≤ n that satisfies P.
-- However, suc n still might satisfy P:
-- if it does, return suc n with a proof that it is the minimum,
-- if not, then we can prove no m ≤ suc n satisfies P.
... | (inj₂ f ) with (P (ℕ.suc n)) Data.Bool.≟ true
...     | yes PSn = 
    let isminPSn : IsMin (ℕ.suc n) P
        isminPSn x x≤Sn Px = 
            let H : x Data.Nat.< (ℕ.suc n) ⊎ (x ≡ ℕ.suc n)
                H = m≤n⇒m<n∨m≡n x≤Sn
            in
            let ¬[x<Sn] : ¬ (x Data.Nat.< ℕ.suc n)
                -- If x < Sn, then x ≤ n, 
                -- but we are assuming (P m ≡ false) for all m ≤ n!
                -- So we can eliminate this option, then only the desired
                -- option x ≡ suc n remains.
                ¬[x<Sn] Sx≤Sn = 
                    let x≤n : x ≤ n
                        x≤n = s≤s⁻¹ Sx≤Sn
                    in 
                    not-¬ (f x x≤n) Px
            in
            elimCaseLeft H ¬[x<Sn]
    in inj₁ (ℕ.suc n , ≤-refl , isminPSn)
...     | no ¬PSn = 
    let f : (ℓ : ℕ) → ℓ ≤ ℕ.suc n → P ℓ ≡ false
        f ℓ ℓ≤Sn = 
            let ℓ<Sn⊎l≡Sn = m≤n⇒m<n∨m≡n ℓ≤Sn
            in
            let H : ℓ Data.Nat.< ℕ.suc n → P ℓ ≡ false
                H Sℓ≤Sn = 
                    let ℓ≤n = s≤s⁻¹ Sℓ≤Sn
                    in
                    f ℓ ℓ≤n
            in
            let K : ℓ ≡ ℕ.suc n → P ℓ ≡ false
                K ℓ≡Sn = subst (λ m → P m ≡ false) (sym ℓ≡Sn) (¬-not ¬PSn)
            in
            ([_,_] H K) ℓ<Sn⊎l≡Sn 
    in
    inj₂ f
