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
open import Data.Empty
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

open import Eser.Logic using (elimCaseLeft ; elimCaseRight)
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

_⊢_~_ : {A : Set} → (A → A → Bool) → Rel A 0ℓ
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
-- Maps between relations and functions.
-- 
-- The main definitions are:
-- * FunToRel : NFFun → DecEquiv
-- * RelToFun : DecEquiv → NFFun
-- But there are also a lot of auxiliary lemmas in this section
-- necessary to define them.
--
-- Some notes:
-- * FunToRel does not use the NF-properties of the input.
--      It could be retyped as (ℕ → ℕ) → DecEquiv.
-- * RelToFun does use symmetry and transitivity to prove the NF-properties of
--      the output. However, given only reflexivity one can still
--      use the current implementation 
--      (mapping n to the minimum m s.t. m ≤ n and R n m)
--      define ReflexiveRel → (ℕ → ℕ).
--------------------------------------------------------------------------------

numIsItself : (n : ℕ) → (n ≡ᵇ n) ≡ true
numIsItself zero = refl
numIsItself (ℕ.suc n) = numIsItself n

numEqualSym : (n m : ℕ) → (n ≡ᵇ m) ≡ true → (m ≡ᵇ n) ≡ true
numEqualSym ℕ.zero ℕ.zero n≡m = refl
numEqualSym (ℕ.suc n) (ℕ.suc m) Sn≡Sm = numEqualSym n m Sn≡Sm

numEqualTrans : 
    (n m ℓ : ℕ) 
    → (n ≡ᵇ m) ≡ true 
    → (m ≡ᵇ ℓ) ≡ true
    → (n ≡ᵇ ℓ) ≡ true
numEqualTrans ℕ.zero ℕ.zero ℕ.zero n≡m m≡ℓ = refl
numEqualTrans (ℕ.suc n) (ℕ.suc m) (ℕ.suc ℓ) Sn≡Sm Sm≡Sℓ = 
    numEqualTrans n m ℓ Sn≡Sm Sm≡Sℓ

FunToRel : NFFun → DecEquiv
FunToRel (f , nleq , nfix) = 
    (R , isequiv)
    where
        R : ℕ → ℕ → Bool
        R n m = f n ≡ᵇ f m
        R' : ℕ → ℕ → Set
        R' = R ⊢_~_
        isequiv : IsEquivalence R'
        isequiv = 
            let
                reflR : Reflexive R'
                reflR {n} = numIsItself (f n)
            in
            let symR : Symmetric R'
                symR {n} {m} R'nm = numEqualSym (f n) (f m) R'nm
            in
            let transR : Transitive R'
                transR {i} {j} {k} R'ij R'jk = 
                    numEqualTrans (f i) (f j) (f k) R'ij R'jk
            in
            record { refl = reflR ; sym = symR ; trans = transR }

-- Predicate: "There exists no number smaller than n that satisfies P"
-- (Note: this does NOT yet guarrantee ANY number satisfies P).
NoSmaller : (n : ℕ) → (P : ℕ → Bool) → Set
NoSmaller n P = (x : ℕ) → (x ≤ n) → (P x ≡ true) → x ≡ n

-- "n is the minimum number that satisfies proposition P".
IsMin : (n : ℕ) → (P : ℕ → Bool) → Set
IsMin n P = (P n ≡ true ) × NoSmaller n P

-- Find the smallest number m ≤ n such that P m ≡ true,
-- xor return a proof that no such number exists.
-- (Note: n itself may also be returned!)
findMin : (n : ℕ) → (P : ℕ → Bool) → 
    ((Σ[ ℓ ∈ ℕ ](ℓ ≤ n × IsMin ℓ P))
    ⊎
    ((ℓ : ℕ) → (ℓ ≤ n) → (P ℓ ≡ false))
    )
findMin 0 P with ((P 0) Data.Bool.≟ true)
... | yes P0 = 
    let f : NoSmaller 0 P
        f x x≤0 _ = n≤0⇒n≡0 x≤0
    in
    inj₁ (0 , ≤-refl , P0 , f)
... | no ¬P0 = 
    inj₂ (λ x x≤0 → subst (λ ℓ → P ℓ ≡ false) (sym (n≤0⇒n≡0 x≤0)) (¬-not ¬P0))
findMin (suc n) P with (findMin n P)
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
    let nosmallerPSn : NoSmaller (ℕ.suc n) P
        nosmallerPSn x x≤Sn Px = 
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
    in inj₁ (ℕ.suc n , ≤-refl , PSn , nosmallerPSn)
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

-- Find smallest m ≤ n such that P m ≡ true,
-- when knowing P n ≡ true.
-- Then there always is such an m! (worst case m := n works).
findMinAlwaysPoss 
    : (n : ℕ) 
    → (P : ℕ → Bool) 
    → (P n ≡ true)
    → Σ[ ℓ ∈ ℕ ](ℓ ≤ n × IsMin ℓ P)
findMinAlwaysPoss n P Pn =
    let foundMin = findMin n P
    in
    let notRightCase : ¬ ((ℓ : ℕ) → ℓ ≤ n → P ℓ ≡ false)
        notRightCase p = not-¬ (p n ≤-refl) Pn
    in
    elimCaseRight foundMin notRightCase

-- #TODO: move or remove
boolRelToSetRel
    : {A : Set}
    → {a b : A}
    → {R : A → A → Bool}
    → (R a b ≡ true)
    → (R ⊢ a ~ b)
boolRelToSetRel {A} {a} {b} {R} Rab = Rab

-- #TODO: move or remove
setRelToBoolRel
    : {A : Set}
    → {a b : A}
    → {R : A → A → Bool}
    → (R ⊢ a ~ b)
    → (R a b ≡ true)
setRelToBoolRel {A} {a} {b} {R} R⊢a~b with R a b Data.Bool.≟ true
... | yes Rab = Rab
... | no  ¬Rab = ⊥-elim (¬Rab R⊢a~b)

-- #TODO: Remove? Look how silly it is...
-- (It helped me to realise that "Transitive (R ⊢_~_)" can be directly applied
-- to Boolean equalities, by definition of the (_⊢_~_) notation!).
boolRelTrans
    : {A : Set}
    → {a b c : A}
    → {R : A → A → Bool}
    → (Transitive (R ⊢_~_))
    → (R a b ≡ true)
    → (R b c ≡ true)
    → (R a c ≡ true)
boolRelTrans {A} {a} {b} {c} {R} transR Rab Rbc = transR Rab Rbc

RelToFun : DecEquiv → NFFun
RelToFun (R , record { refl = reflR ; sym = symR ; trans = transR }) = 
    let f : ℕ → ℕ
        f n = proj₁ (findMinAlwaysPoss n (R n) (reflR {n}))
    in
    let nleq : NLeq f
        nleq n = proj₁ (proj₂ (findMinAlwaysPoss n (R n) (reflR {n})))
    in
    let nfix : NFix f
        --  To show: f (f n) ≡ f n.
        --  Intuition: 
        --  f n is the minimum m ≤ n such that R n m.
        --  f (f n) is the minimum m ≤ f n such that R (f n) m.
        --  So we have f (f n) ≤ f n ≤ n
        --  and (by transitivity) n R (f n) R (f (f n)).
        --  Hence f (f n) is also an m ≤ n such that R n m,
        --  but since f n was the minimum with this property we obtain
        --  f (f n) ≡ f n, as desired!
        nfix n = 
            let fn = proj₁ (findMinAlwaysPoss n (R n) (reflR {n}))
            in
            let ffn = proj₁ (findMinAlwaysPoss fn (R fn) reflR)
            in
            let nRfn : R n (fn) ≡ true
                nRfn = proj₁ (proj₂ (proj₂ 
                       (findMinAlwaysPoss n (R n) (reflR {n}))))
            in
            let fnRffn : R (fn) (ffn) ≡ true
                fnRffn = proj₁ (proj₂ (proj₂ 
                         (findMinAlwaysPoss fn (R fn) (reflR {fn}))))
            in
            let nRffn : R n (ffn) ≡ true
                nRffn = transR nRfn fnRffn 
            in
            let ffn≤fn : ffn ≤ fn
                ffn≤fn = proj₁ (proj₂ 
                    (findMinAlwaysPoss fn (R fn) (reflR {fn})))
            in
            let fnIsMin = proj₂ (proj₂ (proj₂ 
                          (findMinAlwaysPoss n (R n) (reflR {n}))))
            in
            fnIsMin ffn ffn≤fn nRffn
    in
    (f , nleq , nfix)

--------------------------------------------------------------------------------
-- Correspondences up to homotopy
--
-- Both DecEquiv and NFFun have the form of
-- Σ[ g ∈ (A → B) ](a bunch of properties).
-- Let X and Y be types that have a similar form,
-- and let h : X → Y and k : Y → X.
-- We define X ≊ Y 
-- (In nvim Cornelis the default mapping for ≊ is \approxeq)
-- as
-- (1) for all (g , p) ∈ X, a homotopy π₁ k(h(g, p)) ≈ g
-- and
-- (2) for all (f , q) ∈ Y, a homotopy π₁ h(k(f, q)) ≈ f
-- So ≊ expresses 
-- "isomorphism up to homotopy and proof-relevance of the bunches of properties"
--------------------------------------------------------------------------------

-- Homotopy between functions, i.e., pointwise equality.
-- I.e., the functions are the same input-output map,
-- but may have different implementations.
-- A more general, but rather overcomplicated and confusing, definition
-- can be found in the stdlib in Function.Relation.Binary.Setoid.Equality.
_≈_ : {A : Set} → {B : A → Set} → Rel ((a : A) → B a) 0ℓ
_≈_ {A} {B} f g = (a : A) → f a ≡ g a

open import Function

-- FunsWithProps is the type of dependenty functions A → B
-- with some properties.
FunsWithProps : {A : Set}
    {B : A → Set}
    → (((a : A) → B a) → Set)
    → Set
FunsWithProps {A} {B} Properties = Σ[ g ∈ ((a : A) → B a)](Properties g)

-- "Equivalence between types of functions-with-properties
-- up to first-projection-homotopy and proof-relevance of the properties".
record _≊_ 
    {A A' : Set}
    {B : A → Set}
    {B' : A' → Set}
    (P : ((a : A) → B a) → Set)
    (P' : ((a : A') → B' a) → Set)
    : Set
    where
    field
        leftToRight : FunsWithProps P  → FunsWithProps P'
        rightToLeft : FunsWithProps P' → FunsWithProps P
        almostInvL : (proj₁ ∘ rightToLeft ∘ leftToRight) ≡ proj₁
        almostInvR : (proj₁ ∘ leftToRight ∘ rightToLeft) ≡ proj₁

--------------------------------------------------------------------------------
-- Localisible properties
--
-- The intend is to capture the following:
-- a property of an equivalence relation on an enumerable set
-- A = {a₀, a₁, a₂, ...}
-- is 'localisible' if it is defined as an ℕ-indexed family of predicates
-- P that checks,
-- given a relation Rₙ₋₁ on [a₀, ..., aₙ₋₁] (that satisfies P)*
-- whether an extension of Rₙ₋₁ to Rₙ 
-- by choosing an equivalence class chosen for aₙ maintains P.
--
-- * In implementation we do not enforce this condition,
-- in the sense that we require that P holds 
-- on all restrictions of R to prefixes of A, not in any particular order.
--
-- Localisible properties give a tool for building normalisation functions, 
-- and hence for building equivalence relations, 
-- and hence for building quotient types:
-- Start with the relation a₀ R a₀, i.e., with one equivalence class [a₀]
-- on the restriction {a₀}
-- and for each n ≥ 1, choose an equivalence class (either an existing class or
-- a new one) for aₙ, such that P still holds.
--
-- This is especially useful if it is hard to check P on a global relation
-- on ℕ (congruence, associativity, commutativity seem hard to define as a
-- function A → A → Bool!), 
-- but the local check on each {a₀, ..., aₙ} is decidable
-- (which in practise is often the case: checking 
-- if a finite equivalence relation
-- on the finite set {a₀, ..., aₙ} is congruent/associative/commutativity is
-- easy, just brute force!)
--------------------------------------------------------------------------------


