-- Module      : Eser.Correspondences
-- Description : Theorems about correspondences between DecRel and NFFun.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- RelToFun and FunToRel form an isomorphism 'up to proj₁ homotopy'.
open import Level
open import Data.Bool hiding (_≤_ ; _<_)
open import Data.Bool.Properties using (¬-not ; not-¬)
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Vec hiding (restrict)
open import Relation.Nullary -- Needed for with-abstractions on decidable ≡.
open import Function hiding (_↔_)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; ≤-<-trans ; n≤0⇒n≡0 
                                       ; n≤1+n ; m≤n⇒m<n∨m≡n ; ≡ᵇ⇒≡)
open ≡-Reasoning

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

open import Eser.Definitions

module Eser.Correspondences where

--------------------------------------------------------------------------------
-- Part 1 : FRF(f) ≈ f
-- Mapping a function to a relation and back yields a NFFun homotopic to the
-- input fun.
--------------------------------------------------------------------------------

-- If P 0 holds then the smallest m s.t. m ≤ 0 and P m
-- is obviously 0 itself, since no m has m < 0.
findMinZeroLemma
    : (P : ℕ → Bool) 
    → (P0 : P ℕ.zero ≡ true)
    → proj₁ (findMinAlwaysPoss ℕ.zero P P0) ≡ ℕ.zero
findMinZeroLemma P P0 = 
    let H = findMinAlwaysPoss ℕ.zero P P0
    in
    let ℓ≤0 = proj₁ (proj₂ H)
    in
    n≤0⇒n≡0 ℓ≤0

lemma1 
    : (R : DecEquiv) 
    → (proj₁ ∘ RelToFun) R 
        ≈ 
        λ n → proj₁ (findMinAlwaysPoss n ((proj₁ R) n) 
        (((IsEquivalence.refl ∘ proj₂) R) {n}))
lemma1 R n = refl

_$$_ : NFFun → ℕ → ℕ
F $$ n = (proj₁ F) n

-- We can substitute this directly into lemma1 when we know R is of the
-- form R ≗ (FunToRel F).
lemma2 : (F : NFFun) → proj₁ (FunToRel F) ≡ λ (n m : ℕ) → F $$ n ≡ᵇ F $$ m
lemma2 (f , nleq , nfix) = refl

-- Convert a proof that m ≡ᵇ n is true
-- to a proof of m ≡ n.
decEqToPredEq
    : {m n : ℕ}
    → ((m ≡ᵇ n) ≡ true)
    → m ≡ n
decEqToPredEq {m} {n} m≡ᵇn = 
    -- Implementation: we know `true ≡ (m ≡ᵇ n)`
    -- and we know `tt : T true`.
    -- Apply a dependent transport (subst)
    -- to get `tt' : T (m ≡ᵇ n)`, 
    -- which serves as input to the stdlib lemma ≡ᵇ⇒≡.
    ≡ᵇ⇒≡ m n (subst T (sym m≡ᵇn) tt)

predEqToDecEq
    : {m n : ℕ}
    → m ≡ n
    → ((m ≡ᵇ n) ≡ true)
-- Use the inductive definition of ≡ᵇ to make the (m ≡ᵇ n) in the goal compute.
-- Path induction reduces the goal to (m ≡ᵇ m) ≡ true.
-- If m ≗ ℕ.zero then this reduces to true ≡ true.
predEqToDecEq {ℕ.zero} refl = refl
-- If m ≗ ℕ.suc m' then the goal reduces to (m' ≡ᵇ m') ≡ true,
-- which we get by induction.
predEqToDecEq {ℕ.suc m} refl = predEqToDecEq {m} {m} refl

predNeqToDecNeq
    : {m n : ℕ}
    → m ≢ n
    → ((m ≡ᵇ n) ≡ false)
predNeqToDecNeq {m} {n} m≢n with ((m ≡ᵇ n) Data.Bool.≟ true)
... | yes m≡ᵇn = ⊥-elim (m≢n (decEqToPredEq m≡ᵇn))
... | no  m≢ᵇn = ¬-not m≢ᵇn

-- Normal forms are the smallest elements of their equivalence class.
-- (Equivalence classes are fibers of the normal-form function f).
-- More precisely, the minimum m s.t. m ≤ n and such that f n ≡ f m
-- is always f n. This follows from the fact that f n ≤ n (by NFLeq),
-- and for any m with f m ≡ f n hence also f n ≡ f m ≤ m,
-- so f n is ≤ than all inputs that f sends to it.
nfIsSmallestInClass 
    : (f : ℕ → ℕ) 
    → (nleq : NFLeq f) 
    → (nfix : NFFix f)
    → (n : ℕ)
    → (H : (f n ≡ᵇ f n) ≡ true) -- That's obvious!
    → proj₁ (findMinAlwaysPoss n (λ m → f n ≡ᵇ f m) H) ≡ f n
nfIsSmallestInClass f nleq nfix ℕ.zero H = 
    begin 
    proj₁ (findMinAlwaysPoss 0 (λ m → f 0 ≡ᵇ f m) H)
    ≡⟨  findMinZeroLemma (λ m → f 0 ≡ᵇ f m) H ⟩
    0
    ≡⟨ sym ( n≤0⇒n≡0 (nleq 0)) ⟩
    f 0
    ∎
nfIsSmallestInClass f nleq nfix (ℕ.suc n) H = 
    let (ℓ , ℓ≤Sn , fSn≡ᵇfℓ , noSmallerℓ) = 
            (findMinAlwaysPoss (ℕ.suc n) (λ m → f (ℕ.suc n) ≡ᵇ f m) H)
    in
    -- Need make case distinction: f (ℕ.suc n) ≤ ℓ or not. In case of former:
    -- No wait, fSn≡fℓ but we have also nleq!
    -- So that gives fSn≤ℓ already
    let fℓ≡fSn : f ℓ ≡ f (ℕ.suc n)
        fℓ≡fSn = sym (decEqToPredEq fSn≡ᵇfℓ)
    in
    let Sn≤ℓ : f (ℕ.suc n) ≤ ℓ
        -- Need to convert "(f (ℕ.suc n) ≡ᵇ f ℓ) ≡ true" to ≡.
        -- Do this for general `A ≡ᵇ B ≡ true → A ≡ B`.
        -- Didn't I already?
        Sn≤ℓ = subst (λ x → x ≤ ℓ) fℓ≡fSn (nleq ℓ)
    in
    let fSn = f (ℕ.suc n)
    in
    let fSn≡ᵇffSn : (fSn ≡ᵇ f fSn) ≡ true
        fSn≡ᵇffSn = predEqToDecEq (sym (nfix (ℕ.suc n)))
    in
    sym (noSmallerℓ fSn Sn≤ℓ fSn≡ᵇffSn)

lemma3 
    : (f : ℕ → ℕ) 
    → (nleq : NFLeq f) 
    → (nfix : NFFix f)
    → (R : DecEquiv)
    → (defR : proj₁ R ≡ λ (n m : ℕ) → f n ≡ᵇ f m)
    → (proj₁ ∘ RelToFun) R ≈ f
lemma3 f nleq nfix R refl n = 
    let H : (f n ≡ᵇ f n) ≡ true
        -- This is also the definition used in the implementation of RelToFun,
        -- as input to its own call to findMinAlwaysPoss.
        -- Not important: it is proof-irrelevant anyway.
        H = ((IsEquivalence.refl ∘ proj₂) R) {n} 
    in
    begin 
    (proj₁ ∘ RelToFun) R n
    ≡⟨ lemma1 R n ⟩
    proj₁ (findMinAlwaysPoss n ((proj₁ R) n) H)
    ≡⟨ refl ⟩
    proj₁ (findMinAlwaysPoss n (λ m → f n ≡ᵇ f m) H)
    ≡⟨ nfIsSmallestInClass f nleq nfix n H ⟩
    f n
    ∎

-- For all NFFuns f, mapping Fun → Rel → Fun on f gives a NFFun homotopic to f.
-- (Note: we are NOT proving 
-- that `proj₁ ∘ RelToFun ∘ FunToRel` and `proj₁` are homotopic themselves,
-- but instead that THEIR OUTPUTS are homotopic.)
FRFHomot : (F : NFFun) → (proj₁ ∘ RelToFun ∘ FunToRel) F ≈ proj₁ F
FRFHomot F@(f , nleq , nfix) = lemma3 f nleq nfix (FunToRel F) (lemma2 F) 

--------------------------------------------------------------------------------
-- Part 2 : RFR(R) ≈ R
-- Mapping a decidable equivalence relation to a NFFun and back,
-- yields a relation ℕ → ℕ → Bool homotopic to the input relation.
--------------------------------------------------------------------------------


-- General fact about an equivalence relation R ⊆ ℕ×ℕ:
-- if nRm then the equivalence classes [n] and [m] are the same,
-- and hence the same subset of ℕ, and hence have the same minimum.
-- I.e., nRm iff (Min_ℓ(ℓ≤n ∧ nRℓ) ≡ Min_ℓ(ℓ≤m ∧ mRℓ))
oneMinPerClass
    : (R : ℕ → ℕ → Bool)
    → (Req : IsEquivalence (R ⊢_~_))
    → (n m : ℕ)
    → (hₙ : R n n ≡ true) -- This type is proof-irrelevant.
    → (hₘ : R m m ≡ true) -- This one too.
    → (R n m) ≡ 
        (
        proj₁ (findMinAlwaysPoss n (R n) hₙ)
        ≡ᵇ
        proj₁ (findMinAlwaysPoss m (R m) hₘ)
        )
oneMinPerClass R Req n m hₙ hₘ
    using ℓ ← (proj₁ (findMinAlwaysPoss n (R n) hₙ))
    using k ← (proj₁ (findMinAlwaysPoss m (R m) hₘ))
    with ((R n m) Data.Bool.≟ true)
... | yes nRm = 
    let symR : Symmetric (R ⊢_~_)
        symR = IsEquivalence.sym Req
    in
    let transR : Transitive (R ⊢_~_)
        transR = IsEquivalence.trans Req
    in
    let nRℓ : (R n ℓ ≡ true)
        nRℓ = proj₁ (proj₂ (proj₂ (findMinAlwaysPoss n (R n) hₙ)))
    in
    let isSmallestℓn : NoSmaller ℓ (R n)
        isSmallestℓn = proj₂ (proj₂ (proj₂ (findMinAlwaysPoss n (R n) hₙ)))
    in
    let mRℓ : (R m ℓ ≡ true)
        mRℓ = transR (symR nRm) nRℓ
    in
    let isSmallestℓm : NoSmaller ℓ (R m)
        isSmallestℓm x x≤ℓ mRx =
            let nRx : (R n x ≡ true)
                nRx = transR nRm mRx
            in isSmallestℓn x x≤ℓ nRx
    in
    let isminℓm : IsMin ℓ (R m)
        isminℓm = (mRℓ , isSmallestℓm)
    in
    let isminkm : IsMin k (R m)
        isminkm = proj₂ (proj₂ (findMinAlwaysPoss m (R m) hₘ))
    in
    let ℓ≡k : ℓ ≡ k
        ℓ≡k = minUnique ℓ k (R m) isminℓm isminkm
    in
    trans nRm (sym (predEqToDecEq ℓ≡k))
... | no  ¬nRm with (ℓ Data.Nat.≟ k)
...     | yes ℓ≡k = 
        -- Derive a contradiction from nRℓ and kRm, since refl gives ℓRk,
        -- and hence transitivity gives nRm.
        let reflR : Reflexive (R ⊢_~_)
            reflR = IsEquivalence.refl Req
        in
        let transR : Transitive (R ⊢_~_)
            transR = IsEquivalence.trans Req
        in
        let symR : Symmetric (R ⊢_~_)
            symR = IsEquivalence.sym Req
        in
        let nRℓ : (R n ℓ ≡ true)
            nRℓ = proj₁ (proj₂ (proj₂ (findMinAlwaysPoss n (R n) hₙ)))
        in
        let ℓRk : (R ℓ k ≡ true)
            ℓRk = subst (λ v → R ℓ v ≡ true) ℓ≡k (reflR {ℓ}) 
        in
        let kRm : (R k m ≡ true)
            kRm = symR (proj₁ (proj₂ (proj₂ (findMinAlwaysPoss m (R m) hₘ))))
        in
        let nRm : (R n m ≡ true)
            nRm = transR (transR nRℓ ℓRk) kRm
        in
        ⊥-elim (¬nRm nRm)
...     | no  ℓ≢k = 
        let nRm≡false : (R n m) ≡ false
            nRm≡false = ¬-not ¬nRm
        in
        let false≡[ℓ≡k] : false ≡ (ℓ ≡ᵇ k)
            false≡[ℓ≡k] = sym (predNeqToDecNeq ℓ≢k) 
        in
        trans nRm≡false false≡[ℓ≡k]

-- The relation R' outputted by (proj₁ ∘ FunToRel ∘ RelToFun) R
-- has nR'm 
-- if the min ℓ≤n s.t. nRℓ equals the min ℓ≤m s.t. mRℓ.
RFRLemma 
    : (R : DecEquiv) 
    → (proj₁ ∘ FunToRel ∘ RelToFun) R 
        ≡ 
        λ (n m : ℕ) → (
        proj₁ (findMinAlwaysPoss n (proj₁ R $ n) (IsEquivalence.refl (proj₂ R) {n}))
        ≡ᵇ
        proj₁ (findMinAlwaysPoss m (proj₁ R $ m) (IsEquivalence.refl (proj₂ R) {m}))
        )
RFRLemma R = refl

-- #TODO: remove? currently it is more of a personal note.
--
-- If f, g : A → B → C
-- have that (f a b) ≡ (g a b),
-- then we can prove that 
--      λ(a, b) ∈ A×B → f a b
--  is homotopic to
--      λ(a, b) ∈ A×B → g a b
--  (and also that f a ≈ g a for all a : A,
--  but we CANNOT prove that f ≈ g without function extensionality).
doubleArgHomot
    : {A B C : Set}
    → (f g : A → B → C)
    → ((a : A) → (b : B) → f a b ≡ g a b)
    → uncurry f ≈ uncurry g
doubleArgHomot R S H = uncurry H

-- Mapping a decidable equivalence to a NFFunction and back
-- yields the same relation as one started with,
-- up to first-projection homotopy.
--
-- Technical detail: we only proved it is homotopic to the original relation
-- when evaluating both arguments in ℕ at the same time.
-- So this proof uncurries R : ℕ → ℕ → Bool (for which we didn't prove homotopy)
-- to R : ℕ × ℕ → Bool for which we did prove homotopy.
RFRHomot 
    : (R : DecEquiv) 
    → (uncurry ∘ proj₁ ∘ FunToRel ∘ RelToFun) R ≈ (uncurry ∘  proj₁) R
RFRHomot R (n , m) = 
    let H₁ = RFRLemma R
    in
    let hₙ : (proj₁ R) n n ≡ true
        hₙ = IsEquivalence.refl (proj₂ R) {n}
    in
    let hₘ : (proj₁ R) m m ≡ true
        hₘ = IsEquivalence.refl (proj₂ R) {m}
    in
    let H₂ = oneMinPerClass (proj₁ R) (proj₂ R) n m hₙ hₘ
    in
    let H₃ = cong (λ x → (uncurry x) (n , m)) H₁
    in
    trans H₃ (sym H₂)

--------------------------------------------------------------------------------
-- Preservation of properties
-- The isomorphism-up-to-proj₁-homotopies preserves localisible properties.
--
-- More precisely:
-- Let P = (Prel, Ploc) be a localisible property,
-- then
-- (1) Prel R            <-> AllRestr (RelToFun R) Ploc
-- (2) Prel (FunToRel) f <-> AllRestr f Ploc
--------------------------------------------------------------------------------
open LocalisibleProp

-- (1) This direction is trivial, since it holds by definition
-- of a localisible property.
RelToFunPresvProps
    : (P : LocalisibleProp)
    → (R : DecEquiv)
    → Prel P R ↔ AllRestr ((proj₁ ∘ RelToFun) R) (Ploc P)
RelToFunPresvProps P R = correspondence P R

applyEqArgs 
    : {A B C : Set}
    → {a a' : A}
    → {b b' : B}
    → (_app_ : A → B → C)
    → (a ≡ a')
    → (b ≡ b')
    → (a app b ≡ a' app b')
applyEqArgs {A} {B} {C} {a} {a'} {b} {b'} _app_ a≡a' b≡b' =
    begin 
    a app b
    ≡⟨ cong (_app b) a≡a' ⟩
    a' app b
    ≡⟨ cong (a' app_) b≡b' ⟩
    a' app b'
    ∎
    
-- If f ≈ g
-- then λn.(restrict n f) ≈ λn.(restrict n g)
-- i.e., they pointwise output the same vectors.
homotRestrictLift
    : {f g : ℕ → ℕ}
    → (f ≈ g)
    → (n : ℕ)
    → (restrict n f) ≡ (restrict n g)
homotRestrictLift {f} {g} f≈g ℕ.zero = refl
homotRestrictLift {f} {g} f≈g (ℕ.suc n) = 
    let fn≡gn = f≈g n
    in
    let restOfVectorsEqual : restrict n f ≡ restrict n g
        restOfVectorsEqual = homotRestrictLift {f} {g} f≈g n
    in
    applyEqArgs _∷_ fn≡gn restOfVectorsEqual


    
-- Lemma for proving (2):
-- if f ≈ g then f locally satisfies a LocProp
-- iff g locally satisfies it.
-- (This is an advantage of local properties: for properties
-- on relations we *cannot* show `R≈S → (Prel R ↔ Prel S)`).
-- First a sub-lemma that proves only the "→" direction.
-- The bigger "↔" follows from symmetry (note ≈ is symmetric).
homotsPreserveAllRestrSat→
    : {f g : ℕ → ℕ}
    → (f ≈ g)
    → (Ploc : LocProp)
    → AllRestr f Ploc → AllRestr g Ploc
homotsPreserveAllRestrSat→ {f} {g} f≈g Ploc AllRestrF n = 
    subst (λ vec → Ploc n vec) (homotRestrictLift f≈g n) (AllRestrF n)

-- Two-direction version of previous lemma.
homotsPreserveAllRestrSat
    : {f g : ℕ → ℕ}
    → (f ≈ g)
    → (Ploc : LocProp)
    → AllRestr f Ploc ↔ AllRestr g Ploc
homotsPreserveAllRestrSat f≈g Ploc = 
    let LtoR = homotsPreserveAllRestrSat→ f≈g Ploc
    in
    let RtoL = homotsPreserveAllRestrSat→ (≈-sym f≈g) Ploc
    in
    (LtoR , RtoL)

FunToRelPresvProps→
    : (P : LocalisibleProp)
    → (f : NFFun)
    → Prel P (FunToRel f) 
    → AllRestr (proj₁ f) (Ploc P)
FunToRelPresvProps→ (localisibleProp Prel Ploc corresp) f PrelR =
    let R : DecEquiv
        R = FunToRel f
    in
    let H : AllRestr ((proj₁ ∘ RelToFun ∘ FunToRel) f ) Ploc
        H = proj₁ (corresp R) PrelR
    in
    let FRFf≈f = (proj₁ ∘ RelToFun ∘ FunToRel) f ≈ (proj₁ f)
        FRFf≈f = FRFHomot f
    in
    homotsPreserveAllRestrSat→ FRFf≈f Ploc H

FunToRelPresvProps←
    : (P : LocalisibleProp)
    → (f : NFFun)
    → AllRestr (proj₁ f) (Ploc P)
    → Prel P (FunToRel f) 
FunToRelPresvProps← (localisibleProp Prel Ploc corresp) f PlocF =
    -- We cannot apply the definition of a localisible property
    -- because f is not of the shape `RelToFun R`.
    -- However, we can map f first to a relation and then back to a function f',
    -- which is of the right shape, and by FRFHomot still homotopic to f itself.
    let R = FunToRel f
    in
    let f' = proj₁ (RelToFun (FunToRel f))
    in
    let f'≈f : f' ≈ proj₁ f
        f'≈f = FRFHomot f
    in
    let PlocF' : AllRestr f' Ploc
        PlocF' = λ n → subst (λ restr → Ploc n restr)
                    (homotRestrictLift {proj₁ f} {f'} (≈-sym f'≈f) n)
                    (PlocF n)
    in
    proj₂ (corresp R) PlocF'

-- (2) That FunToRel preserves properties is not so trivial.
FunToRelPresvProps
    : (P : LocalisibleProp)
    → (f : NFFun)
    → Prel P (FunToRel f) ↔ AllRestr (proj₁ f) (Ploc P)
FunToRelPresvProps P f = (FunToRelPresvProps→ P f , FunToRelPresvProps← P f)
