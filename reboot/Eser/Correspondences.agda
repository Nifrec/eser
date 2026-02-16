-- Module      : Eser.Correspondences
-- Description : Theorems about correspondences between DecRel and NFFun.
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
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Vec hiding (restrict)
open import Relation.Nullary -- Needed for with-abstractions on decidable ≡.
open import Function
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
-- RelToFun and FunToRel form an isomorphism 'up to proj₁ homotopy'.
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

--lemma2 : 
--    : (F : NFFun) 
--    → (proj₁ ∘ RelToFun ∘ FunToRel) 
--        ≈ 
--        λ n → proj₁ (findMinAlwaysPoss n ((proj₁ R) n) 
--        (((IsEquivalence.refl ∘ proj₂) R) {n}))
-- The Fun → Rel → Fun map is homotopic to id_{Fun}.
-- 
FRFHomot : (F : NFFun) → (proj₁ ∘ RelToFun ∘ FunToRel) F ≈ proj₁ F
FRFHomot F@(f , nleq , nfix) ℕ.zero = 
    let fn≤0 : f ℕ.zero ≤ ℕ.zero
        fn≤0 = nleq 0
    in
    let fn≡0 : f ℕ.zero ≡ ℕ.zero
        fn≡0 = n≤0⇒n≡0 fn≤0
    in
    let R = FunToRel F
    in
    let _ = {! ((proj₁ ∘ RelToFun ∘ FunToRel) F) ℕ.zero !}
    in
    {!
    begin 
    {! ((proj₁ ∘ RelToFun ∘ FunToRel) F) ℕ.zero !}
    ≡⟨ {! lemma1 R 0 !} ⟩
    {! proj₁ (findMinAlwaysPoss 0 ((proj₁ R) 0) (((IsEquivalence.refl ∘ proj₂) R) {0})) !}
    --≡⟨ ? ⟩
    --    ℕ.zero
    --≡⟨ sym fn≡0 ⟩
    --    f ℕ.zero
    --∎
    !}
FRFHomot (f , nleq , nfix) (ℕ.suc n) = {! !}


