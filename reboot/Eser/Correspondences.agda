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
                                       ; n≤1+n ; m≤n⇒m<n∨m≡n)
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

decEqToPredEq
    : {m n : ℕ}
    → ((m ≡ᵇ n) ≡ true)
    → m ≡ n
decEqToPredEq {m} {n} m≡ᵇn with m ≡ᵇ n
    -- Hmm this is not so obvious...
    -- but for ℕ we know that nums are either equal or not?
... | true m≡n 

lemma4 
    : (f : ℕ → ℕ) 
    → (nleq : NFLeq f) 
    → (nfix : NFFix f)
    → (n : ℕ)
    → (H : (f n ≡ᵇ f n) ≡ true) -- That's obvious!
    → proj₁ (findMinAlwaysPoss n (λ m → f n ≡ᵇ f m) H) ≡ f n
lemma4 f nleq nfix ℕ.zero H = 
    begin 
    proj₁ (findMinAlwaysPoss 0 (λ m → f 0 ≡ᵇ f m) H)
    ≡⟨  findMinZeroLemma (λ m → f 0 ≡ᵇ f m) H ⟩
    0
    ≡⟨ sym ( n≤0⇒n≡0 (nleq 0)) ⟩
    f 0
    ∎
lemma4 f nleq nfix (ℕ.suc n) H = 
    let (ℓ , ℓ≤Sn , fSn≡fℓ , noSmallerℓ) = 
            (findMinAlwaysPoss (ℕ.suc n) (λ m → f (ℕ.suc n) ≡ᵇ f m) H)
    in
    -- Need make case distinction: f (ℕ.suc n) ≤ ℓ or not. In case of former:
    -- No wait, fSn≡fℓ but we have also nleq!
    -- So that gives fSn≤ℓ already
    let Sn≤ℓ : f (ℕ.suc n) ≤ ℓ
        -- Need to convert "(f (ℕ.suc n) ≡ᵇ f ℓ) ≡ true" to ≡.
        -- Do this for general `A ≡ᵇ B ≡ true → A ≡ B`.
        -- Didn't I already?
        Sn≤ℓ = subst (λ x → x ≤ ℓ) ({! sym fSn≡fℓ !}) (nleq ℓ)
    in
    let fSn = f (ℕ.suc n)
    in
    {! sym (noSmallerℓ (fSn)   ) !}

lemma3 
    : (f : ℕ → ℕ) 
    → (nleq : NFLeq f) 
    → (nfix : NFFix f)
    → (R : DecEquiv)
    → (defR : proj₁ R ≡ λ (n m : ℕ) → f n ≡ᵇ f m)
    → (proj₁ ∘ RelToFun) R ≈ f
lemma3 f nleq nfix R refl n = 
    begin 
    (proj₁ ∘ RelToFun) R n
    ≡⟨ lemma1 R n ⟩
    proj₁ (findMinAlwaysPoss n ((proj₁ R) n) (((IsEquivalence.refl ∘ proj₂) R) {n}))
    ≡⟨ refl ⟩
    proj₁ (findMinAlwaysPoss n (λ m → f n ≡ᵇ f m) (((IsEquivalence.refl ∘ proj₂) R) {n}))
    ≡⟨ ? ⟩
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


