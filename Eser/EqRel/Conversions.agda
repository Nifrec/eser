-- Module      : Eser.EqRel.Definitions
-- Description : Conversions between representations of equivalence relations
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties using (¬-not ; not-¬)
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_≤_ ; _≤?_)
open import Data.Vec hiding (restrict)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; ≤-<-trans ; n≤0⇒n≡0 
                                       ; n≤1+n ; m≤n⇒m<n∨m≡n ; _≤?_ ; ≰⇒≥)
open import Data.Fin.Properties using (toℕ<n)
open import Relation.Nullary -- Needed for with-abstractions on decidable ≡.
open import Function hiding (_↔_)
open import Data.List hiding (lookup ; last)


open import Eser.Logic using (elimCaseLeft ; elimCaseRight)
open import Eser.Aux
open import Eser.EqRel.Definitions

module Eser.EqRel.Conversions where

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

minUnique
    : (n m : ℕ) 
    → (P : ℕ → Bool)
    → (IsMin n P)
    → (IsMin m P)
    → n ≡ m
minUnique n m P (Pn , noSmallerN) (Pm , noSmallerM) with (n ≤? m)
... | yes n≤m = noSmallerM n n≤m Pn
... | no  n≰m =
    let m≤n : m ≤ n
        m≤n = ≰⇒≥ n≰m
    in
    sym (noSmallerN m m≤n Pm)

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
    let nleq : NFLeq f
        nleq n = proj₁ (proj₂ (findMinAlwaysPoss n (R n) (reflR {n})))
    in
    let nfix : NFFix f
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
