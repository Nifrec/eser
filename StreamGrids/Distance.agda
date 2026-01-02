-- Module      : StreamGrids.Distance
-- Description : Distances between numbers in sets of same cardinality
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Functions dist, finDist, and distCard allow to compute distances
-- from a smaller number to a greater one in ℕ, Fin n or cardToSet c,
-- respectively.
-- The main use case are functions f(i, j) where the distance from i to j 
-- decreases every recursive call; `iterFromTill` in StreamGrids.Construction
-- was the main need in this project (look there for how it is used in
-- combination with "fuel" to please the termination checker).
-- * The theorem `decrDist` proves that the distance i+1 to j
--      is one less than the distance from i to j.
-- * The theorem distCardNonZero proves that the output of distCard is never 0.
--
-- These things were suprisingly hard to prove, and involved some lengthy
-- lemmas. Simplifications in the proofs might be possible.

module StreamGrids.Distance where

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
open import Data.Unit
open import Data.Empty

open import StreamGrids.Card
open import StreamGrids.Fin

-- Compute distance from one number to a greater one.
-- E.g., dist 1 4 ≐ 3 and dist 2 3 ≐ 1.
dist : {n m : ℕ} → n Data.Nat.< m → ℕ
dist {ℕ.zero} {m} (s≤s z≤n) = m
dist {ℕ.suc n} {ℕ.suc m} (s≤s n<m) = dist {n} {m} (n<m)

-- Same as dist, but for finite sets,
finDist : {c : ℕ} → {n m : Fin c} → (n<m : n Data.Fin.< m) → ℕ 
finDist n<m = dist n<m

-- Same as dist, but generalised to work for both ℕ and finite sets.
distCard 
    : {c : ℕ∞}
    → {n m : cardToSet c}
    → cardTo< n m
    → ℕ
distCard {∞} {n} {m} n<m = dist n<m
distCard {fin (suc c)} {n} {m} n<m = dist n<m

lemma'
    : {n : ℕ}
    → {j k : Fin (ℕ.suc n)}
    → (j<k : j Data.Fin.< k)
    → (Sj<k : (ℕ.suc (toℕ j)) Data.Nat.<  (toℕ k))
    → ℕ.suc (distCard {∞} Sj<k) ≡ distCard {fin (ℕ.suc n)} j<k
lemma' {n} {Fin.zero} {Fin.suc (Fin.suc k)} (s≤s z≤n) (s≤s (s≤s z≤n)) = refl
lemma' {ℕ.suc n} {Fin.suc j} {Fin.suc k} (s≤s j<k) (s≤s Sj<k) = 
    let rec = lemma' j<k Sj<k in rec

-- Distance d from 1 to k is k-1, or equivalently, d+1 is k.
lemma'''
    : {c : ℕ}
    → {k : Fin (ℕ.suc c)}
    → (0<k : Data.Fin.zero {ℕ.suc c} Data.Fin.< k)
    → (S0<k : toℕ (endoSuc (biggerToIsNotMax 0<k)) Data.Nat.< (toℕ k))
    → ℕ.suc (distCard {fin (ℕ.suc c)} S0<k) ≡ toℕ k
lemma''' {ℕ.zero} {Fin.zero} () S0<k
lemma''' {ℕ.zero} {Fin.suc ()} (s≤s z≤n) (s≤s S0<k)
lemma''' {c@(ℕ.suc c'@(ℕ.suc c''))} 
         {Fin.suc (Fin.suc k)} 
         (s≤s z≤n) 
         p@(s≤s 0<Sk) = 
    let u : cardTo< {fin (ℕ.suc c)} (Fin.suc Fin.zero) (Fin.suc (Fin.suc k)) 
        u = s≤s (s≤s z≤n)
    in
    let p≡u : p ≡ u
        p≡u = Data.Nat.Properties.≤-irrelevant (s≤s 0<Sk) u
    in
    let normalOutp : ℕ
        normalOutp = distCard {fin (ℕ.suc c)} u
    in
    let outpValue : normalOutp ≡ (ℕ.suc (toℕ k))
        outpValue = refl
    in
    let outp≡outu : distCard {fin (ℕ.suc c)} p ≡ normalOutp
        outp≡outu = cong (distCard {fin (ℕ.suc c)}) p≡u
    in
    cong ℕ.suc (trans outp≡outu outpValue)

lemma''
    : {c : ℕ}
    → {j k : Fin (ℕ.suc c)}
    → (j<k : j Data.Fin.< k)
    → (STj<k : (ℕ.suc (toℕ j)) Data.Nat.<  (toℕ k))
    → (Sj<k : toℕ (endoSuc (biggerToIsNotMax j<k)) Data.Nat.< (toℕ k))
    → distCard {fin (ℕ.suc c)} Sj<k ≡ distCard {∞} STj<k
lemma'' {c} {Fin.zero} {Fin.suc k@(Fin.suc k')} (s≤s z≤n) 
        STj<k@(s≤s (s≤s z≤n)) (s≤s Sj<k) =
    let LHS = distCard {fin (ℕ.suc c)} (s≤s Sj<k)
    in
    -- The LHS does not reduce to a value automatically, but we have a lemma
    -- for that. It just needs 
    let LHSvalueAlmost : ℕ.suc LHS ≡ toℕ (Fin.suc k)
        LHSvalueAlmost = lemma''' (s≤s z≤n) (s≤s Sj<k)
    in
    let LHSvalue : LHS ≡ toℕ k
        LHSvalue = Data.Nat.Properties.suc-injective LHSvalueAlmost
    in
    let call = lemma''' (s≤s z≤n) (s≤s Sj<k)
    in
    let _ = distCard {fin (ℕ.suc c)} (s≤s Sj<k)
    in
    let RHS = distCard {∞} STj<k
    in
    let RHSvalue : RHS ≡ toℕ k -- The RHS computes nicely. 
        RHSvalue = refl
    in
    trans LHSvalue (sym RHSvalue)
lemma'' {ℕ.suc c} {Fin.suc j} {Fin.suc k} (s≤s j<k) (s≤s STj<k) (s≤s Sj<k) =
    let rec = lemma'' {c} {j} {k} j<k STj<k Sj<k
    in
    rec

--Incrementing the lower of two numbers decreases the distance by 1.
decrDist
    : {c : ℕ∞}
    → {j k : cardToSet c}
    → (j<k : cardTo< j k)
    → (Sj<k : cardTo< (endoSuc (biggerToIsNotMax j<k)) k)
    → ℕ.suc (distCard {c} Sj<k) ≡ distCard {c} j<k
decrDist {∞} {ℕ.zero} {ℕ.suc k} (s≤s z≤n) (s≤s (s≤s z≤n)) = refl
decrDist {∞} {ℕ.suc j} {ℕ.suc k} (s≤s j<k) (s≤s Sj<k) =
    decrDist {∞} {j} {k} (j<k) (Sj<k)
decrDist {fin (suc c)} {j} {k} j<k Sj<k =
    let h = biggerToIsNotMax j<k in
    let STj<k : (ℕ.suc (toℕ j)) Data.Nat.<  (toℕ k) 
        STj<k = subst (λ x → x Data.Nat.< (toℕ k)) 
                     (endoSucInjToNatSuc h)
                     Sj<k
    in
    let H₁ :  ℕ.suc (distCard {∞} STj<k) ≡ distCard {fin (ℕ.suc c)} j<k
        H₁ = lemma' j<k STj<k
    in
    let
        H₂ : distCard {fin (ℕ.suc c)} Sj<k ≡ distCard {∞} STj<k
        H₂ = lemma'' j<k STj<k Sj<k
    in
    trans (cong ℕ.suc H₂) H₁

-- distCard requires to prove that j<k, 
-- so the distance from j to k is always greater than zero.
distCardNonZero
    : {c : ℕ∞}
    → {j k : cardToSet c}
    → (j<k : cardTo< {c} j k)
    → ℕ.zero Data.Nat.< distCard {c} j<k
distCardNonZero {fin (ℕ.suc c)} {Fin.zero} {Fin.suc k} (s≤s z≤n) = s≤s z≤n
distCardNonZero {fin (ℕ.suc (ℕ.suc c))} {Fin.suc j} {Fin.suc k} (s≤s j<k) = 
    distCardNonZero {fin (ℕ.suc c)} {j} {k} j<k
distCardNonZero {∞} {ℕ.zero} {ℕ.suc k} (s≤s z≤n) = s≤s z≤n
distCardNonZero {∞} {ℕ.suc j} {ℕ.suc k} (s≤s j<k) = 
    distCardNonZero {∞} {j} {k} j<k
