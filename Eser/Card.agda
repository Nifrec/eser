-- Module      : Eser.Card
-- Description : Tools for working with sets of different cardinalities.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Originally developed for the deprecated `StreamGrids` implementation
-- of this library, now replaced with the `Eser` implementation.
-- Hence there are a lot of now-unused lemmas.

-- TODO: probably not all of these are needed.
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.Empty
open import Data.Fin hiding (_<_)
open import Data.Fin.Properties
open import Function using (Inverseᵇ)
open import Data.List
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Relation.Nullary
open import Data.Unit.Properties using (⊤-irrelevant)
open import Function

open import Eser.Fin

module Eser.Card where

--------------------------------------------------------------------------------
-- ℕ∞ is the type of cardinalities.
--------------------------------------------------------------------------------

-- Natural numbers extended with a top element '∞' (w.r.t. the '<' relation).
data ℕ∞ : Set where
    fin     : ℕ → ℕ∞
    ∞       : ℕ∞

suc∞ : ℕ∞ → ℕ∞
suc∞ (fin n) = fin (suc n)
suc∞ ∞ = ∞

_<∞_ : Rel ℕ∞ 0ℓ
fin n <∞ fin m  = n Data.Nat.< m
fin n <∞ ∞      = ⊤
∞     <∞ fin m  = ⊥
∞     <∞ ∞      = ⊥

_<∞?_ : Decidable _<∞_
fin n <∞? fin m = n Data.Nat.<? m
fin n <∞? ∞ = true because (ofʸ tt)
∞ <∞? fin m = false because ofⁿ id
∞ <∞? ∞ = false because ofⁿ id

_<∞b_ : ℕ∞ → ℕ∞ → Bool
n <∞b m = does (m <∞? n)

<∞-irrel : Relation.Binary.Definitions.Irrelevant _<∞_
<∞-irrel {fin x} {fin y} = Data.Nat.Properties.≤-irrelevant
<∞-irrel {fin x} {∞} p q = refl
<∞-irrel {∞} {fin y} ()
<∞-irrel {∞} {∞} ()
--------------------------------------------------------------------------------
-- Tools for converting between cardinalities and sets.
--------------------------------------------------------------------------------

-- Map a cardinality in Bigℕ to the prefix of the natural numbers
-- with that cardinality.
cardToSet : ℕ∞ → Set
cardToSet (fin 0) = ⊥
cardToSet (fin (suc n)) = Fin (suc n) -- Fin 0 cannot be constructed!
cardToSet ∞ = ℕ

infix 50 ^_
^_ : ℕ∞ → Set
^ c = cardToSet c

 
-- Get the default < relation on a prefix of ℕ, or on ℕ.
cardTo< : {n : ℕ∞} → Rel (cardToSet n) 0ℓ
cardTo< {fin 0} ()
cardTo< {fin (suc n)} = Data.Fin._<_
cardTo< {∞} = Data.Nat._<_

cardTo<Trans
    : {n : ℕ∞}
    → Transitive (cardTo< {n})
cardTo<Trans {fin (ℕ.suc n)} = Data.Fin.Properties.<-trans
cardTo<Trans {∞} = Data.Nat.Properties.<-trans

-- If m ≡ n or m < n, and n < k, then always m < k as well.
leqSmallerTrans
    : {c : ℕ∞}
    → {m n k : cardToSet c}
    → (m ≡ n ⊎ cardTo< m n)
    → cardTo< n k
    → cardTo< m k
leqSmallerTrans {_} {m} {n} {k} (inj₁ m≡n) n<k = 
    subst (λ x → cardTo< x k) (sym m≡n) n<k
leqSmallerTrans {fin (ℕ.suc x)} {m} {n} {k} (inj₂ m<n) n<k = 
    let m≤Sm : (toℕ m) Data.Nat.≤ ℕ.suc (toℕ m)
        m≤Sm = Data.Nat.Properties.n≤1+n (toℕ m)
    in
    let Sm≤Sn : ℕ.suc (toℕ m) Data.Nat.≤ ℕ.suc (toℕ n)
        Sm≤Sn = s≤s (Data.Nat.Properties.≤-trans m≤Sm m<n)
    in
    Data.Nat.Properties.≤-trans Sm≤Sn n<k
leqSmallerTrans {∞} {m} {n} {k} (inj₂ m<n) n<k =
    Data.Nat.Properties.<-trans m<n n<k

-- Elements of sets of any allowed cardinality can be injected into ℕ,
-- since that is the greatest cardinality we allow.
cardToℕ
    : {c : ℕ∞}
    → cardToSet c
    → ℕ
cardToℕ {∞} n = n
cardToℕ {fin (suc c)} n = toℕ n

cardToℕ-injective
    : {c : ℕ∞}
    → {n m : cardToSet c}
    → cardToℕ n ≡ cardToℕ m
    → n ≡ m
cardToℕ-injective {fin (suc c)} {n} {m} H = Data.Fin.Properties.toℕ-injective H
cardToℕ-injective {∞} {n} {m} refl = refl
    

cardTo<Dec
    : {c : ℕ∞}
    → Decidable (cardTo< {c})
cardTo<Dec {fin (ℕ.suc n)} = Data.Fin.Properties._<?_ 
cardTo<Dec {∞} = Data.Nat.Properties._<?_ 

--#TODO: move this to a file with general lemmas?
n≢m→toℕ[n]≢toℕ[m]
    : {k : ℕ}
    → {n m : Fin k}
    → n ≢ m
    → toℕ n ≢ toℕ m
n≢m→toℕ[n]≢toℕ[m] {suc k} {n} {m} n≢m toℕ[n]≡toℕ[m] = 
    let n≡m = toℕ-injective toℕ[n]≡toℕ[m] in
    ⊥-elim (n≢m n≡m)

n≮m→n≢m→m<n
    : {c : ℕ∞}
    → {n m : cardToSet c}
    → ¬ (cardTo< n m)
    → n ≢ m
    → cardTo< m n
n≮m→n≢m→m<n {fin (suc x)} {n} {m} n≮m n≢m = 
    let m≤n = Data.Nat.Properties.≮⇒≥ n≮m in
    -- Note: sym n≢m gives an inequality in a finite set,
    -- but we need an inequality in ℕ.
    let n≢m = n≢m→toℕ[n]≢toℕ[m] (n≢m) in
    Data.Nat.Properties.≤∧≢⇒< m≤n (≢-sym n≢m)
n≮m→n≢m→m<n {∞} {n} {m} n≮m n≢m =
    let m≤n = Data.Nat.Properties.≮⇒≥ n≮m in
    Data.Nat.Properties.≤∧≢⇒< m≤n (≢-sym n≢m)


-- Get the default ≤ relation on a prefix of ℕ, or on ℕ.
cardTo≤ : {n : ℕ∞} → Rel (cardToSet n) 0ℓ
cardTo≤ {fin 0} ()
cardTo≤ {fin (suc n)} = Data.Fin._≤_
cardTo≤ {∞} = Data.Nat._≤_


-- Given n ≤ m, we know that either n ≡ m OR n < m.
card≤to⊎
    : {c : ℕ∞}
    → {n m : cardToSet c}
    → cardTo≤ {c} n m
    → (n ≡ m) ⊎ (cardTo< n m)
card≤to⊎ {∞} {n} {m} n≤m =
    Data.Sum.swap (Data.Nat.Properties.m<1+n⇒m<n∨m≡n (s≤s n≤m))
card≤to⊎ {fin (suc c)} {n} {m} n≤m =
    makeFin (Data.Sum.swap (Data.Nat.Properties.m<1+n⇒m<n∨m≡n (s≤s n≤m)))
        where
            -- m<1+n⇒m<n∨m≡n proves the property for the images under the
            -- embedding from Fin (1+c) into ℕ.
            -- `makeFin` reflects it back to Fin (1+c).
            makeFin 
                : (toℕ n ≡ toℕ m) ⊎ (toℕ n Data.Nat.< toℕ m) 
                → (n ≡ m)  ⊎ (cardTo< n m) 
            makeFin (inj₁ Tn≡Tm) = inj₁ (toℕ-injective Tn≡Tm)
            makeFin (inj₂ Tn<Tm) = inj₂ Tn<Tm

-- Get the zero element of a set of one cardinality greater.
-- Only defined for `suc∞ n` since things with cardinality zero have
-- no elements.
cardToZero : (n : ℕ∞) → cardToSet (suc∞ n) 
cardToZero (fin n) = Data.Fin.zero
cardToZero ∞ = Data.Nat.zero


cardToSuc : {n : ℕ∞} → (m : cardToSet n) → cardToSet (suc∞ n) 
cardToSuc {fin 0} ()
cardToSuc {fin (suc n)} m = Data.Fin.suc m
cardToSuc {∞} m = Data.Nat.suc m

-- Return one lower number if it exists, but return 0 as predecessor of 0.
cardToPred : {n : ℕ∞} → (m : cardToSet n) → cardToSet n
cardToPred {fin 0} ()
cardToPred {fin (suc n)} zero = zero
cardToPred {fin (suc n)} (suc m) = inject₁ m
cardToPred {∞} zero = zero
cardToPred {∞} (suc m) = m


-- Compute successor, but if input is already the max,
-- then return the max.
clipSuc : {n : ℕ} → Fin n → Fin n
clipSuc {suc n} m with n Data.Nat.≟ toℕ m
... | yes _ = m
... | no p = let q = negTransport p (lemma {n} {m}) in
    lower₁ (suc m) q
    where
        lemma : {n : ℕ} {m : Fin (suc n)} 
              → (suc n ≡ toℕ ( suc m)) 
              → (n ≡ toℕ m)
        lemma {n} {m} r = Data.Nat.Properties.suc-injective r
        negTransport : {A B : Set} → ¬ B → (A → B) → ¬ A
        negTransport {A} {B} ¬B f a = ⊥-elim (¬B (f a))

-- Return one greater element if it exists, return the maximum if the set is
-- finite and the input is the maximum element.
cardToClipSuc : {n : ℕ∞} → (m : cardToSet n) → cardToSet n
cardToClipSuc {fin 0} ()
cardToClipSuc {fin (suc n)} m = clipSuc m
cardToClipSuc {∞} m = suc m

-- If `cardToSet c` is inhabited, then c cannot be zero.
elToNonempty
    : {c : ℕ∞}
    → cardToSet c
    → fin ℕ.zero <∞ c
elToNonempty {fin (ℕ.suc c)} i = s≤s z≤n
elToNonempty {∞} i = tt

-- If x ∈ cardToSet c then x is smaller than c (as elements of ℕ∞).
smallerThanCard
    : {c : ℕ∞}
    → (x : cardToSet c)
    → fin (cardToℕ x) <∞ c
smallerThanCard {fin (suc c)} x = toℕ<n {n = ℕ.suc c} x
smallerThanCard {∞} x = tt

-- Compare a natural number for equality n to a number m in (cardToSet c).
ℕequalsCardToSetElem : {c : ℕ∞} → ℕ → (m : cardToSet c) → Set
ℕequalsCardToSetElem {fin (suc c)} n m  = (toℕ m) ≡ n
ℕequalsCardToSetElem {∞} n m = n ≡ m

IsNotMax
    : {c : ℕ∞}
    → (m : cardToSet c)
    → Set
IsNotMax {fin zero} ()
IsNotMax {fin (suc n)} m = m Data.Fin.< (fromℕ n)
    --^ The largest element of fin (1 + n) is fromℕ n.
IsNotMax {∞} n = ⊤ 
    --^ Trivial: there is no maximal natural number.

-- If a bigger element than n exists in a finite set,
-- then n is not the maximum element of the set.
biggerToIsNotMax
    : {c : ℕ∞}
    → {n m : cardToSet c}
    → cardTo< n m
    → IsNotMax n
biggerToIsNotMax {fin (suc c)} {n} {m} n<m = 
    let Sm≤Sc : ℕ.suc (toℕ m) Data.Nat.≤ ℕ.suc c
        Sm≤Sc = toℕ<n m
    in
    let
        m≤c : toℕ m Data.Nat.≤ c
        m≤c = s≤s⁻¹ Sm≤Sc
    in
    let
        c≡TFc : c ≡ toℕ (fromℕ c)
        c≡TFc = sym (toℕ-fromℕ c)
    in
    let
        m≤TFc : toℕ m Data.Nat.≤ (toℕ (fromℕ c))
        m≤TFc = subst (λ x → toℕ m Data.Nat.≤ x) c≡TFc m≤c
    in
    Data.Nat.Properties.≤-trans n<m m≤TFc
biggerToIsNotMax {∞} {n} {m} n<m = tt


IsNotMax-irrel
    : {c : ℕ∞}
    → (m : cardToSet c)
    → Relation.Nullary.Irrelevant (IsNotMax m)
IsNotMax-irrel {fin (suc c)} m = Data.Fin.Properties.<-irrelevant 
-- Last case is NOT Data.Nat.Properties.<-irrelevant since
-- `IsNotMax m` for `m ∈ ℕ` (cardinality ∞) is defined as ⊤.
IsNotMax-irrel {∞} m = ⊤-irrelevant

-- Compute the successor while staying in the set of the same cardinality.
-- Of course, this is only possible if the input number 
-- is not the max of a finite set.
endoSuc
    : {c : ℕ∞}
    → {n : cardToSet c}
    → (h : IsNotMax n)
    → cardToSet c
endoSuc {fin (suc c)} {n} h = 
    let sucn = Fin.suc n in
    let meh = toℕ-fromℕ c in
    let n<c = subst (λ x → suc (toℕ n) Data.Nat.≤ x) meh h in
    let Sn<Sc = s≤s n<c in
    lower {2+ c} {suc c} sucn Sn<Sc
endoSuc {∞} {n} h = ℕ.suc n

endoSucUnique
    : {c : ℕ∞}
    → {n : cardToSet c}
    → (h₁ h₂ : IsNotMax n)
    → (endoSuc h₁ ≡ endoSuc h₂)
endoSucUnique {fin (suc c)} {n} h₁ h₂ = refl
endoSucUnique {∞} {n} h₁ h₂ = refl

-- The successors of two equal numbers are also equal.
endoSucPresvEquality
    : {c : ℕ∞}
    → {a b : cardToSet c}
    → (a ≡ b)
    → (h : IsNotMax a)
    → (k : IsNotMax b)
    → endoSuc h ≡ endoSuc k
endoSucPresvEquality {fin ℕ.zero} {()}
endoSucPresvEquality {∞} {a} {b} refl tt tt = refl
endoSucPresvEquality {fin (ℕ.suc c)} {a} {a} refl h k = 
    -- Path induction (assuming refl : a ≡ a) allows to equate 
    -- h and k, because they are now both of the same type `IsNotMax a`:
    let h≡k : h ≡ k
        h≡k = IsNotMax-irrel a h k
    in
    cong endoSuc h≡k


-- This lemma's primary purpose is to prove
-- the lemma endoSucProjToNatSuc.
endoSucLemma
    : {c : ℕ}
    → (n : cardToSet (fin (ℕ.suc c)))
    → (h : IsNotMax n)
    → toℕ (endoSuc (s≤s h)) ≡ ℕ.suc (toℕ (endoSuc h))
endoSucLemma {suc c} n h = refl

-- When working in ℕ (i.e., if the cardinality is ∞)
-- then endoSuc is just ℕ.suc.
endoSucNatSuc
    : {n : cardToSet ∞}
    → (h : IsNotMax n)
    → endoSuc {∞} {n} h ≡ ℕ.suc n
endoSucNatSuc {n} h = refl

-- When working in Fin (suc c) then endoSuc 'is' Fin.suc.
-- We only need to include an additional `inject₁` to make things well-typed
-- (since n and Fin.suc n do not have the same type).
endoSucFinSuc
    : {c : ℕ}
    → (n : Fin c)
    → (h : IsNotMax (inject₁ n))
    → endoSuc {fin (ℕ.suc c)} {inject₁ n} h ≡ Fin.suc n
endoSucFinSuc {c} zero (s≤s z≤n) = refl
endoSucFinSuc {ℕ.suc c} (Fin.suc n) (s≤s h) = 
    let rec : endoSuc h ≡ Fin.suc n
        rec = endoSucFinSuc {c} n h
    in
    let H₁ : toℕ (endoSuc (s≤s h)) ≡ toℕ (Fin.suc (endoSuc h))
        H₁ = endoSucLemma (inject₁ n) h
    in
    let H₂ : endoSuc (s≤s h) ≡ Fin.suc (endoSuc h)
        H₂ = Data.Fin.Properties.toℕ-injective H₁
    in
    trans H₂ (cong Fin.suc rec)

endoSucBigger
    : {c : ℕ∞}
    → {n : cardToSet c}
    → (h : IsNotMax n)
    → cardTo< n (endoSuc h)
endoSucBigger {fin (2+ c)} {zero} (s≤s z≤n) = s≤s z≤n
endoSucBigger {fin (suc c)} {suc n} h = 
    -- In earlier attempts I used `h` instead of `h'`,
    -- but that one has type `toℕ (suc n) < (toℕ (fromℕ c))`.
    -- Then Agda complained that the term I produced
    -- (`s≤s STn≤STLn`) was wrong
    -- because `toℕ (fromℕ c) != c`. 
    -- This was confusing since `c` does not appear in the type of STn≤STLn.
    -- The problem is that `toℕ (lower (suc n) h) : Fin (toℕ (fromℕ c))`.
    -- Replacing all instances of `h` by `h'` in the proof solved it.
    let h' : toℕ (suc n) Data.Nat.< c
        h' = subst (λ x → toℕ (suc n) Data.Nat.< x) (toℕ-fromℕ c) h
    in
    let n≤n : toℕ n Data.Nat.≤ toℕ n
        n≤n = Data.Nat.Properties.≤-refl
    in
    let STn≤STn : suc (toℕ n) Data.Nat.≤ suc (toℕ n)
        STn≤STn = s≤s n≤n 
    in
    let STn≤TLSn : suc (toℕ n) Data.Nat.≤ toℕ (lower (suc n) h')
        STn≤TLSn = subst (λ x → suc (toℕ n) Data.Nat.≤ x) 
                         (sym (toℕ-lower (suc n) h')) 
                         STn≤STn
    in
    s≤s (subst (λ x → suc (toℕ n) Data.Nat.≤ x) refl STn≤TLSn )
endoSucBigger {∞} {zero} tt = s≤s z≤n
endoSucBigger {∞} {suc n} tt = s≤s (s≤s Data.Nat.Properties.≤-refl)

-- Computing the successor of a non-max element n in a finite set
-- and injecting into ℕ is the same as injecting n first and using ℕ.suc.
endoSucInjToNatSuc
    : {c : ℕ}
    → {n : cardToSet (fin (ℕ.suc c))}
    → (h : IsNotMax n)
    → toℕ (endoSuc h) ≡ ℕ.suc (toℕ n)
endoSucInjToNatSuc {suc c} {zero} (s≤s z≤n) = refl
endoSucInjToNatSuc {suc c} {suc n} (s≤s h) = 
    let H = endoSucLemma {c} n h in
    let rec = endoSucInjToNatSuc {c} {n} h in
    let rec' = cong ℕ.suc rec in
    trans H rec'

-- cardToPrec is a section of the successor function `ℕ.suc ∘ toℕ`,
-- but only on numbers that are the successor of another.
sucpredsuc≡suc
    : {c : ℕ} 
    → (n : Fin c) --^ Same as `cardToSet c` if `c > 0`.
    → ℕ.suc (toℕ (cardToPred {fin (ℕ.suc c)} (Fin.suc n))) ≡ toℕ (Fin.suc n)
sucpredsuc≡suc {c} n = 
    let sn≡sn = refl {x = toℕ (Fin.suc n)} in
    let P = (λ x → x ≡ toℕ (Fin.suc n)) in
    subst P (sym (toℕ-inject₁ (Fin.suc n))) sn≡sn

-- This is FC-g in my notes.
j<i<Sj-impossible
    : {c : ℕ∞}
    → {i j : cardToSet c}
    → {h : IsNotMax j}
    → cardTo< i (endoSuc h) 
    → cardTo< j i
    → ⊥
j<i<Sj-impossible {fin (ℕ.suc c)} {i} {j} {h} i<Sj j<i =
    let SSj≤Si = s≤s j<i in
    let SSj≤Sj = Data.Nat.Properties.≤-trans SSj≤Si i<Sj in
    -- Need to tell Agda that toℕ (endoSuc h) = ℕ.suc (toN j).
    let H = endoSucInjToNatSuc {c} h in
    let SSj≤Sj' = subst (λ x → 2+ (toℕ j) Data.Nat.≤ x) H SSj≤Sj in
    -- Above is almost correct, but only an ℕ.suc too much on both sides.
    let K = s≤s⁻¹ SSj≤Sj' in
    1+n≰n {toℕ j} K
j<i<Sj-impossible {∞} {i} {j} {h} i<Sj j<i = 
    let SSj≤Si = s≤s j<i in
    let SSj≤Sj = Data.Nat.Properties.≤-trans SSj≤Si i<Sj in
    1+n≰n SSj≤Sj

<And≡Impossible
    : {c : ℕ∞}
    → {n m : cardToSet c}
    → cardTo< n m
    → n ≡ m
    → ⊥
<And≡Impossible {∞} {n} {m} n<m n≡m = Data.Nat.Properties.<⇒≢ n<m n≡m
<And≡Impossible {fin (ℕ.suc c)} {n} {m} n<m n≡m = 
    Data.Nat.Properties.<⇒≢ n<m (cong toℕ n≡m)
    
-- A number that is the predecessor of another number is never the maximum
-- in a finite set.
aPredecIsNotMax 
    : {c : ℕ∞}
    → {n : cardToSet c}
    → (cardTo< (cardToPred n) n)
    --^ This expresses that 0<n, in a convenient way!
    → IsNotMax (cardToPred n)
-- To show, by def of IsNotMax:
--  (cardToPred (Fin.suc n)) Data.Fin.< (fromℕ c)
--  I.e., suc n ≤ c. Up to some type conversions.
aPredecIsNotMax {fin (ℕ.suc c)} {Fin.suc n} (s≤s pn<n) =
    let sn≤c' = toℕ≤pred[n] {ℕ.suc c} (Fin.suc n) in
    let P = λ x → toℕ (Fin.suc n) Data.Nat.≤ x in
    let sn≤c = subst P (sym(toℕ-fromℕ c)) sn≤c' in
    --^ (suc n) : Fin (suc c) so (suc n) ≤ c.
    -- This actually already expresses that `suc n ≤ c`,
    -- but we need help Agda telling that the type conversions work out.
    let spsn≡sn = sym(sucpredsuc≡suc n) in
    subst (λ x → x Data.Nat.≤ toℕ (fromℕ c)) spsn≡sn sn≤c 
aPredecIsNotMax {∞} {n} pn<n = tt

-- If m is not the maximum element in a set of cardinality n+1
-- then it also exists in a set of cardinality n.
cardLower : {n : ℕ∞} → {m : cardToSet (suc∞ n)} → (IsNotMax m) → cardToSet n
cardLower {fin (suc n)} {m} notMax = 
    coe h (Data.Fin.lower m notMax)
    where
        h : Fin (toℕ (fromℕ ( ℕ.suc n))) ≡ Fin (ℕ.suc n)
        h = cong (λ X → Fin X) (toℕ-fromℕ (ℕ.suc n))
        -- Coe is taken from the book PROGAM=PROOF.
        coe : {A B : Set} → A ≡ B → A → B
        coe p x = subst (λ A → A) p x
cardLower {∞} {m} notMax = m
    --^ ℕ-1 is still ℕ.

-- Inject the elements of cardinality n into the set of cardinality n+1.
cardInject : {n : ℕ∞} → (m : cardToSet n) → cardToSet (suc∞ n)
cardInject {fin (suc n)} m = inject₁ m
cardInject {∞} m = m

cardFrom<∞
    : {c : ℕ∞}
    → {m : ℕ}
    → (fin m <∞ c)
    →  Σ[ m' ∈ cardToSet c ](cardToℕ m' ≡ m)
cardFrom<∞ {fin (suc c)} {m} m<c = ( fromℕ< m<c , toℕ-fromℕ< m<c)
cardFrom<∞ {∞} {m} m<c = (m , refl)

-- Equality is decidable for sets of all cardinalities.
cardToDecidableEq
    : (c : ℕ∞)
    → DecidableEquality (cardToSet c)
cardToDecidableEq (fin (suc c)) = Data.Fin._≟_
cardToDecidableEq ∞ = Data.Nat._≟_
 
--------------------------------------------------------------------------------
-- Inhabitedness and zero elements
--
-- Personal remark: be careful to pattern match the proof of `fin ℕ.zero <∞ n`
-- carefully all the way down to a canonical form,
-- otherwise Agda can't normalise nonzeroCardToZeroElem.
-- Also be careful not to match it with something like `z<n`,
-- since this is not an existing constuctor of `<` (`<` is defined via `≤`!)
-- and instead Agda creates a variable with that name...
-- ... and leaves me confused why things don't normalise correctly...
--------------------------------------------------------------------------------

-- Get the zero element of a set with cardinality greater than zero.
-- The advantage of using proofs of the form `(fin ℕ.zero <∞ n)`
-- instead of a witness `cardToSet n` (as in cardInhToZero) is that
-- there is now only a unique proof of inhabitness.
nonzeroCardToZeroElem : {n : ℕ∞} → (fin ℕ.zero <∞ n) → cardToSet n
nonzeroCardToZeroElem {fin zero} ()
nonzeroCardToZeroElem {fin (suc n)} (s≤s z≤n) = Data.Fin.zero
nonzeroCardToZeroElem {∞} _ = Data.Nat.zero

-- In case of sets of finite cardinality,
-- the output of `nonzeroCardToZeroElem` projects to 0 ∈ ℕ under toℕ.
zeroElemToNatZero
    : {c : ℕ}
    → (h : fin ℕ.zero <∞ (fin (ℕ.suc c)))
    → toℕ (nonzeroCardToZeroElem h) ≡ ℕ.zero
zeroElemToNatZero {c} (s≤s z≤n) = refl

nothingIs<0
    : {c : ℕ∞}
    → (n : cardToSet c)
    → (h : fin ℕ.zero <∞ c)
    → ¬ (cardTo< n (nonzeroCardToZeroElem h))
nothingIs<0 {fin (ℕ.suc c)} n h n<0 = 
    let nonzeroh≡0 = zeroElemToNatZero {c} h in
    let n<0' = subst (λ x → ℕ.suc (toℕ n) Data.Nat.≤ x) nonzeroh≡0 n<0 in
    n≮0 n<0'
nothingIs<0 {∞} n h n<0 = n≮0 n<0


-- If a cardinality is inhabited, then it is not the zero cardinality.
inhToNonzero
    : {n : ℕ∞}
    → (i : cardToSet n)
    → fin ℕ.zero <∞ n
inhToNonzero {fin zero} ()
inhToNonzero {fin (suc n)} _ = z<s 
inhToNonzero {∞} _ = tt

-- Get the zero element of a set of arbitrary cardinality
-- (and not a one-greater cardinality, like `cardToZero` returns),
-- provided you can give a witness it is not the empty set.
cardInhToZero : {n : ℕ∞} → cardToSet n → cardToSet n
cardInhToZero {fin (ℕ.suc n)} m = Fin.zero
cardInhToZero {∞} _ = Data.Nat.zero
-- This alternative implementation is homotopic to the current implementation.
--cardInhToZero {n} i = nonzeroCardToZeroElem (inhToNonzero {n} i)

cardTo0<1
    : {n : ℕ∞} 
    → (m : cardToSet n) 
    → cardTo< (cardInject (cardInhToZero m)) (cardToClipSuc (cardToZero n))
cardTo0<1 {fin 0} ()
cardTo0<1 {fin (suc n)} m = z<s
cardTo0<1 {∞} m = z<s

cardTo0<1'
    : {n : ℕ∞} 
    → (0<n : fin ℕ.zero <∞ n)
    → cardTo< (cardInject (nonzeroCardToZeroElem 0<n)) 
        (cardToClipSuc (cardToZero n))
cardTo0<1' {fin 0} ()
cardTo0<1' {fin (suc n)} (s≤s z≤n) = 
    let toNinjZero = nonzeroCardToZeroElem {fin (suc n)} (s≤s z≤n) in
    let toNZero = sym (toℕ-inject₁ toNinjZero) in 
    subst (λ x → suc x Data.Nat.≤ suc zero) toNZero (s≤s z≤n)
cardTo0<1' {∞} _ = z<s

thereIsOneZero 
    : {n : ℕ∞}
    → (i : cardToSet n)
    → (0<n : fin ℕ.zero <∞ n)
    → (cardInhToZero i ≡ nonzeroCardToZeroElem 0<n)
thereIsOneZero {fin zero} ()
thereIsOneZero {fin (suc n)} i (z<s) = refl
thereIsOneZero {∞} i 0<n = refl

thereIsOneZero'
    : {n : ℕ∞}
    → (h h' : fin ℕ.zero <∞ n)
    → nonzeroCardToZeroElem h ≡ nonzeroCardToZeroElem h'
thereIsOneZero' {fin (suc n)} (s≤s z≤n) (s≤s z≤n) = refl
thereIsOneZero' {∞} h h' = refl

sucZeroIsOneInℕ
    : (c : ℕ∞)
    → (ℕ.suc $ cardToℕ (cardToZero c)) ≡ 1
sucZeroIsOneInℕ (fin c) = refl
sucZeroIsOneInℕ ∞ = refl

--------------------------------------------------------------------------------
-- Unimportant/unused lemmas
--------------------------------------------------------------------------------
ℕSucCardToSucComm 
    : {n : ℕ}
    → (i : cardToSet (fin n)) 
    → toℕ (cardToSuc i) ≡ ℕ.suc (toℕ (cardInject i))
ℕSucCardToSucComm {ℕ.suc n} i = begin
      toℕ (cardToSuc i) 
        ≡⟨ refl ⟩
      ℕ.suc (toℕ i) 
        ≡⟨ cong ℕ.suc (sym (toℕ-inject₁ i)) ⟩
      ℕ.suc (toℕ (cardInject i))
      ∎

-- If j < (suc i) then j ≤ i.
card<s→≤ 
    : {n : ℕ∞} 
    → {i j : cardToSet n} 
    → (cardTo< (cardInject j) (cardToSuc i) )
    --^ Note: this < lives in `cardToSet (suc∞ n)`.
    → (cardTo≤ j i)
    --^ Note: this ≤ lives in `cardToSet n`.
card<s→≤ {fin (ℕ.suc n)} {i} {j} j<si = 
    let h = ℕSucCardToSucComm i in
    let P = (λ x → ℕ.suc (toℕ (cardInject j)) Data.Nat.≤ x) in
    let sjℕ≤si = subst P h j<si in
    -- Let's first strip away the ℕ.suc from both sides.
    let jℕ≤i = ≤-pred sjℕ≤si in
    -- Next, strip away the toℕ ∘ inject₁ from both sides.
    --let j≤i = toℕ-cancel-≤ jℕ≤i in -- That doesn't help
    let hj = toℕ-inject₁ j in
    let hi = toℕ-inject₁ i in
    let j≤i' = subst (λ x → x Data.Nat.≤ (toℕ (inject₁ i))) hj jℕ≤i in
    let j≤i = subst (λ x → toℕ j Data.Nat.≤ x) hi j≤i' in
    j≤i
card<s→≤ {∞} {i} {j} i<j = ≤-pred i<j
