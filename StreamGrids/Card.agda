-- Module      : StreamGrids.Card
-- Description : Tools for working with sets of different cardinalities.
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

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
open import Data.Vec
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Relation.Nullary


module StreamGrids.Card where

--------------------------------------------------------------------------------
-- ℕ∞ is the type of cardinalities.
--------------------------------------------------------------------------------

-- Natural numbers extended with a top element '∞' (w.r.t. the '<' relation).
-- #TODO: check if this already exist in the standard library?
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

--------------------------------------------------------------------------------
-- Tools for convering between cardinalities and sets.
--------------------------------------------------------------------------------

-- Map a cardinality in Bigℕ to the prefix of the natural numbers
-- with that cardinality.
cardToSet : ℕ∞ → Set
cardToSet (fin 0) = ⊥
cardToSet (fin (suc n)) = Fin (suc n) -- Fin 0 cannot be constructed!
cardToSet ∞ = ℕ
 
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

-- Get the default ≤ relation on a prefix of ℕ, or on ℕ.
cardTo≤ : {n : ℕ∞} → Rel (cardToSet n) 0ℓ
cardTo≤ {fin 0} ()
cardTo≤ {fin (suc n)} = Data.Fin._≤_
cardTo≤ {∞} = Data.Nat._≤_

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
