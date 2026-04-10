-- Module      : Eser.Monotone
-- Description : Basic definitions and properties of funs monotone on (ℕ, <).
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Most things could have been defined much more general,
-- e.g., for all total orders on any type,
-- but within Eser we only need it for ℕ → ℕ functions.
-- It is possible that all the results in here are in some abstract/generalised
-- form in the stdlib, but I haven't been able to find them.


open import Level
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary
open import Data.Product
open import Relation.Binary.Structures
open import Function
open import Relation.Binary.Reasoning.Syntax

open import Eser.Aux
open import Eser.Stdlib using (∸-suc)

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

module Eser.Monotone where

-- Functions f : ℕ → ℕ such that (m < n) ⇒ (f m < f n).
ℕ<Monotone : (ℕ → ℕ) → Set 
ℕ<Monotone = Monotonic₁ _<_ _<_

-- Functions injective on ℕ.
ℕInjective : (ℕ → ℕ) → Set
ℕInjective = Injective _≡_ _≡_

-- If m < n then there exist a nonzero k s.t. n ≡ k + m.
smallerToSum : {m n : ℕ} → m < n → Σ[ k ∈ ℕ ] n ≡ ℕ.suc k + m
smallerToSum {m} {n} m<n = 
    let k = n ∸ ℕ.suc m in
    let Sk+m≡n : ℕ.suc k + m ≡ n
        Sk+m≡n = 
            ≡begin 
                ℕ.suc k + m 
            ≡⟨⟩
                ℕ.suc (n ∸ ℕ.suc m) + m
            ≡⟨ cong (_+ m) (sym $ ∸-suc m<n)  ⟩
                (n ∸ m) + m
            ≡⟨ m∸n+n≡m (<⇒≤ m<n) ⟩
                n
            ≡∎
    in (k , sym Sk+m≡n)
    
-- If f n < f (ℕ.suc n) then we can inductively see that
-- f n < f (1 + n) < f (2 + n) < f (3 + n) < ... < f(ℕ.suc k + n)
piecewiseIncrImplMonoLemma
    : {f : ℕ → ℕ}
    → ((n : ℕ) → f n < f (ℕ.suc n))
    → ((n k : ℕ) → f n < f (ℕ.suc k + n))
piecewiseIncrImplMonoLemma {f} H n 0 = H n
piecewiseIncrImplMonoLemma {f} H n (ℕ.suc k) = 
    let fn<fSk+n = piecewiseIncrImplMonoLemma H n k
    in
    <-trans fn<fSk+n (H $ ℕ.suc k + n)

-- If f (suc n) > f n for all n, then that already implies that f is monotone.
piecewiseIncrImplMono
    : {f : ℕ → ℕ}
    → ((n : ℕ) → f n < f (ℕ.suc n))
    → ℕ<Monotone f
piecewiseIncrImplMono {f} H {m} {n} m<n = 
    let (k , n≡Sk+m) = smallerToSum m<n
    in
    let fm<fSk+m = piecewiseIncrImplMonoLemma H m k
    in
    subst (λ x → f m < f x) (sym n≡Sk+m) fm<fSk+m

a<b→fa≡fb→MonoF→⊥
    : {a b : ℕ}
    → {f : ℕ → ℕ}
    → ℕ<Monotone f
    → a < b
    → f a ≡ f b
    → ⊥
a<b→fa≡fb→MonoF→⊥ {a} {b} {f} mono a<b fa≡fb = <⇒≢ (mono a<b) fa≡fb

monotoneImplInjective
    : {f : ℕ → ℕ}
    → ℕ<Monotone f
    → ℕInjective f
monotoneImplInjective {f} mono {m} {n} fm≡fn with <-cmp m n
... | tri< m<n  _   _   = ⊥-elim $ a<b→fa≡fb→MonoF→⊥ mono m<n fm≡fn 
... | tri≈ _    m≡n _   = m≡n
... | tri> _    _   n<m = ⊥-elim $ a<b→fa≡fb→MonoF→⊥ mono n<m (sym fm≡fn)

-- If f : ℕ → ℕ is strictly increasing,
-- then it factorises most of ℕ into the intervals
-- [f 0 , f 1) [f 1 , f2) [f 2 , f 3) , ...
-- and any number w ≥ f 0 falls into exactly one such interval.
increasingImplIval
    : (f : ℕ → ℕ)
    → ℕ<Monotone f
    → (w : ℕ)
    → f 0 ≤ w
    → Σ[ i ∈ ℕ ]( f i ≤ w × w < f (ℕ.suc i))
increasingImplIval f mono 0 f0≤w =
    let f0≡0 : f 0 ≡ 0
        f0≡0 = n≤0⇒n≡0 (f0≤w)
    in
    let 0<f1 : 0 < f 1
        0<f1 = subst (λ x → x < f 1) f0≡0 (mono $ s≤s z≤n)
    in
    (0 , f0≤w , 0<f1)
-- Inductive case.
-- First case distinction on f 0 ≤ suc w.
--  If f0≡Sw then i ≔ 0 works.
--  If f0<Sw then also f0 ≤ w,
--      so we can make a recursive call giving an i s.t. f i ≤ w < f (suc i).
--      This also implies `suc w ≤ f (suc i)`.
--      Then the "i for suc w" is either i or suc i,
--      depending on whether `suc w ≤ f (suc i)` is `≡` or `<` respectively.
increasingImplIval f mono (suc w) f0≤Sw with (m≤n⇒m<n∨m≡n f0≤Sw) 
... | inj₂ f0≡Sw = (0 
                   , subst (λ x → f 0 ≤ x) f0≡Sw ≤-refl
                   , subst (λ x → x < f 1) f0≡Sw (mono $ s≤s z≤n))
... | inj₁ f0<Sw =
    let w≤Sw : w ≤ ℕ.suc w
        w≤Sw = n≤1+n w
    in
    let (i , fi≤w , w<fSi) = increasingImplIval f mono w (s≤s⁻¹ f0<Sw)
    in
    let Sw≤fSi : ℕ.suc w ≤ f (ℕ.suc i)
        Sw≤fSi = w<fSi -- By definition of `a < b ≗ suc a ≤ b`.
    in
    caseDistinction i fi≤w $ m≤n⇒m<n∨m≡n Sw≤fSi
    where
        caseDistinction 
            : (i : ℕ)
            → f i ≤ w
            → (ℕ.suc w < f (ℕ.suc i)) ⊎ (ℕ.suc w ≡ f (ℕ.suc i))
            →  Σ[ i ∈ ℕ ] (f i ≤ ℕ.suc w × ℕ.suc w < f (ℕ.suc i))
        caseDistinction i fi≤w (inj₁ Sw<fSi) = 
            (i , ≤-trans fi≤w (n≤1+n w) , Sw<fSi)
        caseDistinction i _ (inj₂ Sw≡fSi) = 
            (ℕ.suc i 
            , ≡→≤ (sym Sw≡fSi)
            , subst (λ x → x < (f $ ℕ.suc $ ℕ.suc i)) 
                    (sym Sw≡fSi) 
                    (mono $ n<1+n (ℕ.suc i))
            )

-- If w ∈ [a , b) and we know t ∈ P w and ¬ P i for all i ∈ (a , b)
-- then it must be that w ≡ a.
firstOfIval
    : {w a b : ℕ}
    → a ≤ w
    → w < b
    → (P : ℕ → Set)
    → ((ℓ : ℕ) → Between a b ℓ → ¬ P ℓ)
    → P w
    → w ≡ a
firstOfIval {w} {a} {b} a≤w w<b P H Pw with (m≤n⇒m<n∨m≡n a≤w)
... | inj₁ a<w = ⊥-elim (H w (a<w , w<b) Pw)
... | inj₂ a≡w = sym a≡w
