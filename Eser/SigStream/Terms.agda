-- Module      : Eser.SigStream.Terms
-- Description : Two representations of terms in term algebra over a signature.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Two representations of the term of the term algebra over a signature.
--
-- (1) 𝐕𝐞𝐜𝐓𝐞𝐫𝐦
--  Terms represented by the index of the operation in the signature,
--  and for multiary operations, paired with a vector encoding their arguments,
--  whose length matches their arity.
--  The interpretation is as follows: Vec ℕ m gives the indices of the arguments
--  in an enumeration of all the terms. This interpretation is, of course, 
--  only useful when given an enumeration of all the terms,
--  such that the index assigned to a term is greater than the indices
--  assigned to its arguments.
--------------------------------------------------------------------------------

open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
-- We want the 'here' of _∈_ not of _[_]=_.
open import Data.Vec hiding (here ; there) 
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any
open import Data.List renaming (_∷_ to _∷L_) hiding (sum ; length)
open import Function hiding (_↔_)

open import Eser.Aux using (S[m∸Sn]≡m∸n)
open import Eser.Signature.Definitions
open import Eser.Card
open import Eser.Equivalences.Notation using (_≃_)
open import Eser.Equivalences.Properties using (mk≃')

module Eser.SigStream.Terms 
    {μ' ζ' : ℕ∞} 
    (S : Signature (suc∞ μ') (suc∞ ζ')) 
    where

μ = suc∞ μ'
ζ = suc∞ ζ'

ar : cardToSet ζ → ℕ
ar = arity {μ} {ζ} {S = S}

data NumTerms : Set where
    nt-nullary : cardToSet μ → NumTerms
    nt-multiary : (c : cardToSet ζ) → Vec ℕ (ar c) → NumTerms

NT = NumTerms

-- Open NumTerms: these don't take a vector of argument,
-- but arguments one by one. This is more convenient when doing
-- structural induction, since the termination checker does not
-- allow recursing on elements of a vector, but does allow recursing
-- on a single argument.
-- Index ℕ encodes the number of arguments a term still needs.
-- Arguments can only be given in order from 'left to right'.
data ONT : ℕ → Set where
    ont-nullary : cardToSet μ → ONT 0
    ont-multiary : (c : cardToSet ζ) → ONT (ar c)
    ont-app : {n : ℕ} → ONT (suc n) → ℕ → ONT n

IsMultiary : NumTerms → Set
IsMultiary (nt-nullary _) = ⊥
IsMultiary (nt-multiary _ _) = ⊤

OIsMultiary : {n : ℕ} → ONT n → Set
OIsMultiary (ont-nullary _) = ⊥
OIsMultiary (ont-multiary _) = ⊤
OIsMultiary (ont-app _ _) = ⊤

getArity
    : {t : NumTerms}
    → IsMultiary t
    → ℕ
getArity {nt-multiary c _} tt = ar c

getVector 
    : {t : NumTerms}
    → (mv : IsMultiary t)
    → Vec ℕ (getArity {t} mv)
getVector {nt-multiary _ t} tt = t

MakesArgsSmaller
    : (f : NumTerms → ℕ)
    → Set
MakesArgsSmaller f =
      (t : NumTerms)
    → (mv : IsMultiary t)
    → (i : ℕ)
    → (i ∈ (getVector {t} mv))
    → i < f t

--------------------------------------------------------------------------------
-- Conversion between vector-of-args and args-one-by-one encodings
--------------------------------------------------------------------------------

getOpIdx : {n : ℕ} → (t : ONT n) → {OIsMultiary t} → cardToSet ζ
getOpIdx {n} (ont-multiary c) = c
getOpIdx {n} (ont-app (ont-multiary c) _) = c
getOpIdx {n} (ont-app t@(ont-app _ _) _) = getOpIdx t

getOpIdx-lemma 
    : {n : ℕ} 
    → (t : ONT (suc n)) 
    → (a : ℕ)
    → {p : OIsMultiary t}
    → getOpIdx (ont-app t a) ≡ getOpIdx t {p}
getOpIdx-lemma {n} (ont-multiary c) a {p} = refl
getOpIdx-lemma {n} (ont-app t a') a {p} = refl

--ont-app-isMultiary
--    : {n : ℕ}
--    → (t : ONT (suc n))
--    → (a : ℕ)
--    → OIsMultiary (ont-app t a)
--ont-app-isMultiary (ont-multiary c) a = tt
--ont-app-isMultiary (ont-app t a') a = ont-app-isMultiary t a'

ont-app-isMultiary
    : {n : ℕ}
    → (t : ONT (suc n))
    → OIsMultiary t
ont-app-isMultiary (ont-multiary c) = tt
ont-app-isMultiary (ont-app t a) = tt

ont-idx-lemma
    : {n : ℕ} 
    → (t : ONT n) 
    → {p : OIsMultiary t} 
    → n ≤ (ar $ getOpIdx t {p})
ont-idx-lemma {n} (ont-multiary c) {p} = ≤-refl
ont-idx-lemma {n} (ont-app t a) {p} = ≤-trans (n≤1+n n) IH'
    where
        IH : suc n ≤ (ar $ getOpIdx t {ont-app-isMultiary t})
        IH = ont-idx-lemma {suc n} t        
        IH' : suc n ≤ (ar $ getOpIdx (ont-app t a))
        IH' = subst (λ x → suc n ≤ ar x) (sym $ getOpIdx-lemma t a) IH

getVec 
    : {n : ℕ} 
    → (t : ONT n) 
    → {p : OIsMultiary t} 
    → Vec ℕ ((ar $ getOpIdx t {p}) ∸ n)
getVec {n} (ont-multiary c) = subst (Vec ℕ) (sym $ n∸n≡0 $ ar c) []
getVec {n} (ont-app t a) = ans
    where
        p : OIsMultiary t
        p = ont-app-isMultiary t
        rec : Vec ℕ ((ar $ getOpIdx t {p}) ∸ suc n)
        rec = getVec t
        rec' : Vec ℕ (suc $ (ar $ getOpIdx t {p}) ∸ suc n)
        rec' = a ∷ (getVec t)
        m : ℕ
        m = ar $ getOpIdx t {p}
        m-eq : m ≡ (ar $ getOpIdx (ont-app t a))
        m-eq = sym $ cong ar $ getOpIdx-lemma t a
        ans : Vec ℕ ((ar $ getOpIdx (ont-app t a)) ∸ n)
        ans = subst (Vec ℕ) 
            (subst (λ x → suc (m ∸ suc n) ≡ x ∸ n) 
                m-eq (S[m∸Sn]≡m∸n {m} {n} $ ont-idx-lemma t)
            ) rec'

pile-args
    : {n : ℕ}
    → (t : ONT n)
    → Vec ℕ n
    → ONT 0
pile-args-rec
    : {n m : ℕ}
    → (t : ONT n)
    → m ≤ n
    → Vec ℕ m
    → ONT (n ∸ m)
pile-args {n} t v = subst ONT (n∸n≡0 n) $ pile-args-rec {n} {n} t (≤-refl) v

pile-args-rec {0} {0} t _ [] = t
pile-args-rec {suc n} {suc m} Sm≤Sn t (a ∷ as) = {! ont-app (pile-args-rec t as) a !}

k : ONT 0 → NT
k (ont-nullary c) = nt-nullary c
k t@(ont-app t' a) = nt-multiary (getOpIdx t) (getVec t)

w : NT → ONT 0
w (nt-nullary c) = ont-nullary c
w (nt-multiary c v) = pile-args (ont-multiary c) v
