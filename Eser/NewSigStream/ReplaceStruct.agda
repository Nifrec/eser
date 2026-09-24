-- Module      : Eser.NewSigStream.ReplaceStruct
-- Description : All term algebras over Signatures give rise to a ReplaceStruct.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Using the enumeration algorithm in NewSigStream for term algebras
-- of Signatures, we can show that each such term algebra has
-- the structure of a 'ReplaceStruct'.
--
-- #EXT: Currently only implemented for the non-trivial signatures
-- with at least one nullary and at least one multiary operation.
--------------------------------------------------------------------------------

open import Level hiding (suc)
open import Data.Bool using (Bool ; true) renaming (T to IsTrue)
open import Data.Nat
open import Data.Nat.Properties
--open ≤-Reasoning renaming (begin-equation to ≡begin)
open import Data.Sum hiding (reduce)
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
--open ≡-Reasoning -- renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Relation.Unary using (_⊆_)
open import Data.Vec
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.All as All hiding (_∷_ ; head ; tail)
--open import Data.Vec.Relation.Unary.All as All hiding (_∷_)
open import Data.Vec.Relation.Unary.Any as Any hiding (head ; tail)
--open import Data.Vec.Relation.Unary.All.Properties
open import Data.Fin using (Fin)
open import Function hiding (_↔_)

open import Eser.Logic using (≡true→T)
open import Eser.Card
open import Eser.Signature
open import Eser.Equivalences.Notation hiding (begin_ ; _∎)
--open import Eser.Equivalences.Properties
--open import Eser.Aux using (_≈_ ; ℓ<m<1+n→ℓ<n)
open import Eser.NewSigStream
open import Eser.Filters.ReplaceStructs
open import Eser.NatCoding


module Eser.NewSigStream.ReplaceStruct 
    (μ' : ℕ∞) 
    {ζ' : ℕ∞} 
    (S : Signature (suc∞ μ') (suc∞ ζ'))
    where

open WithMuZeta μ' ζ'
open InductiveCaseImpl μ' {ζ'} S
--μ : ℕ∞
--μ = suc∞ μ'
--ζ : ℕ∞
--ζ = suc∞ ζ'

--T : Set
--T = Term {μ} {ζ} S


-- Enumeration of the terms of S. 
-- Because we are assuming at least one nullary and at least one multiary
-- constructor, we know the RHS is ℕ and cannot be `Fin n`.
enum : T ≃ ℕ
--enum = subst (λ A → T ≃ A) (sigset-suc∞ μ' ζ') (sigenum {μ} S)
enum = inductiveCase μ' {ζ'} S

open EquivShorthands enum -- Imports φ as encoder and φ⁻¹ as decoder.

--------------------------------------------------------------------------------
-- Is-argument-of-relation defined on Terms (as ∈∈) and on their ℕ-codes (as ⊂).
--------------------------------------------------------------------------------

_∈∈_ : T → T → Set
t ∈∈ nullary c = ⊥
t ∈∈ multiary c v = t ∈ v

_≡T?_ : DecidableEquality T
_≡vT?_ : {n : ℕ} → DecidableEquality (Vec T n)

nullary-injective 
    : {c c' : ^ μ} 
    → nullary {μ} c ≡ nullary c' 
    → c ≡ c'
nullary-injective refl = refl

multiary-op-injective 
    : {c c' : ^ ζ} 
    → {v : Vec T (suc $ S c)}
    → {v' : Vec T (suc $ S c')}
    → multiary {μ} c v ≡ multiary c' v'
    → c ≡ c'
multiary-op-injective refl = refl

multiary-vec-injective 
    : {c : ^ ζ} 
    → {v v' : Vec T (suc $ S c)}
    → multiary {μ} c v ≡ multiary c v'
    → v ≡ v'
multiary-vec-injective refl = refl

nullary c ≡T? nullary c' = cases $ cardToDecidableEq μ c c'
    where
        cases : (Dec (c ≡ c')) → (Dec (nullary c ≡ nullary c'))
        cases (no c≢c') = no (λ eq → c≢c' $ nullary-injective eq)
        cases (yes c≡c') = yes $ cong nullary c≡c'
nullary c ≡T? multiary c' v'    = no (λ ())
multiary c v ≡T? nullary c'      = no (λ ())
multiary c v ≡T? multiary c' v'  = cases (cardToDecidableEq ζ c c')
    where
        cases 
            : (Dec (c ≡ c')) 
            → (Dec (multiary c v ≡ multiary c' v'))
        cases (no c≢c') = no (λ eq → c≢c' $ multiary-op-injective eq)
        -- The type `v ≡ v'` is only well-defined when v and v'
        -- have the same type, i.e., the same length,
        -- i.e., when c and c' have the same arity.
        -- So we first have to contract c to c' before we can check 
        -- whether v and v' are equal.
        cases (yes refl) with (v ≡vT? v')
        ... | yes v≡v' = yes (cong (multiary c) v≡v')
        ... | no v≢v' = no $ (λ eq → v≢v' $ multiary-vec-injective eq)
        

[] ≡vT? []             = yes refl
(t ∷ ts) ≡vT? (s ∷ ss) = cases (t ≡T? s) (ts ≡vT? ss)
    where
        cases : (Dec (t ≡ s)) → (Dec (ts ≡ ss)) → (Dec (t ∷ ts ≡ s ∷ ss))
        cases (no t≢s) (yes ts≡ss) = no (λ eq → t≢s $ cong head eq)
        cases (yes t≡s) (yes ts≡ss) = yes $ cong₂ (_∷_) t≡s ts≡ss
        cases (yes t≡s) (no ts≢ss)  = no (λ eq → ts≢ss $ cong tail eq)

_∈∈?_ : Relation.Binary.Definitions.Decidable _∈∈_
t ∈∈? nullary c = no λ { () }
t ∈∈? multiary c v = t ∈? v
    where 
        open import Data.Vec.Membership.DecPropositional {A = T} (_≡T?_)

_is-arg-of_ : ℕ → ℕ → Bool
x is-arg-of y = isYes $ (φ⁻¹ x) ∈∈? (φ⁻¹ y)

_⊂_ : ℕ → ℕ → Set
x ⊂ y = x is-arg-of y ≡ true

--------------------------------------------------------------------------------
-- ⊂-resp-< : the is-arg-of relation respects < on the encoding
--------------------------------------------------------------------------------

code-term-vec-membership
    : {t : T}
    → {n : ℕ}
    → {v : Vec T n}
    → t ∈ v
    → φ t ∈ (code-term-vec v)
code-term-vec-membership {t} {_} {t ∷ ss} (Any.here refl) = Any.here refl
code-term-vec-membership {t} {_} {s ∷ ss} (Any.there t∈ss) 
    = Any.there (code-term-vec-membership t∈ss)

arg-membership-lemma
    : {t : T}
    → {c : ^ ζ}
    → {v : Vec T (ar c)}
    → t ∈∈ multiary c v
    → φ t ∈ (code-term-vec v)
arg-membership-lemma {t} {_} {v} t∈∈s = code-term-vec-membership t∈∈s

arg-encode-lemma
    : {t s : T}
    → t ∈∈ s
    → φ t < φ s
arg-encode-lemma {t} {s@(multiary c v)} t∈∈s = 
    begin-strict
        φ t
    ≤⟨ H ⟩
        code-vec (code-term-vec v)
    ≤⟨ code-pair-lemma (code-vec (code-term-vec v)) c ⟩
        code-pair (c , code-vec (code-term-vec v))
    <⟨ code-sum-lemma (code-pair (c , code-vec (code-term-vec v))) ⟩
        code-sum (inj₂ $ code-pair (c , code-vec (code-term-vec v)))
    ≡⟨⟩
        code-term (multiary c v)
    ≡⟨⟩
        φ s 
    ∎
    where
        open ≤-Reasoning
        φt∈v' : φ t ∈ (code-term-vec v)
        φt∈v' = arg-membership-lemma t∈∈s

        H : φ t ≤ code-vec (code-term-vec v)
        H = All.lookup (code-vec-lemma (code-term-vec v)) φt∈v'

⊂-resp-<
    : (y x : ℕ)
    → x ⊂ y
    → x < y
⊂-resp-< y x x⊂y =
    begin-strict 
        x
    ≡⟨ sym $ φ∘φ⁻¹≈id x ⟩
        φ (φ⁻¹ x)
    <⟨ arg-encode-lemma t∈∈s ⟩
        φ (φ⁻¹ y)
    ≡⟨ φ∘φ⁻¹≈id y ⟩
        y
    ∎
    where
        open ≤-Reasoning
        t : T
        t = φ⁻¹ x
        s : T
        s = φ⁻¹ y
        t∈∈s : t ∈∈ s
        t∈∈s = toWitness $ ≡true→T x⊂y
    
    


sig-to-replacestruct : ReplaceStruct
sig-to-replacestruct = record 
    { _is-arg-of_ = _is-arg-of_
    ; ⊂-resp-< = ⊂-resp-< 
    ; replace = {! !} 
    ; replace-< = {! !} 
    ; keep = {! !} 
    ; nospawn = {! !} 
    ; comm = {! !} 
    ; noeff = {! !} 
    ; halfcut = {! !} 
    ; id-rep = {! !} 
    ; complete = {! !} 
    }
