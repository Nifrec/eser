-- Module      : Eser.Signature.NewSigStream
-- Description : New enumeration algorithm -- simplified implementation
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Simplified version of the new enumeration algorithm for term algebras of
-- Signatures.
--------------------------------------------------------------------------------
open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
--open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Data.Vec
open import Data.Vec.Functional -- Imports `Vector`, `toVec`, `fromVec` etc.
open import Data.Fin using (Fin)
open import Function hiding (_↔_)

open import Eser.Card
open import Eser.Signature
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties

module Eser.NewSigStream where

infix 50 ^_
^_ : ℕ∞ → Set
^ c = cardToSet c

-- sigcard μ ζ gives the cardinality of the term algebra
-- of a Signature μ ζ.
-- Note that this does not depend on the actual constructors,
-- only on the size of the sets of nullary/multiary constructors!
sigcard : ℕ∞ → ℕ∞ → ℕ∞
-- No nullary constructors => no terms at all.
sigcard (fin 0) _ = fin 0
-- Only nullary constructors.
sigcard μ (fin 0) = μ
-- At least 1 nullary & 1 multiary constructor => inf term algebra.
sigcard μ ζ = ∞

-- The set of the form `Fin n` xor `ℕ` to which the term algebra
-- of a Signature is equivalent.
sigset : ℕ∞ → ℕ∞ → Set
sigset μ ζ = ^ (sigcard μ ζ)

module _ {μ ζ : ℕ∞} (S : Signature μ ζ) where
    ar : ^ ζ → ℕ
    ar c = suc (S c)

    data Term : Set where
        nullary : ^ μ → Term
        multiary : (c : ^ ζ) → Vec Term (ar c) → Term

    -- Terms annotated with their height.
    -- Computing the height on a Term is problematic because the termination
    -- checker does not allow `map height v` on the vector v or arguments.
    -- And we want to use heights precisely to have a tool to recurse on the
    -- arguments! (So we cannot make such a tool in advance because circular...)
    data HTerm : ℕ → Set where
        h-nul : ^ μ → HTerm 0
        h-mul 
            : (c : ^ ζ) 
            → (v : Vec (Σ[ h ∈ ℕ ] HTerm h) (ar c)) 
            → HTerm (suc $ max $ map proj₁ v)

pattern
    finsuc x = fin (suc x)

emptyCaseLemma 
    : {ζ : ℕ∞}
    → (S : Signature (fin 0) ζ)
    → (t : Term {fin 0} S)
    → ⊥
emptyCaseLemma {ζ} S (multiary c (x ∷ v)) = emptyCaseLemma S x

emptyCase
    : {ζ : ℕ∞}
    → (S : Signature (fin 0) ζ) 
    → Term {fin 0} S ≃ ⊥
emptyCase S = mk≃' f f⁻¹ invˡ invʳ
    where
    f : Term S → ⊥
    f (nullary ())
    f t@(multiary _ _) = emptyCaseLemma S t
    f⁻¹ : ⊥ → Term S
    f⁻¹ ()
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {()}
    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {_} {()}


noMultiaryCase 
    : (μ : ℕ∞) 
    → (S : Signature μ (fin 0)) 
    → Term {μ} {fin 0} S ≃ ^ μ
noMultiaryCase μ S = equiv
    where
        equiv : Term {μ} {fin 0} S ≃ ^ μ
        equiv = mk≃' f f⁻¹ invˡ invʳ
            where
                f : Term S → ^ μ
                f (nullary c) = c
                f⁻¹ : ^ μ → Term S
                f⁻¹ = nullary
                invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
                invˡ {c} {nullary c} refl = refl
                invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
                invʳ {nullary c} {c} refl = refl

inductiveCase
    : (μ' : ℕ∞)
    → {ζ' : ℕ∞}
    → (S : Signature (suc∞ μ') (suc∞ ζ'))
    → Term {suc∞ μ'} {suc∞ ζ'} S ≃ ℕ
inductiveCase μ' {ζ'} S = 
    begin 
        Term S
    ≃⟨ {! nulmul lemma !} ⟩
        FTerm
    --≃⟨ {! nulmul lemma !} ⟩
    --    NulTerm S ⊎ MulTerm S
    ≃⟨ {! sum lemma !} ⟩
        (^ μ ⊎ ℕ)
    ≃⟨ {! merge lemma !} ⟩
        ℕ
    ∎
    where
        --MulTerm : Set
        --MulTerm = Σ[ c ∈ ^ ζ ] Vec (Term S) (ar c)
        μ : ℕ∞
        μ = suc∞ μ'
        ζ : ℕ∞
        ζ = suc∞ ζ'


        -- Same as Term S, but now the arguments are given
        -- as a function (Vector A n  ≔ (Fin n → A)),
        -- for which the termination checker allows to recurse on its elements
        -- (for a Vec, this is not allowed).
        data FTerm : Set where
            f-nul : ^ μ → FTerm
            f-mul : (c : ^ ζ) → Vector FTerm (ar {μ} S c) → FTerm

        toFun : Term S → FTerm
        toFunFuelled : {b : ℕ} → (t : Term S) → (height t < b) → FTerm
        toTermFuelled {suc b} t p = ?

        toFun (nullary c) = f-nul c
        --toFun (multiary c v) = f-mul c (Data.Vec.Functional.map toFun $ fromVec v)
        toFun (multiary c v) = f-mul c {! g !}
            where
                -- # TODO: this doesn't sat the termination checker.
                -- Possible solutions:
                -- * Well-founded induction on subterm relation
                --  (but then toFun becomes black box)
                -- * Add intermediate "weightedTerms", and use fuel,
                --  weight of a term is 1 + sum-of-child-weights. 
                g : Vector FTerm (ar {μ} S c)
                g i = toFun $ fromVec v i
        toTerm : FTerm → Term S
        toTerm (f-nul c) = nullary c
        toTerm (f-mul c f) = multiary c (toVec g) -- (toVec (Data.Vec.Functional.map toTerm f))
            where
                g : Vector (Term S) (ar {μ} S c)
                g i = toTerm $ f i

        code-f : FTerm → ^ μ ⊎ ℕ
        code-sum : ^ μ ⊎ ℕ → ℕ

        code-f t = ?
        code-sum = {! code-sum-lemma !}

    

sigenum
    : {μ ζ : ℕ∞}
    → (S : Signature μ ζ)
    → Term {μ} {ζ} S ≃ sigset μ ζ
sigenum {fin 0} {ζ} S            = emptyCase S
sigenum {μ@(finsuc _)} {fin 0} S = noMultiaryCase μ S
sigenum {μ@∞} {fin 0} S          = noMultiaryCase μ S
sigenum {finsuc x} {finsuc y} S  = inductiveCase (fin x) S
sigenum {finsuc x} {∞} S         = inductiveCase (fin x) S
sigenum {∞} {finsuc y} S         = inductiveCase ∞ S
sigenum {∞} {∞} S                = inductiveCase ∞ S

