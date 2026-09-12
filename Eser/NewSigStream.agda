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
open import Relation.Unary using (_⊆_)
open import Data.Vec
open import Data.Vec.Functional -- Imports `Vector`, `toVec`, `fromVec` etc.
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.All as All -- renaming (map to All-map ; lookup to All-lookup)
open import Data.Vec.Relation.Unary.All.Properties
open import Data.Fin using (Fin)
open import Function hiding (_↔_)

open import Eser.Card
open import Eser.Signature
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Aux using (ℓ<m<1+n→ℓ<n)


module Eser.NewSigStream where

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
    private
        ar : ^ ζ → ℕ
        ar c = suc (S c)

    data Term : Set where
        nullary : ^ μ → Term
        multiary : (c : ^ ζ) → Vec Term (ar c) → Term

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
        μ : ℕ∞
        μ = suc∞ μ'
        ζ : ℕ∞
        ζ = suc∞ ζ'
        ar : ^ ζ → ℕ
        ar c = suc (S c)

        open import Eser.NatCoding
        open Eser.NatCoding.WithMuZeta μ' ζ' hiding (μ ; ζ)


        -- Same as Term S, but now the arguments are given
        -- as a function (Vector A n  ≔ (Fin n → A)),
        -- for which the termination checker allows to recurse on its elements
        -- (for a Vec, this is not allowed).
        data FTerm : Set where
            f-nul : ^ μ → FTerm
            f-mul : (c : ^ ζ) → Vector FTerm (ar c) → FTerm

        toFun : Term S → FTerm
        argVecToFuns : {n : ℕ} → Vec (Term {μ} S) n → Vector FTerm n

        argVecToFuns [] = Data.Vec.Functional.[]
        argVecToFuns (t ∷ ts) Fin.zero = toFun t 
        argVecToFuns (t ∷ ts) (Fin.suc i) = argVecToFuns ts i

        toFun (nullary c) = f-nul c
        toFun (multiary c v) = f-mul c (argVecToFuns v)

        toTerm : FTerm → Term S
        toTerm (f-nul c) = nullary c
        toTerm (f-mul c f) = multiary c (toVec g)
            where
                g : Vector (Term S) (ar c)
                g i = toTerm $ f i

        decode-multiary-lemma
            : (i w y : ℕ)
            → (c : ^ ζ)
            → (v : Vec ℕ (ar c))
            → decode-sum i ≡ inj₂ w
            → decode-pair w ≡ (c , y)
            → decode-vec (S c) y ≡ v
            → All (_< i) v
        decode-multiary-lemma = ?

        code-fterm : FTerm → ℕ
        code-fterm (f-nul c) = code-sum (inj₁ c)
        code-fterm (f-mul c v) = (code-sum ∘ inj₂ ∘ code-pair) (c , v-code)
            where
                v' : Vector ℕ (ar c)
                v' i = code-fterm $ v i
                v-code : ℕ
                v-code = code-vec (toVec v')

        -- Decoding an ℕ into an FTerm cannot be done by structural recursion;
        -- we get a number i, and if it encodes a multiary-constructed
        -- term then we also get a Vec ℕ of arguments (as numbers).
        -- There is no structural relation between these numbers
        -- and i. However, we can *prove* that they are all smaller than i,
        -- which means we can use the fuel technique 
        -- (or (ℕ, <)-wellfounded-recursion, but the fuel technique makes it
        -- easier to prove that decode-fterm is inverse to code-fterm).
        decode-fterm-fuelled : {b i : ℕ} → i < b → FTerm
        decode-fterm-fuelled {b@(suc b')} {i} i<b = cases (decode-sum i) refl
            where
                cases : (j : ^ μ ⊎ ℕ) → (decode-sum i ≡ j) → FTerm
                cases (inj₁ c) _ = f-nul c
                cases (inj₂ w) eq = f-mul c v
                    where
                        c : ^ ζ
                        c = proj₁ $ decode-pair w
                        y : ℕ
                        y = proj₂ $ decode-pair w

                        v' : Vec ℕ (ar c)
                        v' = decode-vec (S c) y

                        v'<i : All (_< i) v'
                        v'<i = decode-multiary-lemma i w y c v' eq refl refl

                        <i⊆<b' : (_< i) ⊆ (_< b')
                        <i⊆<b' {x} x<i = ℓ<m<1+n→ℓ<n x<i i<b

                        v'<b' : All (_< b') v'
                        v'<b' = All.map <i⊆<b' v'<i

                        recurse
                            : {n : ℕ}
                            → (n ∈ v')
                            → FTerm
                        recurse {n} n∈v' = decode-fterm-fuelled {b'} {n} n<b'
                            where
                                n<b' : n < b'
                                n<b' = All.lookup v'<b' n∈v'

                        v : Vector FTerm (ar c)
                        v = fromVec $ mapWith∈ v' recurse
                        
        decode-fterm : ℕ → FTerm
        decode-fterm i = decode-fterm-fuelled {suc i} {i} (n<1+n i)
                
    

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

