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
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Relation.Unary using (_⊆_)
open import Data.Vec
open import Data.Vec.Functional hiding (_∷_)
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.All as All hiding (_∷_)
open import Data.Vec.Relation.Unary.All.Properties
open import Data.Fin using (Fin)
open import Function hiding (_↔_)

open import Eser.Card
open import Eser.Signature
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Aux using (_≈_ ; ℓ<m<1+n→ℓ<n)


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

        T : Set
        T = Term {μ} S
        

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

        --code-fterm : FTerm → ℕ
        --code-fterm (f-nul c) = code-sum (inj₁ c)
        --code-fterm (f-mul c v) = (code-sum ∘ inj₂ ∘ code-pair) (c , v-code)
        --    where
        --        v' : Vector ℕ (ar c)
        --        v' i = code-fterm $ v i
        --        v-code : ℕ
        --        v-code = code-vec (toVec v')

        ---- Decoding an ℕ into an FTerm cannot be done by structural recursion;
        ---- we get a number i, and if it encodes a multiary-constructed
        ---- term then we also get a Vec ℕ of arguments (as numbers).
        ---- There is no structural relation between these numbers
        ---- and i. However, we can *prove* that they are all smaller than i,
        ---- which means we can use the fuel technique 
        ---- (or (ℕ, <)-wellfounded-recursion, but the fuel technique makes it
        ---- easier to prove that decode-fterm is inverse to code-fterm).
        --decode-fterm-fuelled : {b i : ℕ} → i < b → FTerm
        --decode-fterm-fuelled {b@(suc b')} {i} i<b = cases (decode-sum i) refl
        --    where
        --        cases : (j : ^ μ ⊎ ℕ) → (decode-sum i ≡ j) → FTerm
        --        cases (inj₁ c) _ = f-nul c
        --        cases (inj₂ w) eq = f-mul c v
        --            where
        --                c : ^ ζ
        --                c = proj₁ $ decode-pair w
        --                y : ℕ
        --                y = proj₂ $ decode-pair w

        --                v' : Vec ℕ (ar c)
        --                v' = decode-vec (S c) y

        --                v'<i : All (_< i) v'
        --                v'<i = decode-multiary-lemma i w y c v' eq refl refl

        --                <i⊆<b' : (_< i) ⊆ (_< b')
        --                <i⊆<b' {x} x<i = ℓ<m<1+n→ℓ<n x<i i<b

        --                v'<b' : All (_< b') v'
        --                v'<b' = All.map <i⊆<b' v'<i

        --                recurse
        --                    : {n : ℕ}
        --                    → (n ∈ v')
        --                    → FTerm
        --                recurse {n} n∈v' = decode-fterm-fuelled {b'} {n} n<b'
        --                    where
        --                        n<b' : n < b'
        --                        n<b' = All.lookup v'<b' n∈v'

        --                v : Vector FTerm (ar c)
        --                v = fromVec $ mapWith∈ v' recurse
                        
        --decode-fterm : ℕ → FTerm
        --decode-fterm i = decode-fterm-fuelled {suc i} {i} (n<1+n i)
                
    
        code-term : T → ℕ
        code-term-vec : {n : ℕ} → Vec T n → Vec ℕ n

        code-term (nullary c) = code-sum (inj₁ c)
        code-term (multiary c v) = (code-sum ∘ inj₂ ∘ code-pair) 
            (c , (code-vec ∘ code-term-vec) v)

        code-term-vec {0} [] = Vec.[]
        code-term-vec {suc n} (t ∷ ts) = (code-term t) ∷ (code-term-vec {n} ts)


        -- Decoding an ℕ into a Term cannot be done by structural recursion;
        -- we get a number i, and if it encodes a multiary-constructed
        -- term then we also get a Vec ℕ of arguments (as numbers).
        -- There is no structural relation between these numbers
        -- and i. However, we can *prove* that they are all smaller than i,
        -- which means we can use the fuel technique 
        -- (or (ℕ, <)-wellfounded-recursion, but the fuel technique makes it
        -- easier to prove that decode-term is inverse to code-term).
        decode-term-fuelled : {b i : ℕ} → i < b → T
        decode-term-fuelled {b@(suc b')} {i} i<b = cases (decode-sum i) refl
            module Decode where
                cases : (j : ^ μ ⊎ ℕ) → (decode-sum i ≡ j) → T
                cases (inj₁ c) _ = nullary c
                cases (inj₂ w) eq-i = multiary c (getVec (c , y) refl)
                    module DecodeCases where
                        c : ^ ζ
                        c = proj₁ $ decode-pair w
                        y : ℕ
                        y = proj₂ $ decode-pair w

                        getVec 
                            : (x : ^ ζ × ℕ) 
                            → (decode-pair w ≡ x) 
                            → Vec T (ar $ proj₁ x)
                        getVec (c , y) eq-w = v''
                            where
                                v' : Vec ℕ (ar c)
                                v' = decode-vec (S c) y

                                v'<i : All (_< i) v'
                                v'<i = decode-multiary-lemma i w y c v' eq-i eq-w refl

                                <i⊆<b' : (_< i) ⊆ (_< b')
                                <i⊆<b' {x} x<i = ℓ<m<1+n→ℓ<n x<i i<b

                                v'<b' : All (_< b') v'
                                v'<b' = All.map <i⊆<b' v'<i

                                recurse
                                    : {n : ℕ}
                                    → (n ∈ v')
                                    → T
                                recurse {n} n∈v' = decode-term-fuelled {b'} {n} n<b'
                                    where
                                        n<b' : n < b'
                                        n<b' = All.lookup v'<b' n∈v'

                                v'' : Vec T (ar c)
                                v'' = mapWith∈ v' recurse

                -- This is not used to produce output,
                -- but used in the inversity proofs, 
                -- which open the `Decode` module.
                cases-lemma 
                    : (j j' : ^ μ ⊎ ℕ)
                    → (p : decode-sum i ≡ j)
                    → (q : j ≡ j')
                    → cases j p ≡ cases j' (trans p q)
                cases-lemma j j' refl refl = refl
                        
        decode-term : ℕ → T
        decode-term i = decode-term-fuelled {suc i} {i} (n<1+n i)

        dec = decode-term
        enc = code-term
        decode-code-term : decode-term ∘ code-term ≈ id
        decode-code-term (nullary c) = 
            ≡begin 
                dec (enc (nullary c))
            ≡⟨⟩
                dec (code-sum (inj₁ c))
            ≡⟨⟩
                cases (decode-sum (code-sum (inj₁ c))) refl
            ≡⟨ cases-lemma  (decode-sum (code-sum (inj₁ c))) (inj₁ c) refl eq ⟩
                cases (inj₁ c) eq
            ≡⟨⟩
                nullary c
            ≡∎
            where
                i : ℕ
                i = code-sum (inj₁ c)

                open Decode i {i} (n<1+n i)

                eq : decode-sum (code-sum (inj₁ c)) ≡ inj₁ c
                eq = decode-code-sum $ inj₁ c
            
        decode-code-term (multiary c v) = 
            ≡begin 
                dec (enc (multiary c v))
            ≡⟨⟩
                (dec $ code-sum $ inj₂ $ code-pair 
                    (c , code-vec (code-term-vec v)))
            ≡⟨⟩
                cases (decode-sum $ code-sum i) refl
            ≡⟨ cases-lemma (decode-sum (code-sum i)) i refl sum-eq ⟩
                cases i sum-eq 
            ≡⟨⟩
                cases (inj₂ w) sum-eq
            ≡⟨⟩
                multiary c' (getVec (c' , y') refl)
            ≡⟨ cases-output-cong (c' , y') (c , y) refl c'y'≡cy ⟩
                multiary c (getVec (c , y) (c'y'≡cy))
            ≡⟨ cong (multiary c) eq-v ⟩
                multiary c v
            ≡∎
            where
                i : ^ μ ⊎ ℕ
                i = inj₂ $ code-pair (c , code-vec (code-term-vec v))
                w : ℕ
                w = code-pair (c , code-vec (code-term-vec v))
                y : ℕ
                y = code-vec (code-term-vec v)

                open Decode (code-sum i) {code-sum i} (n<1+n $ code-sum i)

                sum-eq : (decode-sum $ code-sum i) ≡ i
                sum-eq = decode-code-sum i

                open DecodeCases w sum-eq renaming (c to c' ; y to y')

                c'y'≡cy : (c' , y') ≡ (c , y)
                c'y'≡cy = decode-code-pair (c , code-vec (code-term-vec v))

                cases-output-cong
                    : (x x' : ^ ζ × ℕ)
                    → (eq-w : decode-pair w ≡ x)
                    → (eq-x : x ≡ x')
                    → multiary (proj₁ x) (getVec x eq-w) 
                    ≡ multiary (proj₁ x') (getVec x' (trans eq-w eq-x))
                cases-output-cong x x' refl refl = refl

                eq-v : getVec (c , y) (c'y'≡cy) ≡ v
                eq-v = ?


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

