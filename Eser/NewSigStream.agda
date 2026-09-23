-- Module      : Eser.NewSigStream
-- Description : New enumeration algorithm -- simplified implementation
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Simplified version of the new enumeration algorithm for term algebras of
-- Signatures.
--------------------------------------------------------------------------------

-- Lossy unification makes a huge difference in how long it takes
-- to type-check this file.
{-# OPTIONS --safe  --lossy-unification #-}

open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum hiding (reduce)
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Relation.Unary using (_⊆_)
open import Data.Vec
open import Data.Vec.Relation.Unary.All as All hiding (_∷_)
open import Data.Vec.Relation.Unary.Any as Any
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

sigset-suc∞ 
    : (μ' ζ' : ℕ∞) 
    → sigset (suc∞ μ') (suc∞ ζ') ≡ ℕ
sigset-suc∞ (fin _) (fin _) = refl
sigset-suc∞ (fin _) ∞ = refl
sigset-suc∞ ∞ (fin _) = refl
sigset-suc∞ ∞ ∞ = refl

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
inductiveCase μ' {ζ'} S = mk≃' enc dec invˡ invʳ
    where
        open import Eser.NatCoding
        -- This import also defines μ ≔ suc∞ μ' and ζ := suc∞ ζ'.
        open Eser.NatCoding.WithMuZeta μ' ζ'

        ar : ^ ζ → ℕ
        ar c = suc (S c)
        T : Set
        T = Term {μ} S

        decode-multiary-lemma
            : (i w y : ℕ)
            → (c : ^ ζ)
            → (v : Vec ℕ (ar c))
            → decode-sum i ≡ inj₂ w
            → decode-pair w ≡ (c , y)
            → decode-vec (S c) y ≡ v
            → All (_< i) v
        decode-multiary-lemma i w y c v eq-i eq-w eq-y = ans
            where
                y<i : y < i
                y<i = decode-sum-pair-lemma i w y c eq-i eq-w
                cv<i : code-vec v < i
                cv<i = subst (_< i) (sym eq) y<i
                    where
                        eq : code-vec v ≡ y
                        eq = 
                            ≡begin 
                                code-vec v
                            ≡⟨ cong code-vec $ sym eq-y ⟩
                                code-vec (decode-vec (S c) y)
                            ≡⟨ code-decode-vec (S c) y ⟩
                                y
                            ≡∎
                v≤cv : All (_≤ (code-vec v)) v
                v≤cv = code-vec-lemma v

                ans : All (_< i) v
                ans = All.map f v≤cv 
                    where
                        f : (_≤ (code-vec v)) ⊆ (_< i)
                        f {x} x≤cv = ≤-<-trans x≤cv cv<i
            

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
                            module GetVec where
                                v' : Vec ℕ (ar c)
                                v' = decode-vec (S c) y

                                v'<i : All (_< i) v'
                                v'<i = decode-multiary-lemma i w y c v' eq-i eq-w refl

                                <i⊆<b' : (_< i) ⊆ (_< b')
                                <i⊆<b' {x} x<i = ℓ<m<1+n→ℓ<n x<i i<b

                                v'<b' : All (_< b') v'
                                v'<b' = All.map <i⊆<b' v'<i

                                v'' : Vec T (ar c)
                                v'' = reduce decode-term-fuelled v'<b'

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

        -- The function `decode-term-fuelled` gives the same output 
        -- for any given amount of fuel, provided it is sufficient.
        dec-term-fuel-irrel
            : {b d i : ℕ}
            → (i<b : i < b)
            → (i<d : i < d)
            → decode-term-fuelled i<b ≡ decode-term-fuelled i<d
        dec-term-fuel-irrel {suc b'} {suc d'} {i} i<b i<d = 
            cases (decode-sum i) refl
            where
                cases
                    : (j : ^ μ ⊎ ℕ) 
                    → decode-sum i ≡ j
                    → decode-term-fuelled i<b ≡ decode-term-fuelled i<d
                cases (inj₁ c) eq-i =
                    ≡begin 
                        decode-term-fuelled i<b
                    ≡⟨⟩
                        b-cases (decode-sum i) refl
                    ≡⟨ b-cases-lemma (decode-sum i) (inj₁ c) refl eq-i ⟩
                        b-cases (inj₁ c) eq-i
                    ≡⟨⟩
                        nullary c
                    ≡⟨⟩
                        d-cases (inj₁ c) eq-i
                    ≡⟨ sym $ d-cases-lemma (decode-sum i) (inj₁ c) refl eq-i ⟩
                        d-cases (decode-sum i) refl
                    ≡⟨⟩
                        decode-term-fuelled i<d
                    ≡∎
                    where
                        open Decode b' i<b 
                            renaming (cases to b-cases 
                                     ; cases-lemma to b-cases-lemma 
                                     )

                        open Decode d' i<d
                            renaming (cases to d-cases 
                                     ; cases-lemma to d-cases-lemma 
                                     )
                    
                cases (inj₂ w) eq-i = 
                    ≡begin 
                        decode-term-fuelled i<b
                    ≡⟨⟩
                        b-cases (decode-sum i) refl
                    ≡⟨ b-cases-lemma (decode-sum i) (inj₂ w) refl eq-i ⟩
                        b-cases (inj₂ w) eq-i
                    ≡⟨⟩
                        multiary c (reduce dtf Rb)
                    ≡⟨ cong (multiary c) $ sublemma {ar c} 
                        {v = decode-vec (S c) y} Rb Rd 
                     ⟩
                        multiary c (reduce dtf Rd)
                    ≡⟨⟩
                        d-cases (inj₂ w) eq-i
                    ≡⟨ sym $ d-cases-lemma (decode-sum i) (inj₂ w) refl eq-i ⟩
                        d-cases (decode-sum i) refl
                    ≡⟨⟩
                        decode-term-fuelled i<d
                    ≡∎
                    where
                        dtf = decode-term-fuelled
                        c : ^ ζ
                        c = proj₁ $ decode-pair w
                        y = proj₂ $ decode-pair w

                        open Decode b' i<b 
                            renaming (cases to b-cases 
                                     ; cases-lemma to b-cases-lemma 
                                     )

                        open Decode.DecodeCases.GetVec b' i<b w eq-i c y refl
                            renaming (v'<b' to Rb)

                        open Decode d' i<d
                            renaming (cases to d-cases 
                                     ; cases-lemma to d-cases-lemma 
                                     )

                        open Decode.DecodeCases.GetVec d' i<d w eq-i c y refl
                            renaming (v'<b' to Rd)
                        sublemma
                            : {m : ℕ}
                            → {v : Vec ℕ m}
                            → (Rb : All (_< b') v)
                            → (Rd : All (_< d') v)
                            → reduce dtf Rb ≡ reduce dtf Rd
                        sublemma {0} {Vec.[]} All.[] All.[] = refl
                        sublemma {suc m} {x ∷ xs} 
                            (rb All.∷ rbs) (rd All.∷ rds) =
                            ≡begin 
                                reduce dtf (rb All.∷ rbs)
                            ≡⟨⟩
                                dtf rb ∷ reduce dtf rbs
                            ≡⟨ cong (dtf rb ∷_) $ sublemma rbs rds ⟩
                                dtf rb ∷ reduce dtf rds
                            ≡⟨ cong (_∷ reduce dtf rds)
                                $ dec-term-fuel-irrel {b'} {d'} {x} rb rd 
                             ⟩
                                dtf rd ∷ reduce dtf rds
                            ≡⟨⟩
                                reduce dtf (rd All.∷ rds)
                            ≡∎

        reduce-with-eq
            : {A B : Set}
            → {P : A → Set}
            → {m : ℕ}
            → {v v' : Vec A m}
            → (eq : v ≡ v')
            → (f : {a : A} → P a → B)
            → (R : All P v)
            → reduce f R ≡ reduce f (subst (All P) eq R)
        reduce-with-eq refl f R = refl

        dec = decode-term
        enc = code-term

        ------------------------------------------------------------------------
        -- decode ∘ code  ≈ id
        ------------------------------------------------------------------------

        -- Like `encode-term`, we need define one way of the inversity
        -- of decoding-encoding via mutual induction,
        -- in order to avoid termination issues with vectors.
        decode-code-term : decode-term ∘ code-term ≈ id
        dec-enc-term-vec
            : {m : ℕ}
            → {v : Vec T m}
            → {b : ℕ}
            → (rs : All (_< b) (code-term-vec v))
            → reduce decode-term-fuelled rs ≡ v
        dec-enc-term-vec {0} {Vec.[]} {b} All.[] = refl
        dec-enc-term-vec {suc m'} {v@(t ∷ ts)} {b} (r All.∷ rs) = 
            ≡begin 
                reduce decode-term-fuelled (r All.∷ rs)
            ≡⟨⟩
                decode-term-fuelled r ∷ reduce decode-term-fuelled rs
            ≡⟨ cong (decode-term-fuelled r ∷_) IH ⟩
                decode-term-fuelled r ∷ ts
            ≡⟨ cong (_∷ ts) $ dec-term-fuel-irrel r x<1+x  ⟩
                decode-term-fuelled x<1+x ∷ ts
            ≡⟨⟩ -- Fold the definition of `decode-term`.
                dec x ∷ ts
            ≡⟨⟩
                dec (enc t) ∷ ts
            ≡⟨ cong (_∷ ts) $ decode-code-term t ⟩
                v 
            ≡∎
            where
                IH : reduce decode-term-fuelled rs ≡ ts
                IH = dec-enc-term-vec rs
                x : ℕ
                x = code-term t
                x<1+x : x < suc x
                x<1+x = n<1+n x
            
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
                eq-v = 
                    ≡begin 
                        getVec (c , y) (c'y'≡cy) 
                    ≡⟨⟩
                        reduce decode-term-fuelled R
                    ≡⟨ reduce-with-eq v'≡v decode-term-fuelled R ⟩
                        reduce decode-term-fuelled R'
                    ≡⟨ dec-enc-term-vec R' ⟩
                        v
                    ≡∎
                    where
                        open GetVec c y c'y'≡cy renaming (v'<b' to R)
                        v'≡v : v' ≡ code-term-vec v
                        v'≡v = decode-code-vec {S c} (code-term-vec v)
                        b' : ℕ
                        b' = code-sum i
                        R' : All (_< b') (code-term-vec v)
                        R' = subst (All (_< b')) v'≡v R

        invʳ : Inverseʳ _≡_ _≡_ enc dec
        invʳ {t} refl = decode-code-term t
                        
        ------------------------------------------------------------------------
        -- code ∘ decode  ≈ id
        ------------------------------------------------------------------------
                    
        code-decode-term-fuelled
            : {b i : ℕ}
            → i < b
            → (code-term $ decode-term i) ≡ i
        code-decode-term-fuelled {suc b'} {i} i<1+b' = 
            ≡begin 
                enc (dec i)
            ≡⟨⟩
                enc (decode-term-fuelled (n<1+n i))
            ≡⟨ cong enc (dec-term-fuel-irrel (n<1+n i) i<1+b') ⟩
                enc (decode-term-fuelled i<1+b')
            ≡⟨ cases (decode-sum i) refl ⟩
                i
            ≡∎
            where
                open Decode b' i<1+b' renaming (cases to dec-cases)
                cases 
                    : (j : ^ μ ⊎ ℕ) 
                    → (eq-i : decode-sum i ≡ j) 
                    → (code-term $ dec-cases j eq-i) ≡ i
                cases (inj₁ c) eq-i = 
                    ≡begin 
                        enc (dec-cases (inj₁ c) eq-i)
                    ≡⟨⟩
                        enc (nullary c)
                    ≡⟨⟩
                        code-sum (inj₁ c)
                    ≡⟨ cong code-sum (sym eq-i) ⟩
                        code-sum (decode-sum i)
                    ≡⟨ code-decode-sum i ⟩
                        i
                    ≡∎
                    
                cases (inj₂ w) eq-i =
                    ≡begin 
                        enc (dec-cases (inj₂ w) eq-i)
                    ≡⟨⟩
                        enc (multiary c (getVec (c , y) refl))
                    ≡⟨⟩
                        code-sum (inj₂ (code-pair (c , (code-vec (code-term-vec v)))))
                    ≡⟨ cong (λ v → code-sum $ inj₂ $ code-pair (c , v)) v-eq ⟩
                        code-sum (inj₂ (code-pair (decode-pair w)))
                    ≡⟨ cong (code-sum ∘ inj₂) $ code-decode-pair w ⟩
                        code-sum (inj₂ w)
                    ≡⟨ cong code-sum (sym eq-i) ⟩
                        code-sum (decode-sum i)
                    ≡⟨ code-decode-sum i ⟩
                        i
                    ≡∎
                    where
                        open DecodeCases w eq-i
                        open GetVec c y refl renaming (v'<b' to R)
                        sublemma
                            : {m : ℕ}
                            → {z : Vec ℕ m}
                            → (R : All (_< b') z)
                            → code-term-vec (reduce decode-term-fuelled R) ≡ z
                        sublemma {0} {Vec.[]} All.[] = refl
                        sublemma {suc m} {x ∷ xs} R@(r All.∷ rs) = 
                            ≡begin 
                                code-term-vec (reduce decode-term-fuelled R)
                            ≡⟨⟩ -- Definition `reduce`
                                code-term-vec (dtf r ∷ reduce dtf rs)
                            ≡⟨⟩ -- Definition `code-term-vec`
                                enc (dtf r) ∷ (code-term-vec $ reduce dtf rs)
                            ≡⟨ cong (enc (dtf r) ∷_) $ sublemma rs ⟩
                                enc (dtf r) ∷ xs
                            ≡⟨ cong (λ u → (enc u) ∷ xs) 
                                $ dec-term-fuel-irrel r (n<1+n x) ⟩
                                enc (dtf (n<1+n x)) ∷ xs
                            ≡⟨⟩
                                enc (dec x) ∷ xs
                            -- We can make this recursive call, because b'
                            -- is a strict subterm of `suc b'`.
                            ≡⟨ cong (_∷ xs) 
                                $ code-decode-term-fuelled {b'} {x} r ⟩
                                x ∷ xs    
                            ≡∎
                            where
                                dtf = decode-term-fuelled
                        v : Vec T (ar c)
                        v = getVec (c , y) refl
                        v-eq : code-vec (code-term-vec v) ≡ y
                        v-eq =
                            ≡begin 
                                code-vec (code-term-vec (getVec (c , y) refl))
                            ≡⟨⟩
                                code-vec (code-term-vec 
                                    (reduce decode-term-fuelled R))
                            ≡⟨ cong code-vec $ sublemma R ⟩
                                code-vec (decode-vec (S c) y)
                            ≡⟨ code-decode-vec (S c) y ⟩
                                y
                            ≡∎

        code-decode-term : code-term ∘ decode-term ≈ id
        code-decode-term i = code-decode-term-fuelled {suc i} {i} (n<1+n i)

        invˡ : Inverseˡ _≡_ _≡_ enc dec
        invˡ {i} refl = code-decode-term i
        


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

