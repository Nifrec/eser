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
open import Data.Sum hiding (reduce ; map)
open import Data.Product hiding (map)
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
--open ≡-Reasoning -- renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Relation.Unary using (_⊆_)
open import Data.Vec
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.All as All hiding (_∷_ ; head ; tail ; map)
--open import Data.Vec.Relation.Unary.All as All hiding (_∷_)
open import Data.Vec.Relation.Unary.Any as Any hiding (head ; tail ; map)
--open import Data.Vec.Relation.Unary.All.Properties
open import Data.Fin using (Fin ; toℕ)
open import Function hiding (_↔_)

open import Eser.Logic using (≡true→T)
open import Eser.Card
open import Eser.Signature.Definitions
open import Eser.Equivalences.Notation hiding (begin_ ; _∎)
--open import Eser.Equivalences.Properties
--open import Eser.Aux using (_≈_ ; ℓ<m<1+n→ℓ<n)
open import Eser.NewSigStream
open import Eser.Filters.ReplaceStructs
open import Eser.NatCoding
open import Eser.Vec
open import Eser.NewSigStream.EnumVectors
open import Eser.Partitions


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
        cases (no t≢s) _ = no (λ eq → t≢s $ cong head eq)
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
    
--------------------------------------------------------------------------------
-- Replace operation for Terms: replace ALL occurrences of an argument.
--------------------------------------------------------------------------------
-- replace-T s t t' returns s with ALL arguments equal to t replaced by t'.
-- The operation has no effect if t is not an argument of s.
replace-T : T → T → T → T
replace-T (nullary c) t t' = nullary c
replace-T (multiary c v) t t' = multiary c (replace-all _≡T?_ v t t')
 
replace : ℕ → ℕ → ℕ → ℕ
replace y x x' = φ $ replace-T (φ⁻¹ y) (φ⁻¹ x) (φ⁻¹ x')

--------------------------------------------------------------------------------
-- replace-< 
--------------------------------------------------------------------------------
-- Replacing an argument x with an argument x'
-- s.t. x comes earlier in the enumeration than x',
-- leads to a term that comes earlier in the enumeration than the original term.

todo : ⊥
todo = {! Move the lemmas below to appropriate files !}

code-term-vec-replace-all
    : {n : ℕ}
    → (v : Vec T n)
    → (t t' : T)
    → code-term-vec (replace-all _≡T?_ v t t')
      ≡
      replace-all _≟_ (code-term-vec v) (φ t) (φ t')
code-term-vec-replace-all [] t t' = refl
code-term-vec-replace-all {suc n'} v@(x ∷ xs) t t' = 
    begin 
        code-term-vec (replace-all _≡T?_ (x ∷ xs) t t')
    ≡⟨⟩ -- Def replace-all
        code-term-vec (map match-term (x ∷ xs))
    ≡⟨⟩ -- Def map
        code-term-vec (match-term x ∷ map match-term xs)
    ≡⟨⟩
        code-term (match-term x) ∷ code-term-vec (map match-term xs)
    ≡⟨ cong (_∷ code-term-vec (map match-term xs)) $ lemma (x ≡T? t) refl ⟩
        match-num (code-term x) ∷ code-term-vec (map match-term xs)
    ≡⟨⟩
        match-num (code-term x) ∷ code-term-vec (replace-all _≡T?_ xs t t')
    ≡⟨ cong (match-num (code-term x) ∷_) $ code-term-vec-replace-all xs t t' ⟩
        match-num (φ x) ∷ replace-all _≟_ (code-term-vec xs) (φ t) (φ t')
    ≡⟨⟩
        match-num (φ x) ∷ (map match-num (code-term-vec xs))
    ≡⟨⟩
        map match-num (φ x ∷ code-term-vec xs)
    ≡⟨⟩
        map match-num (code-term-vec (x ∷  xs))
    ≡⟨⟩
        replace-all _≟_ (code-term-vec v) (φ t) (φ t')
    ∎
    where
        open ≡-Reasoning
        ys : Vec ℕ n'
        ys = replace-all _≟_ (code-term-vec xs) (φ t) (φ t')

        open ReplaceAllImpl _≡T?_ v t t' 
            renaming (replace-if-matches to match-term)
        open ReplaceAllImpl.Cases _≡T?_ v t t' x 
            renaming (cases to term-cases)
        open ReplaceAllImpl _≟_ (code-term-vec v) (φ t) (φ t')
            renaming (replace-if-matches to match-num)
        open ReplaceAllImpl.Cases _≟_ (code-term-vec v) (φ t) (φ t') (φ x) 
            renaming (cases to num-cases)
        lemma 
            : (d : Dec (x ≡ t)) 
            → (x ≡T? t ≡ d)
            → code-term (match-term x) ≡ match-num (φ x)
        lemma (yes x≡t) eq = 
            begin 
                code-term (match-term x) 
            ≡⟨⟩
                φ (term-cases (x ≡T? t))
            ≡⟨ cong (φ ∘ term-cases) eq  ⟩
                φ (term-cases (yes x≡t))
            ≡⟨⟩
                φ t'
            ≡⟨⟩
                num-cases (yes φx≡φt)
            ≡⟨ cong num-cases (sym $ dec-yes-irr (φ x ≟ φ t) ≡-irrelevant φx≡φt)
             ⟩
                num-cases (φ x ≟ φ t)
            ≡⟨⟩
                match-num (φ x)
            ≡⟨⟩
                match-num (code-term x)
            ∎
            where
                φx≡φt : φ x ≡ φ t
                φx≡φt = cong φ x≡t
        lemma (no x≢t) eq =
            begin 
                code-term (match-term x) 
            ≡⟨⟩
                φ (term-cases (x ≡T? t))
            ≡⟨ cong (φ ∘ term-cases) eq  ⟩
                φ (term-cases (no x≢t))
            ≡⟨⟩
                φ x
            ≡⟨⟩
                num-cases (no φx≢φt)
            ≡⟨ cong num-cases (sym $ dec-no (φ x ≟ φ t) φx≢φt) ⟩
                num-cases (φ x ≟ φ t)
            ≡⟨⟩
                match-num (φ x)
            ≡⟨⟩
                match-num (code-term x)
            ∎
            where
                φx≢φt : φ x ≢ φ t
                φx≢φt φx≡φt = x≢t x≡t
                    where
                        x≡t : x ≡ t
                        x≡t =  
                            begin 
                                x
                            ≡⟨ sym $ φ⁻¹∘φ≈id x ⟩
                               φ⁻¹ (φ x)
                            ≡⟨ cong φ⁻¹ φx≡φt ⟩
                               φ⁻¹ (φ t)
                            ≡⟨ φ⁻¹∘φ≈id t ⟩
                                t
                            ∎
                            
replace-all-weight-<
    : {n : ℕ}
    → {v : Vec ℕ n}
    → {x' x : ℕ}
    → x ∈ v
    → x' < x
    → weight (replace-all _≟_ v x x') < weight v
replace-all-weight-< {suc n'} {x ∷ ys} {x'} {x} (here refl) x'<x = 
    begin-strict
        weight (replace-all _≟_ (x ∷ ys) x x')  
    ≡⟨⟩
        replace-if-matches x + weight (replace-all _≟_ ys x x')  
    ≡⟨⟩
        repl-cases (x ≟ x) + weight (replace-all _≟_ ys x x')  
    ≡⟨ cong (λ d → repl-cases d + weight (replace-all _≟_ ys x x'))
        (dec-yes-irr (x ≟ x) ≡-irrelevant refl)
     ⟩
        repl-cases (yes refl) + weight (replace-all _≟_ ys x x')  
    ≡⟨⟩
        x' + weight (replace-all _≟_ ys x x')  
    ≤⟨ +-monoʳ-≤ x' (rec (x ∈? ys)) ⟩
        x' + weight ys
    <⟨ +-monoˡ-< (weight ys) x'<x ⟩
        x + weight ys
    ≡⟨⟩
        weight (x ∷ ys)
    ∎
    where
        open ≤-Reasoning
        open ReplaceAllImpl _≟_ (x ∷ ys) x x'
        open ReplaceAllImpl.Cases _≟_ (x ∷ ys) x x' x 
            renaming (cases to repl-cases)
        open import Data.Vec.Membership.DecPropositional {A = ℕ} (_≟_) 
            hiding (_∈_)
        rec : (Dec (x ∈ ys)) → weight (replace-all _≟_ ys x x') ≤ weight ys
        rec (yes x∈ys) = (<⇒≤ $ replace-all-weight-< x∈ys x'<x)
        rec (no x∈ys) =
            begin 
                weight (replace-all _≟_ ys x x')
            ≡⟨ cong weight $ replace-all-not-member _≟_ ys x x' x∈ys ⟩
                 weight ys
            ≤⟨ ≤-refl ⟩
                 weight ys
            ∎
replace-all-weight-< {suc n'} {y ∷ ys} {x'} {x} (there x∈ys) x'<x =
    begin-strict
        weight (replace-all _≟_ (y ∷ ys) x x')  
    ≡⟨⟩
        replace-if-matches y + weight (replace-all _≟_ ys x x')  
    ≡⟨⟩
        u + weight (replace-all _≟_ ys x x')  
    <⟨ +-monoʳ-< u $ replace-all-weight-< {n'} {ys} {x'} {x} x∈ys x'<x ⟩
        u + weight ys
    ≤⟨ +-monoˡ-≤ (weight ys) (u≤y (y ≟ x) refl) ⟩
        y + weight ys
    ≡⟨⟩
        weight (y ∷ ys)
    ∎
    where
        open ≤-Reasoning
        open ReplaceAllImpl _≟_ (x ∷ ys) x x'
        open ReplaceAllImpl.Cases _≟_ (x ∷ ys) x x' y
        u : ℕ
        u = replace-if-matches y
        u≤y : (d : Dec (y ≡ x)) → (d ≡ (y ≟ x)) → u ≤ y
        u≤y (yes y≡x) eq = 
            begin 
                replace-if-matches y
            ≡⟨⟩
                cases (y ≟ x)
            ≡⟨ cong cases (sym eq) ⟩
                cases (yes y≡x)
            ≡⟨⟩
                x'
            ≤⟨ <⇒≤ x'<x ⟩
                x
            ≡⟨ sym y≡x ⟩
                y
            ∎
        u≤y (no y≢x) eq =
            begin 
                replace-if-matches y
            ≡⟨⟩
                cases (y ≟ x)
            ≡⟨ cong cases (sym eq) ⟩
                cases (no y≢x)
            ≡⟨⟩
                y
            ∎
    

code-vec-weight-<
    : {n : ℕ}
    → (v' v : Vec ℕ (suc n))
    → weight v' < weight v
    → code-vec v' < code-vec v
code-vec-weight-< {n} v' v w'<w = 
    begin-strict
        code-vec v'
    ≡⟨⟩
       ⨁ i' + toℕ j'
    ≡⟨ cong (λ x → ⨁ x + toℕ j') i'≡w' ⟩
       ⨁ w' + toℕ j'
    <⟨ step-in-chunk j' w'<w  ⟩
       ⨁ w 
    ≡⟨ cong ⨁ (sym i≡w) ⟩
        ⨁ i
    ≤⟨ m≤m+n (⨁ i) (toℕ j) ⟩
       ⨁ i + toℕ j  
    ≡⟨⟩
        code-vec v
    ∎
    where
        part : Partition (Vec ℕ (suc n))
        part = vec-part n

        open PartToEnumImpl part
        open ≤-Reasoning

        w' : ℕ
        w' = weight v'
        i' : ℕ
        i' = proj₁ $ proj₁ $ Partition.complete part v'
        j' : SubIdx (Partition.chunks part) i'
        j' = proj₂ $ proj₁ $ Partition.complete part v'
        i'≡w' : i' ≡ w'
        i'≡w' = vec-chunk-idx-is-weight v'

        w : ℕ
        w = weight v
        i : ℕ
        i = proj₁ $ proj₁ $ Partition.complete part v
        j : SubIdx (Partition.chunks part) i
        j = proj₂ $ proj₁ $ Partition.complete part v
        i≡w : i ≡ w
        i≡w = vec-chunk-idx-is-weight v

code-pair-inf-< 
    : (c : ℕ)
    → {x' x : ℕ} 
    → x' < x 
    → code-pair-inf (c , x') < code-pair-inf (c , x)
code-pair-inf-< c {x'} {x} x'<x = 
    begin-strict 
        code-pair-inf (c , x')
    ≡⟨⟩
        code-vec (toVec (c , x'))
    <⟨ code-vec-weight-< (c ∷ x' ∷ []) (c ∷ x ∷ []) w'<w ⟩
        code-vec (toVec (c , x))
    ≡⟨⟩
        code-pair-inf (c , x)
    ∎
    where
        open ≤-Reasoning
        w : ℕ
        w = weight (c ∷ x ∷ [])
        w' : ℕ
        w' = weight (c ∷ x' ∷ [])
        w'<w : w' < w
        w'<w = ?
    
code-pair-< 
    : {ζ' : ℕ∞}
    → (c : ^ (suc∞ ζ'))
    → {x' x : ℕ} 
    → x' < x 
    → code-pair (c , x') < code-pair (c , x)
code-pair-< {fin n} = {! code-pair-fin-< !}
code-pair-< {∞} = code-pair-inf-<


code-sum-< : {w' w : ℕ} → w' < w → code-sum (inj₂ w') < code-sum (inj₂ w)
code-sum-< = ?

replace-T-<
    : (s t t' : T)
    → t ∈∈ s
    → φ t' < φ t
    → φ (replace-T s t t') < φ s
replace-T-< s@(multiary c v) t t' t∈v t'<t = H₀
    where
        v' : Vec T (ar c)
        v' = replace-all _≡T?_ v t t'

        φt∈codev : φ t ∈ code-term-vec v
        φt∈codev = code-term-vec-membership t∈v

        H₄ : code-term-vec v' ≡ replace-all _≟_ (code-term-vec v) (φ t) (φ t')
        H₄ = code-term-vec-replace-all v t t'

        H₃ : weight (code-term-vec v') < weight (code-term-vec v)
        H₃ = subst (λ u → weight u < weight (code-term-vec v)) (sym H₄)
            $ replace-all-weight-< φt∈codev t'<t 

        H₂ : code-vec (code-term-vec v') < code-vec (code-term-vec v)
        H₂ = code-vec-weight-< (code-term-vec v') (code-term-vec v) H₃

        H₁ : code-pair (c , code-vec (code-term-vec v'))
             <                                           
             code-pair (c , code-vec (code-term-vec v))
        H₁ = code-pair-< c H₂

        H₀ : code-sum (inj₂ $ code-pair (c , code-vec (code-term-vec v')))
             <
             code-sum (inj₂ $ code-pair (c , code-vec (code-term-vec v)))
        H₀ = code-sum-< H₁

replace-<
    : (y x x' : ℕ)
    → x ⊂ y
    → x' < x
    → replace y x x' < y
replace-< y x x' x⊂y x'<x = 
    begin-strict
        replace y x x'
    ≡⟨ sym $ φ∘φ⁻¹≈id $ replace y x x' ⟩
        φ (φ⁻¹ (replace y x x'))
    ≡⟨⟩
        φ (φ⁻¹ (φ (replace-T s t t')))
    ≡⟨ cong φ $ φ⁻¹∘φ≈id $ replace-T s t t'  ⟩
        φ (replace-T s t t')
    <⟨ replace-T-< s t t' t∈∈s φt'<φt ⟩
        φ s
    ≡⟨ φ∘φ⁻¹≈id y ⟩
        y
    ∎
    where
        open ≤-Reasoning
        s : T
        s = φ⁻¹ y
        t : T
        t = φ⁻¹ x
        t' : T
        t' = φ⁻¹ x'

        t∈∈s : t ∈∈ s
        t∈∈s = toWitness $ ≡true→T x⊂y

        φt'<φt : φ t' < φ t
        φt'<φt =
            begin-strict
                φ t' 
            ≡⟨⟩
                φ (φ⁻¹ x')
            ≡⟨ φ∘φ⁻¹≈id x' ⟩
                x'
            <⟨ x'<x ⟩
                x
            ≡⟨ sym $ φ∘φ⁻¹≈id x ⟩
                φ (φ⁻¹ x)
            ≡⟨⟩
                φ t
            ∎
            

    



sig-to-replacestruct : ReplaceStruct
sig-to-replacestruct = record 
    { _is-arg-of_ = _is-arg-of_
    ; ⊂-resp-< = ⊂-resp-< 
    ; replace = replace
    ; replace-< = {! !} 
    ; keep = {! !} 
    ; nospawn = {! !} 
    ; comm = {! !} 
    ; noeff = {! !} 
    ; halfcut = {! !} 
    ; id-rep = {! !} 
    ; complete = {! !} 
    }
