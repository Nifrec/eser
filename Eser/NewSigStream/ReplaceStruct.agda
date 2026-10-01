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
open import Data.Bool using (Bool ; true ; false)
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

open import Eser.Logic using 
    ( ≡true→T 
    ; T→≡true
    ; ≡false→T∘not 
    ; isYes-elim-true 
    ; isYes-intro-true 
    ; false≢true 
    )
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

_⊄_ : ℕ → ℕ → Set
x ⊄ y = x is-arg-of y ≡ false

⊂→∈∈
    : {x y : ℕ}
    → x ⊂ y
    → φ⁻¹ x ∈∈ φ⁻¹ y
⊂→∈∈ = toWitness ∘ ≡true→T

⊄→¬∈∈
    : {x y : ℕ}
    → x ⊄ y
    → ¬ (φ⁻¹ x ∈∈ φ⁻¹ y)
⊄→¬∈∈ = toWitnessFalse ∘ ≡false→T∘not

∈∈→⊂
    : {x y : ℕ}
    → φ⁻¹ x ∈∈ φ⁻¹ y
    → x ⊂ y
∈∈→⊂ = T→≡true ∘ fromWitness
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
        t∈∈s = ⊂→∈∈ x⊂y
    
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
        t∈∈s = ⊂→∈∈ x⊂y

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
            


replace-T-replace
    : (y x x' : ℕ)
    → replace-T (φ⁻¹ y) (φ⁻¹ x) (φ⁻¹ x') ≡ φ⁻¹ (replace y x x')
replace-T-replace y x x' =
    begin 
        replace-T (φ⁻¹ y) (φ⁻¹ x) (φ⁻¹ x')
    ≡⟨ sym $ φ⁻¹∘φ≈id $ replace-T (φ⁻¹ y) (φ⁻¹ x) (φ⁻¹ x')  ⟩
        (φ⁻¹ $ φ $ replace-T (φ⁻¹ y) (φ⁻¹ x) (φ⁻¹ x'))
    ≡⟨⟩
        φ⁻¹ (replace y x x')
    ∎
    where
        open ≡-Reasoning
    
--------------------------------------------------------------------------------
-- keep
--------------------------------------------------------------------------------

keep-T
    : {s t t' r : T}
    → r ∈∈ s
    → t ≢ r
    → r ∈∈ (replace-T s t t')
keep-T {multiary c v} {t} {t'} {r} r∈v t≢r = 
    replace-all-keep _≡T?_ v t t' r r∈v t≢r

keep
    : (y x x' z : ℕ)
    → z ⊂ y
    → x ≢ z
    → z ⊂ (replace y x x')
keep y x x' z z⊂y x≢z = isYes-intro-true ans (φ⁻¹ z ∈∈? φ⁻¹ y')
    where
        import Eser.Equivalences.Properties
        open  Eser.Equivalences.Properties.NeqCong enum
        open ≡-Reasoning
        y' : ℕ
        y' = replace y x x'
        ans' : φ⁻¹ z ∈∈ (replace-T (φ⁻¹ y) (φ⁻¹ x) (φ⁻¹ x'))
        ans' = keep-T ( isYes-elim-true {a? = (φ⁻¹ z) ∈∈? (φ⁻¹ y)} z⊂y) 
            (≢-cong-from x≢z)
        eq : replace-T (φ⁻¹ y) (φ⁻¹ x) (φ⁻¹ x') ≡ φ⁻¹ y'
        eq = replace-T-replace y x x'
            
        ans : φ⁻¹ z ∈∈ φ⁻¹ y'
        ans = subst ( φ⁻¹ z ∈∈_) eq ans'

--------------------------------------------------------------------------------
-- nospawn
--------------------------------------------------------------------------------
nospawn-T
    : {s t t' r : T}
    → ¬ (r ∈∈ s)
    → t' ≢ r
    → ¬ (r ∈∈ (replace-T s t t'))
nospawn-T {nullary c} {t} {t'} {r} r∈v t≢r ()
nospawn-T {multiary c v} {t} {t'} {r} r∈v t≢r = 
    replace-all-nospawn _≡T?_ v t t' r r∈v t≢r

nospawn
    : (y x x' z : ℕ)
    → z ⊄ y
    → x' ≢ z
    → z ⊄ (replace y x x')
nospawn y x x' z z⊄y x'≢z = cases (z is-arg-of y') refl
    -- The goal unfolds to:
    --      z is-arg-of (replace y x x') ≡ false
    where
        import Eser.Equivalences.Properties
        open Eser.Equivalences.Properties.NeqCong enum
        y' : ℕ
        y' = replace y x x'
        eq-y' : replace-T (φ⁻¹ y) (φ⁻¹ x) (φ⁻¹ x') ≡ φ⁻¹ y'
        eq-y' = replace-T-replace y x x'
        cases : (b : Bool) → (z is-arg-of y' ≡ b) → z ⊄ y'
        cases false eq-b = eq-b
        cases true eq-b =  ⊥-elim $ ¬H H
            where
                K : ¬ (φ⁻¹ z ∈∈ φ⁻¹ y)
                K p = false≢true $ trans (sym z⊄y)
                                         (isYes-intro-true p (φ⁻¹ z ∈∈? φ⁻¹ y))
                H : φ⁻¹ z ∈∈ φ⁻¹ y'
                H = isYes-elim-true { a? = ((φ⁻¹ z) ∈∈? (φ⁻¹ y')) } eq-b
                ¬H : ¬ (φ⁻¹ z ∈∈ φ⁻¹ y')
                ¬H = subst (λ s → ¬ (φ⁻¹ z ∈∈ s)) eq-y' 
                    (nospawn-T K (≢-cong-from x'≢z))
--------------------------------------------------------------------------------
-- comm
--------------------------------------------------------------------------------

halfcomm-T
    : (s t t' r r' : T) 
    → t ≢ r
    → t ≢ r'
    → r ≢ t'
    → replace-T (replace-T s r r') t t' ≡ replace-T (replace-T s t t') r r'
halfcomm-T (nullary c) t t' r r' t≢r t≢r' r≢t' = refl
halfcomm-T (multiary c v) t t' r r' t≢r t≢r' r≢t'
    = cong (multiary c) $ replace-all-comm _≡T?_ v t≢r t≢r' r≢t'

halfcomm
    : (y x x' z z' : ℕ) 
    → x ⊂ y 
    → z ⊂ y 
    → x ≢ z
    → x ≢ z'
    → z ≢ x'
    → replace (replace y z z') x x' ≡ replace (replace y x x') z z'
halfcomm y x x' z z' _ _ x≢z x≢z' z≢x' =
    cong φ $
    begin 
        replace-T (φ⁻¹ (replace y z z')) (φ⁻¹ x) (φ⁻¹ x')
    ≡⟨ cong (λ u → replace-T u t t') $ sym $ replace-T-replace y z z' ⟩
        replace-T (replace-T s r r') t t'
    ≡⟨ halfcomm-T s t t' r r' t≢r t≢r' r≢t' ⟩
        replace-T (replace-T s t t') r r'
    ≡⟨ cong (λ u → replace-T u r r') $ replace-T-replace y x x' ⟩
        replace-T (φ⁻¹ (replace y x x')) (φ⁻¹ z) (φ⁻¹ z')
    ∎
    where
        open ≡-Reasoning
        import Eser.Equivalences.Properties
        open Eser.Equivalences.Properties.NeqCong enum
        t = φ⁻¹ x
        t' = φ⁻¹ x'
        r = φ⁻¹ z
        r' = φ⁻¹ z'
        s = φ⁻¹ y
        t≢r : t ≢ r
        t≢r = ≢-cong-from x≢z
        t≢r' : t ≢ r'
        t≢r' = ≢-cong-from x≢z'
        r≢t' : r ≢ t'
        r≢t' = ≢-cong-from z≢x'

--------------------------------------------------------------------------------
-- noeff
--------------------------------------------------------------------------------

noeff-T
    : (s t t' : T) 
    → ¬ (t ∈∈ s) 
    → s ≡ replace-T s t t'
noeff-T (nullary c) _ _ _ = refl
noeff-T (multiary c v) t t' ¬t∈v = 
      sym 
    $ cong (multiary c) 
    $ replace-all-not-member _≡T?_ v t t' ¬t∈v

noeff
    : (y x x' : ℕ) 
    → (x is-arg-of y ≡ false) 
    → y ≡ replace y x x'
noeff y x x' x⊄y = 
    sym $
    begin 
        replace y x x'
    ≡⟨⟩
        φ (replace-T s t t')
    ≡⟨ cong φ $ sym $ noeff-T s t t' ¬t∈∈s ⟩
        φ s
    ≡⟨ φ∘φ⁻¹≈id y ⟩
        y
    ∎
    where
        open ≡-Reasoning
        s : T
        s = φ⁻¹ y
        t : T
        t = φ⁻¹ x
        t' : T
        t' = φ⁻¹ x'
        ¬t∈∈s : ¬ (t ∈∈ s)
        ¬t∈∈s = ⊄→¬∈∈ x⊄y

--------------------------------------------------------------------------------
-- eff
--------------------------------------------------------------------------------

eff-T
    : (s t t' : T)
    → t ∈∈ s
    → t' ∈∈ (replace-T s t t')
eff-T (multiary c v) t t' t∈v = replace-all-effect _≡T?_ t' t∈v

eff
    : (y x x' : ℕ)
    → (x is-arg-of y ≡ true)
    → x' is-arg-of (replace y x x') ≡ true
eff y x x' x⊂y = ∈∈→⊂ t'∈∈s'
    where
        open ≡-Reasoning
        s : T
        s = φ⁻¹ y
        t : T
        t = φ⁻¹ x
        t' : T
        t' = φ⁻¹ x'
        s' : T
        s' = replace-T s t t'
        t∈∈s : t ∈∈ s
        t∈∈s = ⊂→∈∈ x⊂y
        t'∈∈s' : t' ∈∈ φ⁻¹ (replace y x x')
        t'∈∈s' = subst (t' ∈∈_) (replace-T-replace y x x')
            $ eff-T s t t' t∈∈s

    

--------------------------------------------------------------------------------
-- halfcut
--------------------------------------------------------------------------------
--The proof is very similar to halfcomm.

halfcut-T
    : (s t r u : T)
    → replace-T (replace-T s t u) u r ≡ replace-T (replace-T s t r) u r
halfcut-T (nullary c) _ _ _ = refl
halfcut-T (multiary c v) t r u = 
    cong (multiary c) $ replace-all-halfcut _≡T?_ v t r u

halfcut
    : (y x z a : ℕ)
    → replace (replace y x a) a z ≡ replace (replace y x z) a z
halfcut y x z a =
    cong φ $
    begin 
        replace-T (φ⁻¹ (replace y x a)) (φ⁻¹ a) (φ⁻¹ z)
    ≡⟨ cong (λ j → replace-T j u r) $ sym $ replace-T-replace y x a ⟩
        replace-T (replace-T s t u) u r
    ≡⟨ halfcut-T s t r u ⟩
        replace-T (replace-T s t r) u r
    ≡⟨ cong (λ j → replace-T j u r) $ replace-T-replace y x z ⟩
        replace-T (φ⁻¹ (replace y x z)) (φ⁻¹ a) (φ⁻¹ z)
    ∎
    where
        open ≡-Reasoning
        s = φ⁻¹ y
        t = φ⁻¹ x
        r = φ⁻¹ z
        u = φ⁻¹ a

--------------------------------------------------------------------------------
-- id-rep (identity replacement)
--------------------------------------------------------------------------------

id-rep-T
    : (s t : T)
    → replace-T s t t ≡ s
id-rep-T (nullary c) _ = refl
id-rep-T (multiary c v) t = cong (multiary c) $ replace-all-id v t

id-rep
    : (y x : ℕ)
    → replace y x x ≡ y
id-rep y x = 
    begin 
        replace y x x
    ≡⟨⟩
        φ (replace-T s t t)
    ≡⟨ cong φ $ id-rep-T s t ⟩
        φ s
    ≡⟨ φ∘φ⁻¹≈id y ⟩
        y
    ∎
    where
        open ≡-Reasoning
        s = φ⁻¹ y
        t = φ⁻¹ x
    
--------------------------------------------------------------------------------
-- complete
--------------------------------------------------------------------------------

complete
    : (y x x' : ℕ)
    → x ≢ x'
    → (x is-arg-of y ≡ true) 
    → (x is-arg-of (replace y x x')) ≡ false
complete = ?

--------------------------------------------------------------------------------
-- Putting it all together in one ReplaceStruct
--------------------------------------------------------------------------------


sig-to-replacestruct : ReplaceStruct
sig-to-replacestruct = record 
    { _is-arg-of_ = _is-arg-of_
    ; ⊂-resp-< = ⊂-resp-< 
    ; replace = replace
    ; replace-< = replace-<
    ; keep = keep
    ; nospawn = nospawn
    ; halfcomm = halfcomm
    ; noeff = noeff
    ; eff = eff
    ; halfcut = halfcut
    ; id-rep = {! !} 
    ; complete = {! !} 
    }
