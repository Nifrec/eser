-- Module      : Eser.SigStream.ExpandTerms
-- Description : Replace args-as-numbers by actual subterms.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- In NumTerms (and in ONT), each multiary term has a vector
-- of integers representing its arguments.
-- Given a 'nice' enumeration of NumTerms, we can interpret these integers
-- as giving the enumeration-indices of subterms and substitute them
-- accordingly. This gives IndTerms: a representation of the term algebra in
-- which each term has explicit IndTerms as arguments.
--
-- 'Nice' means that the enumeration assigns a multiary NumTerm a 
-- greater number than any of the integers in its vector of arguments
-- (formalised as `MakesArgsSmaller`).
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
open import Data.Vec.Properties
open import Data.List renaming (_∷_ to _∷L_) hiding (sum ; length)
open import Function hiding (_↔_)

open import Induction.WellFounded

open import Eser.Stdlib using (∸-suc)
open import Eser.Aux using (doubleSubst ; S[m∸Sn]≡m∸n ; _≈_)
open import Eser.Signature.Definitions hiding (ClosedTerms)
open import Eser.Card
open import Eser.Equivalences.Notation using (_≃_)
open import Eser.Equivalences.Properties using (mk≃')

module Eser.SigStream.ExpandTerms
    {μ' ζ' : ℕ∞} 
    (S : Signature (suc∞ μ') (suc∞ ζ')) 
    where

open import Eser.SigStream.NewTerms {μ'} {ζ'} S

module _ 
    (e : NT ≃ ℕ)
    (argSmaller : MakesArgsSmaller (Inverse.to e))
    where

    open Eser.Equivalences.Notation.EquivShorthands e

    -- Type IndTerms : open terms of term algebra over signature,
    -- where arguments are given one-by-one (in same style as in ONT)
    -- and are also of type IndTerms.
    -- IndTerms is also indexed by the number of arguments
    -- a partially-applied operation still needs to become a closed term.
    open import Eser.Signature.NoWeight.Definitions
        --renaming (OpenTermsNW to IndTerms)
    IndTerms = OpenTermsNW {μ} {ζ} S

    open OpenTermsNW renaming 
        ( mk-nullary-nw to it-nullary
        ; mk-multiary-nw to it-multiary
        ; giveArg-nw to it-app
        )

    ClosedTerms = IndTerms 0

    CONT≃ℕ : CONT ≃ ℕ
    CONT≃ℕ = {! TODO: get from e !}

    open Eser.Equivalences.Notation.EquivShorthands CONT≃ℕ renaming
        (φ to ψ 
        ; φ⁻¹ to ψ⁻¹
        ; φ∘φ⁻¹≈id to ψ∘ψ⁻¹≈id
        ; φ⁻¹∘φ≈id to ψ⁻¹∘ψ≈id
        )

    --------------------------------------------------------------------------------
    -- From CONT ≃ ℕ we get ClosedTerms ≃ ℕ.
    -- This proof requires delicate inductive reasoning and to satisfy the
    -- termination checker we use the fuel technique.
    -- The fuel arguments are denoted by 'b'.
    --
    -- Since CONT contains two kinds of representations,
    -- namely 
    -- 1. an operation with args-as-numbers
    -- and 
    -- 2. numbers (as used for the args)
    -- we define g and g' by mutual induction.
    -- g acts on the numbers, g' on the operations
    --------------------------------------------------------------------------------

    data _∈∈_ : {n m : ℕ} → {a : Arity} → ℕ → ONT n m a → Set where
        ∈∈-here 
            : {n m : ℕ} 
            → (a x : ℕ) 
            → (t : ONT (suc n) m Multiary) 
            → a ≡ x
            → a ∈∈ ont-app t x
        ∈∈-there
            : {n m : ℕ} 
            → (a x : ℕ) 
            → (t : ONT (suc n) m Multiary) 
            → a ∈∈ t
            → a ∈∈ ont-app t x

    -- #TODO: prove a MakesArgsSmaller-enum implies for CONT:
    -- a ∈∈ t -> a < ψ (t)
    -- where ψ ≔ φ ∘ k and φ ≔ Inverse.to e.
    lemma-MakesArgsSmallers-∈∈
        : {m x : ℕ}
        → {a : Arity}
        → (t : ONT 0 m a)
        → x ∈∈ t
        → x < ψ (m , a , t)
    lemma-MakesArgsSmallers-∈∈ = ?
    
    -- b is fuel
    -- i is the number to map to a ClosedTerm.
    g : (b i : ℕ) → i < b → ClosedTerms
    g' 
        : (b : ℕ) 
        → {n m : ℕ} → {a : Arity} → (t : ONT (suc n) m a)
        → ({x : ℕ} → x ∈∈ t → x < b)
        → IndTerms (suc n)

    g (suc b) i i<1+b = g-cases (ψ⁻¹ i) refl
        where
            g-cases : (t : CONT) → (t ≡ ψ⁻¹ i) → ClosedTerms
            g-cases (ℕ.zero , Nullary , ont-nullary c) _ = it-nullary c
            g-cases s@(suc m , Multiary , ont-app t a) eq = it-app t' a'
                where
                    x∈∈s→x<i : {x : ℕ} → x ∈∈ (ont-app t a) → x < i
                    x∈∈s→x<i {x} x∈∈s =  
                        subst (x <_) (trans (cong ψ eq) (ψ∘ψ⁻¹≈id i)) 
                        $ lemma-MakesArgsSmallers-∈∈ (ont-app t a) x∈∈s

                    H : ({x : ℕ} → x ∈∈ t → x < b)
                    H {x} x∈∈t = x<b
                        where
                            x<i : x < i
                            x<i = x∈∈s→x<i (∈∈-there x a t x∈∈t)  
                            x<b : x < b
                            x<b = ≤-trans x<i (s≤s⁻¹ i<1+b)
                    t' : IndTerms 1
                    t' = g' b t H
                    a<i : a < i
                    a<i = x∈∈s→x<i (∈∈-here a a t refl)  
                    a<b : a < b
                    a<b = ≤-trans a<i (s≤s⁻¹ i<1+b)
                    a' : IndTerms 0
                    a' = g b a a<b

    g' b (ont-multiary c) H = it-multiary c
    g' b (ont-app t a) H = it-app (g' b t H') (g b a a<b)
        where
            H' : ({x : ℕ} → x ∈∈ t → x < b)
            H' {x} x∈∈t = H (∈∈-there x a t x∈∈t)
            a<b : a < b
            a<b = H (∈∈-here a a t refl)

    -- Variant on g that automatically chooses an appropriate quantity of fuel.
    -- For this variant we can prove that it is an equivalence.
    g* : ℕ → ClosedTerms
    g* i = g (suc i) i (n<1+n i)
             
    ----------------------------------------------------------------------------
    -- Surjectivity of g*
    ----------------------------------------------------------------------------
    
    -- Same as ∈∈ but then defined on IndTerms instead of ONT.
    -- The variable `m` is only for flexibility,
    -- there are only constructors for m ≔ 0.
    data _⋤_ : {m n : ℕ} → IndTerms m → IndTerms n → Set where
        ⋤-here 
            : {n : ℕ} 
            → (t : IndTerms (suc n)) 
            → (a : IndTerms 0) 
            → a ⋤ (it-app t a)
        ⋤-there
            : {n : ℕ} 
            → (t : IndTerms (suc n)) 
            → (a x : IndTerms 0) 
            → a ⋤ t
            → a ⋤ (it-app t x)

    -- #TODO: ⋤ is well-founded and admits a rec:
    AllIndTerms : Set
    AllIndTerms = Σ[ n ∈ ℕ ] IndTerms n

    _⋤*_ : AllIndTerms → AllIndTerms → Set
    (m , s) ⋤* (n , t) = s ⋤ t

    _⋤C_ : ClosedTerms → ClosedTerms → Set
    s ⋤C t = s ⋤ t

    ⋤C→⋤*
        : {s t : ClosedTerms}
        → s ⋤C t 
        → (0 , s) ⋤* (0 , t)
    ⋤C→⋤* = id

    ⋤*→⋤C
        : {s t : ClosedTerms}
        → (0 , s) ⋤* (0 , t)
        → s ⋤C t 
    ⋤*→⋤C = id

    ⋤*-WF : WellFounded _⋤*_
    ⋤*-WF = ?

    ⋤C-WF : WellFounded _⋤C_
    ⋤C-WF t = acc f
        where
            lemma : {s : ClosedTerms} →  Acc _⋤*_ (0 , s) → Acc _⋤C_ s
            lemma {s} (acc fₛ) = acc {! h !}
                where
                    h : {r : ClosedTerms} → r ⋤C s → Acc _⋤C_ r
                    h {r} r⋤Cs = Acc⋤*R
                        where
                            Acc⋤*R : Acc _⋤*_ (0 , r)
                            Acc⋤*R = fₛ r⋤Cs
            f : {a : ClosedTerms}
                → (a ⋤C t)
                → Acc _⋤C_ a
            f {a} a⋤Ct = lemma $ acc-inverse (⋤*-WF (0 , t)) (⋤C→⋤* a⋤Ct)



    ⋤*-rec 
        : (P : AllIndTerms → Set)
        → (
            (nt : AllIndTerms)
            → ({ms : AllIndTerms} → ms ⋤* nt → P ms)
            → P nt
        )
        → (nt : AllIndTerms)
        → P nt
    ⋤*-rec = wfRec 0ℓ
        where
            open Induction.WellFounded.All {_<_ = _⋤*_} ⋤*-WF

    -- Predicate on an t : ClosedTerms that there exist an input i 
    -- and a fuel b>i such that g(b , i , i<b) ≡ t.
    g⁻¹-ex : ClosedTerms → Set
    g⁻¹-ex t =  Σ[ b ∈ ℕ ]  Σ[ i ∈ ℕ ] Σ[ i<b ∈ i < b ] (g b i i<b) ≡ t

    -- Predicate on an t : IndTerms (suc n) that there exist inputs
    -- * Fuel b : ℕ
    -- * Open number term s : ONT (suc n)
    -- * Proof H : x ∈∈ s → x < b
    -- inputs b and H to g' 
    -- s.t. (g' b s H) ≡ t.
    g'⁻¹-ex : {n : ℕ} → IndTerms (suc n) → Set
    g'⁻¹-ex {n} t = 
        Σ[ b ∈ ℕ ] 
        Σ[ m ∈ ℕ ]
        Σ[ s ∈ (ONT (suc n) m Multiary)]
        Σ[ H ∈ ({x : ℕ} → x ∈∈ s → x < b) ]
        (g' b s H) ≡ t

    -- g-surj and g'-surj are defined in mutual induction, quite like
    -- how g and g' are defined in mutual induction themselves.
    g-surj 
        : (t : ClosedTerms)
        → (b : ℕ)
        → ((a : ClosedTerms) → a ⋤ t → g⁻¹-ex a)
        → g⁻¹-ex t
    g-surj t b IH = ?

    g'-surj 
        : {n : ℕ} 
        → (t : IndTerms (suc n))
        → (b : ℕ)
        → ((a : ClosedTerms) → a ⋤ t → g⁻¹-ex a)
        → g'⁻¹-ex t
    g'-surj {n} t b IH = ?



    g*-surj : Surjective _≡_ _≡_ g*
    g*-surj t = ?
        --where
        --    wf-rec
        --        : (
        --            (nt : AllIndTerms)
        --            → ({ms : AllIndTerms} → ms ⋤* nt → g⁻¹-ex (proj₂ ms))
        --            → (g⁻¹-ex (proj₂ nt))
        --        )
        --        → (nt : AllIndTerms) → (g⁻¹-ex (proj₂ nt))
        --    wf-rec =  ⋤*-rec (λ (n , t) → g⁻¹-ex t)
          

    ----------------------------------------------------------------------------
    -- Injectivity of g*
    ----------------------------------------------------------------------------
    g*-inj : Injective _≡_ _≡_ g*
    g*-inj = ?
