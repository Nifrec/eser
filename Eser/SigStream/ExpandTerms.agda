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

open import Level hiding (suc ; _⊔_ )
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
open import Eser.Aux using (doubleSubst ; doubleCong ; S[m∸Sn]≡m∸n ; _≈_)
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
        module G-Impl where
            g-cases : (t : CONT) → (t ≡ ψ⁻¹ i) → ClosedTerms
            g-cases (ℕ.zero , Nullary , ont-nullary c) _ = it-nullary c
            g-cases s@(suc m , Multiary , ont-app t a) eq = it-app t' a'
                module G-Cases where
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
        module G'-Impl where
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
    
    -- Subterm relation for IndTerms.
    -- Similar to ∈∈ but then defined on IndTerms instead of ONT,
    -- and subterms can also be from the second argument in the `app`
    -- constructor (which is, in ONT, a number, but here also an IndType 0
    -- which can have subtypes itself).
    --
    -- The variable `m` is only for flexibility,
    -- there are only constructors for m ≔ 0.
    data _⋤_ : {m n : ℕ} → IndTerms m → IndTerms n → Set where
        ⋤-here 
            : {n : ℕ} 
            → (t : IndTerms (suc n)) 
            → (a : IndTerms 0) 
            → a ⋤ (it-app t a)
        ⋤-there-left
            : {n : ℕ} 
            → (t : IndTerms (suc n)) 
            → (a x : IndTerms 0) 
            → a ⋤ t
            → a ⋤ (it-app t x)
        ⋤-there-right
            : {n : ℕ} 
            → (t : IndTerms (suc n)) 
            → (a x : IndTerms 0) 
            → a ⋤ x
            → a ⋤ (it-app t x)

    AllIndTerms : Set
    AllIndTerms = Σ[ n ∈ ℕ ] IndTerms n

    _⋤*_ : AllIndTerms → AllIndTerms → Set
    (m , s) ⋤* (n , t) = s ⋤ t

    open import Eser.IWellFounded
    ⋤-IWF : IWellFounded {I = ℕ} {A = IndTerms} _⋤_
    ⋤-IWF {n} (mk-nullary-nw c) = iacc λ { _ _ () }
    ⋤-IWF {n} (mk-multiary-nw c) = iacc λ { _ _ () }
    ⋤-IWF {n} (it-app t a) = iacc f
        where
            t-Acc : IAcc _⋤_ (suc n , t)
            t-Acc = ⋤-IWF t
            a-Acc : IAcc _⋤_ (0 , a)
            a-Acc = ⋤-IWF a
            f : (m : ℕ) (s : IndTerms m) 
                → s ⋤ it-app t a 
                → IAcc {A = IndTerms} _⋤_ (m , s)
            f 0 a (⋤-here t a) = a-Acc
            f m x (⋤-there-left t x a p) with t-Acc
            ... | iacc h = h m x p
            f m x (⋤-there-right t x a p) with a-Acc
            ... | iacc h = h m x p

    _⋤C_ : ClosedTerms → ClosedTerms → Set
    -- This is judgementally the same definition as: 
    --      _⋤C_ ≔ _⋤*_ on (λ t → (0 , t)).
    -- We exploit this judgemental equality in the  ⋤C-WF proof below.
    s ⋤C t = s ⋤ t

    ⋤C-WF : WellFounded _⋤C_
    ⋤C-WF = IWF→WF ⋤-IWF 0

    ⋤C-rec 
        : (P : ClosedTerms → Set)
        → (
            (t : ClosedTerms)
            → ({s : ClosedTerms} → s ⋤C t → P s)
            → P t
        )
        → (t : ClosedTerms)
        → P t
    ⋤C-rec = wfRec 0ℓ
        where
            open Induction.WellFounded.All {_<_ = _⋤C_} ⋤C-WF

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

    -- The value of the arguments b and i<b to g do not influence the output,
    -- they are just witnesses that these types are inhabited.
    g-fuel-irrel
        : (b b' i : ℕ)
        → (i<b : i < b)
        → (i<b' : i < b')
        → g b i i<b ≡ g b' i i<b'
    g-fuel-irrel = ?

    -- Analogue of previous lemma but for g':
    g'-fuel-irrel
        : (b b' : ℕ)
        → {n m : ℕ} → {a : Arity} → (t : ONT (suc n) m a)
        → (H : {x : ℕ} → x ∈∈ t → x < b)
        → (H' : {x : ℕ} → x ∈∈ t → x < b')
        → g' b t H ≡ g' b' t H'
    g'-fuel-irrel = ?

    -- g-surj and g'-surj are defined in mutual induction, quite like
    -- how g and g' are defined in mutual induction themselves.
    g-surj 
        : (t : ClosedTerms)
        → ({a : ClosedTerms} → a ⋤ t → g⁻¹-ex a)
        → g⁻¹-ex t
    g'-surj 
        : {n : ℕ} 
        → (t : IndTerms (suc n))
        → ({a : ClosedTerms} → a ⋤ t → g⁻¹-ex a)
        → g'⁻¹-ex t

    g-surj (mk-nullary-nw c) IH = (suc i , i , n<1+n i , eq)
        where
            t : CONT
            t = (0 , Nullary , ont-nullary c)
            i : ℕ
            i = ψ t
            open G-Impl i i (n<1+n i)
            g-cases-cong
                : (t t' : CONT)
                → (p : t ≡ t')
                → (q : t ≡ ψ⁻¹ i)
                → (q' : t' ≡ ψ⁻¹ i)
                → g-cases t q ≡ g-cases t' q'
            g-cases-cong _ _ refl refl refl = refl

            eq : g (suc i) i (n<1+n i) ≡ mk-nullary-nw c
            eq =
                begin 
                    g (suc i) i (n<1+n i)
                ≡⟨⟩
                    g-cases (ψ⁻¹ i) refl
                ≡⟨⟩
                    g-cases (ψ⁻¹ (ψ t)) refl
                ≡⟨ g-cases-cong (ψ⁻¹ (ψ t)) t (ψ⁻¹∘ψ≈id t) refl 
                                (sym $ ψ⁻¹∘ψ≈id t) 
                 ⟩
                    g-cases t (sym $ ψ⁻¹∘ψ≈id t)
                ≡⟨⟩
                    it-nullary c
                ∎
    g-surj (it-app t a) IH = (b , i , i<b , eq)
        where
            IH' : {x : ClosedTerms} → x ⋤ t → g⁻¹-ex x
            IH' {x} x⋤t = IH {x} (⋤-there-left t x a x⋤t)
            t-rec : g'⁻¹-ex t
            t-rec = g'-surj t IH'
            bₛ : ℕ
            bₛ = proj₁ t-rec
            m : ℕ
            m = proj₁ $ proj₂ t-rec
            s' : ONT 1 m Multiary
            s' = proj₁ $ proj₂ $ proj₂ t-rec
            Hₛ : {x : ℕ} → x ∈∈ s' → x < bₛ
            Hₛ = proj₁ $ proj₂ $ proj₂ $ proj₂ t-rec
            s-eq : g' bₛ s' Hₛ ≡ t
            s-eq = proj₂ $ proj₂ $ proj₂ $ proj₂ t-rec

            IHₐ : {x : ClosedTerms} → x ⋤ a → g⁻¹-ex x
            IHₐ {x} x⋤a = IH {x} (⋤-there-right t x a x⋤a)
            a-rec : g⁻¹-ex a
            a-rec = g-surj a IHₐ
            bₐ : ℕ
            bₐ = proj₁ a-rec
            a' : ℕ
            a' = proj₁ $  proj₂ a-rec
            a<bₐ : a' < bₐ 
            a<bₐ = proj₁ $ proj₂ $ proj₂ a-rec
            a-eq : g bₐ a' a<bₐ ≡ a
            a-eq = proj₂ $ proj₂ $ proj₂ a-rec 

            s : ONT 0 (suc m) Multiary
            s = ont-app s' a'
            s* : CONT
            s* = (suc m , Multiary , s)

            i : ℕ
            i = ψ s*
            b : ℕ
            b = suc i
            i<b : i < b
            i<b = n<1+n i
            open G-Impl i i i<b 

            -- #EXT: this lemma is duplicate with the previous case.
            g-cases-cong
                : (t t' : CONT)
                → (p : t ≡ t')
                → (q : t ≡ ψ⁻¹ i)
                → (q' : t' ≡ ψ⁻¹ i)
                → g-cases t q ≡ g-cases t' q'
            g-cases-cong _ _ refl refl refl = refl

            open G-Impl.G-Cases i i (n<1+n i) m s' a' (sym $ ψ⁻¹∘ψ≈id s*)
                using (H ; a<b)
            eq : g b i i<b ≡ it-app t a
            eq = 
                begin 
                    g b i i<b  
                ≡⟨⟩
                    g-cases (ψ⁻¹ i) refl
                ≡⟨⟩
                    g-cases ( ψ⁻¹ (ψ s*)) refl
                ≡⟨ g-cases-cong (ψ⁻¹ (ψ s*)) s* (ψ⁻¹∘ψ≈id s*) refl 
                                (sym $ ψ⁻¹∘ψ≈id s*) 
                 ⟩
                    g-cases s* (sym $ ψ⁻¹∘ψ≈id s*)
                ≡⟨⟩
                    g-cases (suc m , Multiary , ont-app s' a') 
                        (sym $ ψ⁻¹∘ψ≈id s*)
                ≡⟨⟩
                    it-app (g' i s' H) (g i a' a<b)
                ≡⟨ doubleCong it-app
                    (g'-fuel-irrel i bₛ s' H Hₛ)
                    (g-fuel-irrel i bₐ a' a<b a<bₐ)
                     ⟩
                    it-app (g' bₛ s' Hₛ) (g bₐ a' a<bₐ)
                ≡⟨ doubleCong it-app s-eq a-eq ⟩
                    it-app t a
                ∎

    g'-surj {n} (mk-multiary-nw c) IH = (0 , 0 , s , H , p)
        where
            s : ONT (suc n) 0 Multiary
            s = ont-multiary c
            H : {x : ℕ} → x ∈∈ s → x < 0
            H ()
            p : g' 0 s H ≡ (mk-multiary-nw c)
            p = refl
    g'-surj {n} (it-app t a) IH = (b , suc m , s , H , eq)
        where
            -- #EXT : The next block of definitions is exactly the same
            -- an in g-surj above. This can probably be refactored.
            IHₐ : {x : ClosedTerms} → x ⋤ a → g⁻¹-ex x
            IHₐ {x} x⋤a = IH {x} (⋤-there-right t x a x⋤a)
            a-rec : g⁻¹-ex a
            a-rec = g-surj a IHₐ
            bₐ : ℕ
            bₐ = proj₁ a-rec
            a' : ℕ
            a' = proj₁ $  proj₂ a-rec
            a<bₐ : a' < bₐ 
            a<bₐ = proj₁ $ proj₂ $ proj₂ a-rec
            a-eq : g bₐ a' a<bₐ ≡ a
            a-eq = proj₂ $ proj₂ $ proj₂ a-rec 

            -- #EXT : similar for the next block,
            -- except g-surj uses `1` instead of `suc (suc n)`.
            IH' : {x : ClosedTerms} → x ⋤ t → g⁻¹-ex x
            IH' {x} x⋤t = IH {x} (⋤-there-left t x a x⋤t)
            t-rec : g'⁻¹-ex t
            t-rec = g'-surj t IH'
            bₛ : ℕ
            bₛ = proj₁ t-rec
            m : ℕ
            m = proj₁ $ proj₂ t-rec
            s' : ONT (suc (suc n)) m Multiary
            s' = proj₁ $ proj₂ $ proj₂ t-rec
            Hₛ : {x : ℕ} → x ∈∈ s' → x < bₛ
            Hₛ = proj₁ $ proj₂ $ proj₂ $ proj₂ t-rec
            s-eq : g' bₛ s' Hₛ ≡ t
            s-eq = proj₂ $ proj₂ $ proj₂ $ proj₂ t-rec
 


            b : ℕ
            b = bₛ ⊔ bₐ -- This denotes (max bₛ bₐ)
            s : ONT (suc n) (suc m) Multiary
            s = ont-app s' a'
            H : {x : ℕ} → x ∈∈ s → x < b
            H {a'} (∈∈-here a' a' s' refl) = m<n⇒m<o⊔n bₛ a<bₐ 
            H {x} (∈∈-there x a' s' x∈∈s) = m<n⇒m<n⊔o bₐ (Hₛ {x} x∈∈s)

            open G'-Impl b s' a' H -- Imports H' and a<b from definition g'.

            eq : g' b s H ≡ it-app t a
            eq =
                begin 
                    g' b s H
                ≡⟨⟩
                    it-app (g' b s' H') (g b a' a<b)
                ≡⟨ doubleCong it-app
                    (g'-fuel-irrel b bₛ s' H' Hₛ)
                    (g-fuel-irrel b bₐ a' a<b a<bₐ)
                     ⟩
                    it-app (g' bₛ s' Hₛ) (g bₐ a' a<bₐ)
                ≡⟨ doubleCong it-app s-eq a-eq ⟩
                    it-app t a
                ∎

    g*-surj : Surjective _≡_ _≡_ g*
    g*-surj x = (i , f)
        where
            P : ClosedTerms → Set
            P = g⁻¹-ex 
            rec : ((t : ClosedTerms)
                → ({a : ClosedTerms} → a ⋤C t → P a)
                → P t
                )
            rec t IH = g-surj t IH'
                where
                    IH' : {a : ClosedTerms} → a ⋤ t → g⁻¹-ex a
                    IH' {a} a⋤t = IH a⋤t
            Q : (t : ClosedTerms) → g⁻¹-ex t
            Q = ⋤C-rec P rec
            
            b : ℕ
            b = proj₁ $ Q x

            i : ℕ
            i = proj₁ $ proj₂ $ Q x

            i<b : i < b
            i<b = proj₁ $ proj₂ $ proj₂ $ Q x

            f : {j : ℕ} → j ≡ i → g* j ≡ x
            f {i} refl = 
                begin 
                    g* i
                ≡⟨⟩
                    g (suc i) i (n<1+n i)
                ≡⟨ g-fuel-irrel (suc i) b i (n<1+n i) i<b ⟩
                    g b i i<b
                ≡⟨ proj₂ $ proj₂ $ proj₂ $ Q x ⟩
                    x
                ∎
          

    ----------------------------------------------------------------------------
    -- Injectivity of g*
    ----------------------------------------------------------------------------
    g*-inj : Injective _≡_ _≡_ g*
    g*-inj = ?
