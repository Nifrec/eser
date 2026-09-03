-- Module      : Eser.SigStream.NewTerms
-- Description : Two representations of terms in term algebra over a signature.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Different representations of the terms of the term algebra over a signature.
--
-- (1) 𝐍𝐮𝐦𝐓𝐞𝐫𝐦𝐬 (NT)
--  Terms represented by the index of the operation in the signature,
--  and for multiary operations, paired with a vector encoding their arguments,
--  whose length matches their arity.
--  The interpretation is as follows: Vec ℕ m gives the indices of the arguments
--  in an enumeration of all the terms. This interpretation is, of course, 
--  only useful when given an enumeration of all the terms,
--  such that the index assigned to a term is greater than the indices
--  assigned to its arguments.
--
-- (2) 𝐎𝐍𝐓 ("Open NumTerms")
--  Same as NumTerms, but now the arguments are not given as a vector,
--  but one-by-by via a constructor `appArg`.
--  Terms are indexed by the number of arguments they still need in order
--  to become closed. See below for more details.
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

open import Eser.Stdlib using (∸-suc)
open import Eser.Aux using (doubleSubst ; S[m∸Sn]≡m∸n ; _≈_)
open import Eser.Signature.Definitions
open import Eser.Card
open import Eser.Equivalences.Notation using (_≃_)
open import Eser.Equivalences.Properties using (mk≃')

module Eser.SigStream.NewTerms 
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

-- We index ONT by the arity of an term; it is notationally 
-- more convenient/concise to have `t : ONT n m Multiary`
-- than to carrying proofs of `OIsMultiary t` around.
data Arity : Set where
    Nullary : Arity
    Multiary : Arity

-- Open NumTerms: these don't take a vector of argument,
-- but arguments one by one. This is more convenient when doing
-- structural induction, since the termination checker does not
-- allow recursing on elements of a vector, but does allow recursing
-- on a single argument.
--
-- 1st index in ℕ encodes the number of arguments a term still needs.
-- Arguments can only be given in order from 'left to right'.
--
-- 2nd index in ℕ encodes the number of arguments already obtained.
-- This is, of course, just the difference between the arity of an operation
-- and the 1st index of the term, but working with ∸ is annoying;
-- the type checker can't do arithmetic and a lot of dependent substitutions
-- in vector length had to be made. Using this index simplifies that.
--
-- 3rd index is whether the top-level constructor is nullary or multiary.
data ONT : ℕ → ℕ → Arity → Set where
    ont-nullary : cardToSet μ → ONT 0 0 Nullary
    ont-multiary : (c : cardToSet ζ) → ONT (ar c) 0 Multiary
    ont-app : {n m : ℕ} → ONT (suc n) m Multiary → ℕ → ONT n (suc m) Multiary

ONTM : ℕ → ℕ → Set
ONTM n m = ONT n m Multiary

IsMultiary : NumTerms → Set
IsMultiary (nt-nullary _) = ⊥
IsMultiary (nt-multiary _ _) = ⊤

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
-- Subset of closed terms in ONT: the terms needing 0 more arguments.
-- They can have any arity and a corresponding number of arguments already
-- obtained.
CONT : Set
CONT = Σ[ m ∈ ℕ ] Σ[ a ∈ Arity ] ONT 0 m a

-- Get the operation index (in cardToSet ζ) of the top-level operation
-- of a term.
getOpIdx : {n m : ℕ} → (t : ONT n m Multiary) → cardToSet ζ
getOpIdx {n} {0} (ont-multiary c) = c
getOpIdx {n} {suc m} (ont-app t _) = getOpIdx t

-- The codomain of getOpIdx does not depend on the n and m in `ONT n m
-- Multiary`, so the output of getOpIdx is not influenced by a subst
-- on any of these indices.
getOpIdx-ignores-doubleSubst
    : {n n' m m' : ℕ}
    → (t : ONT n m Multiary)
    → (eqₙ : n ≡ n')
    → (eqₘ : m ≡ m')
    → getOpIdx (doubleSubst ONTM eqₙ eqₘ t) ≡ getOpIdx t
getOpIdx-ignores-doubleSubst t refl refl = refl

-- Same as above, but substituting only the first index.
getOpIdx-ignores-firstSubst
    : {n n' m : ℕ}
    → (t : ONT n m Multiary)
    → (eq : n ≡ n')
    → getOpIdx (subst (λ n → ONT n m Multiary) eq t) ≡ getOpIdx t
getOpIdx-ignores-firstSubst t refl = refl

ont-indices-invariant
    : {n m : ℕ}
    → (t : ONT n m Multiary)
    → n + m ≡ ar (getOpIdx t)
ont-indices-invariant {n} {ℕ.zero} (ont-multiary c) = +-identityʳ (ar c)
ont-indices-invariant {n} {suc m} (ont-app t a) = sym $ 
    begin 
        ar (getOpIdx (ont-app t a))
    ≡⟨⟩
        ar (getOpIdx t)
    ≡⟨ sym $ ont-indices-invariant t ⟩
        suc n + m
    ≡⟨⟩
        suc (n + m)
    ≡⟨ sym $ +-suc n m ⟩
        n + suc m
    ∎

-- A multiary term that needs 0 more arguments,
-- has already received exactly as many arguments as its arity.
getOpIdx-closed 
    : {m : ℕ}
    → (t : ONT 0 m Multiary)
    → m ≡ ar (getOpIdx t)
getOpIdx-closed {m} (ont-app t a) = ont-indices-invariant t 

getVec 
    : {n m : ℕ} 
    → (t : ONT n m Multiary) 
    → Vec ℕ m
getVec {n} {0} (ont-multiary c) = []
getVec {n} {suc m} (ont-app t a) = a ∷ (getVec t)

appArgs
    : {n m ℓ : ℕ}
    → (t : ONT n m Multiary)
    → Vec ℕ ℓ
    → ℓ ≤ n
    → ONT (n ∸ ℓ) (ℓ + m) Multiary
appArgs {n} {m} {ℕ.zero} t [] ℓ≤n = t
appArgs {n} {m} {suc ℓ} t (a ∷ as) 1+ℓ≤n = t''
    module AppArgs where
        ℓ≤n : ℓ ≤ n
        ℓ≤n = ≤-trans (n≤1+n ℓ) 1+ℓ≤n
        t' : ONT (n ∸ ℓ) (ℓ + m) Multiary
        t' = appArgs t as ℓ≤n
        eq : n ∸ ℓ ≡ suc (n ∸ (suc ℓ))
        eq = 
            begin 
                n ∸ ℓ
            ≡⟨⟩
                suc n ∸ suc ℓ
            ≡⟨ ∸-suc 1+ℓ≤n ⟩
                suc (n ∸ suc ℓ)
            ∎
        t'' : ONT (n ∸ suc ℓ) (suc ℓ + m) Multiary
        t'' = ont-app (subst (λ x → ONT x (ℓ + m) Multiary) eq t') a
            

k : CONT → NT
k (0 , Nullary , ont-nullary c) = nt-nullary c
k (m , Multiary , t) = nt-multiary (getOpIdx t) v
    module K-Impl where
        v : Vec ℕ (ar (getOpIdx t))
        v = subst (Vec ℕ) (getOpIdx-closed t) (getVec t)

w : NT → CONT
w (nt-nullary c) = (0 , Nullary , ont-nullary c)
w (nt-multiary c v) = (ar c , Multiary , t)
    module W-Impl where
        eq₁ : ar c ∸ ar c ≡ 0
        eq₁ = n∸n≡0 (ar c)
        eq₂ : ar c + 0 ≡ ar c
        eq₂ = +-identityʳ (ar c)
        t : ONT 0 (ar c) Multiary
        t = doubleSubst (λ n m → ONT n m Multiary) eq₁ eq₂ 
            (appArgs (ont-multiary c) v ≤-refl )
        

k∘w≈id : (k ∘ w) ≈ id
k∘w≈id (nt-nullary c) = refl
k∘w≈id (nt-multiary c v) = 
    begin 
        (k ∘ w) (nt-multiary c v)
    ≡⟨⟩
        k (ar c , Multiary , t)
    ≡⟨⟩
        nt-multiary (getOpIdx t) v'
    ≡⟨⟩
        f (getOpIdx t , v')
    ≡⟨ cong f $ subst-idx-in-pair v' c-eq ⟩
        f (c , subst (Vec ℕ) (cong ar c-eq) v')
    ≡⟨ cong (λ x → f (c , x)) (subst-subst {P = Vec ℕ} (getOpIdx-closed t) 
                                           {cong ar c-eq} )  ⟩
        f (c , subst (Vec ℕ) eq' (getVec t))
    ≡⟨ cong (λ x → f (c , x)) (lemma₁ eq' (getVec t)) ⟩
        f (c , getVec t)
    -- Use that t ≗ doubleSubst (λ n m → ONT n m Multiary) eq₁ eq₂ t') 
    ≡⟨ cong (λ x → f (c , x)) (lemma₂ eq₁ eq₂ t') ⟩
        f (c , subst (Vec ℕ) eq₂ (getVec t'))
    ≡⟨⟩
        nt-multiary c (subst (Vec ℕ) eq₂ (getVec t')) 
    ≡⟨ cong (λ v → nt-multiary c (subst (Vec ℕ) eq₂ v)) 
            (getVec-appArgs' c v (sym eq₂))  ⟩
        nt-multiary c (subst (Vec ℕ) eq₂ (subst (Vec ℕ) (sym eq₂) v))
    ≡⟨ cong (nt-multiary c) $ subst-subst-sym eq₂ ⟩
        nt-multiary c v
    ∎
    where
        open W-Impl c v
        open K-Impl (ar c) t renaming (v to v')
        f : Σ[ c ∈ cardToSet ζ ] Vec ℕ (ar c) → NT
        f (c , v) = nt-multiary c v
        t' = appArgs (ont-multiary c) v ≤-refl

        getOpIdx-appArgs
            : {c : cardToSet ζ}
            → {ℓ : ℕ}
            → (p : ℓ ≤ ar c)
            → (v : Vec ℕ ℓ)
            → getOpIdx (appArgs (ont-multiary c) v p) ≡ c
        getOpIdx-appArgs {c} {ℕ.zero} p [] = refl
        getOpIdx-appArgs {c} {suc ℓ} p (a ∷ as) = 
            begin 
                getOpIdx (appArgs (ont-multiary c) (a ∷ as) p)
            ≡⟨⟩
                getOpIdx 
                    (ont-app (subst (λ x → ONT x (ℓ + 0) Multiary) eq₀ t₀) a)
            ≡⟨⟩
                getOpIdx (subst (λ x → ONT x (ℓ + 0) Multiary) eq₀ t₀)
            ≡⟨ getOpIdx-ignores-firstSubst t₀ eq₀ ⟩
                getOpIdx t₀
            ≡⟨⟩
                getOpIdx (appArgs (ont-multiary c) as ℓ≤n)
            ≡⟨ getOpIdx-appArgs ℓ≤n as ⟩
               c 
            ∎
            where
                open AppArgs ℓ (ont-multiary c) a as p
                    renaming (t' to t₀ ; eq to eq₀)

        c-eq : getOpIdx t ≡ c
        c-eq = 
            begin 
                getOpIdx t
            ≡⟨ getOpIdx-ignores-doubleSubst t' eq₁ eq₂ ⟩
                getOpIdx t'
            ≡⟨ getOpIdx-appArgs {c} {ar c} ≤-refl v ⟩
                c
            ∎
            
        subst-idx-in-pair :
            {c c' : cardToSet ζ}
            → (v : Vec ℕ (ar c))
            → (eq : c ≡ c')
            → (c , v) ≡ (c' , subst (Vec ℕ) (cong ar eq) v)
        subst-idx-in-pair v refl = refl
        eq' : ar c ≡ ar c
        eq' =  trans (getOpIdx-closed t) (cong ar c-eq) 

        lemma₁
            : {a : ℕ}
            → (eq : a ≡ a)
            → (v : Vec ℕ a)
            → (subst (Vec ℕ) eq v) ≡ v
        lemma₁ refl v = refl

        lemma₂
            : {n n' m m' : ℕ}
            → (eqₙ : n ≡ n')
            → (eqₘ : m ≡ m')
            → (t : ONT n m Multiary)
            → (getVec (doubleSubst ONTM eqₙ eqₘ t)) 
                ≡ 
                subst (Vec ℕ) eqₘ (getVec t)
        lemma₂ refl refl t = refl


        getVec-ignores-n-subst
            : {n n' m : ℕ}
            → (t : ONT n m Multiary)
            → (eq : n ≡ n')
            → getVec (subst (λ x → ONT x m Multiary) eq t) ≡ getVec t
        getVec-ignores-n-subst t refl = refl

        getVec-appArgs-toList
            : (c : cardToSet ζ)
            → {ℓ : ℕ}
            → (p : ℓ ≤ ar c)
            → (v : Vec ℕ ℓ)
            → (eq : ℓ ≡ ℓ + 0)
            → toList (getVec (appArgs (ont-multiary c) v p))
                ≡
              toList v
        getVec-appArgs-toList c {ℕ.zero} p [] refl = refl
        getVec-appArgs-toList c {suc ℓ} p v@(a ∷ as) eq = List-eq
            where
                open AppArgs {ar c} {0} (ℓ) (ont-multiary c) a as p 
                    renaming (eq to eq'' ; t' to t₀)
                t''' = subst (λ x → ONT x (ℓ + 0) Multiary) eq'' t₀

                List-eq : 
                    toList (getVec (appArgs (ont-multiary c) v p)) ≡ toList v
                List-eq =
                    begin 
                        toList (getVec (appArgs (ont-multiary c) (a ∷ as) p))
                    ≡⟨⟩
                        toList (getVec (ont-app t''' a))
                    ≡⟨⟩
                        toList (a ∷ (getVec t'''))
                    ≡⟨⟩
                        a Data.List.∷ (toList (getVec t'''))
                    ≡⟨ cong (λ v → a Data.List.∷ (toList v)) 
                        $ getVec-ignores-n-subst t₀ eq'' ⟩
                        a Data.List.∷ (toList (getVec 
                            (appArgs (ont-multiary c) as ℓ≤n)))
                    ≡⟨ cong (a Data.List.∷_) 
                        $ getVec-appArgs-toList c ℓ≤n as (sym $ +-identityʳ ℓ) ⟩
                        a Data.List.∷ toList (as)
                    ≡⟨⟩
                        toList (a ∷ as)
                    ∎
                    

        getVec-appArgs'
            : (c : cardToSet ζ)
            → (v : Vec ℕ (ar c))
            → (eq : ar c ≡ ar c + 0)
            → getVec (appArgs (ont-multiary c) v ≤-refl) 
                ≡
              subst (Vec ℕ) eq v
        getVec-appArgs' c v eq = H₂
            where
                H : toList( getVec (appArgs (ont-multiary c) v ≤-refl))
                    ≡ 
                    toList (v)
                H = getVec-appArgs-toList c ≤-refl v (sym $ +-identityʳ (ar c)) 
                H₂ : getVec (appArgs (ont-multiary c) v ≤-refl)
                    ≡ 
                    subst (Vec ℕ) eq v
                H₂ = trans  
                    (sym $ 
                    toList-injective eq 
                        v 
                        (getVec (appArgs (ont-multiary c) v ≤-refl)) (sym H)
                    )
                    (sym $ subst-is-cast eq v)

            

    

w∘k≈id : (w ∘ k) ≈ id
w∘k≈id (0 , Nullary , ont-nullary c) = refl
w∘k≈id (suc m , Multiary , t) = ?
