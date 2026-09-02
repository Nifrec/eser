-- Module      : Eser.SigStream.NewTerms
-- Description : Two representations of terms in term algebra over a signature.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Different representations of the terms of the term algebra over a signature.
--
-- (1) 𝐍𝐮𝐦𝐓𝐞𝐫𝐦
--  Terms represented by the index of the operation in the signature,
--  and for multiary operations, paired with a vector encoding their arguments,
--  whose length matches their arity.
--  The interpretation is as follows: Vec ℕ m gives the indices of the arguments
--  in an enumeration of all the terms. This interpretation is, of course, 
--  only useful when given an enumeration of all the terms,
--  such that the index assigned to a term is greater than the indices
--  assigned to its arguments.
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

todo : ?
todo = {! update docstring above, rename from `NewTerms` to `Terms`, etc. !}

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

-- #TODO: those things are outdated.
--    OIsMultiary : {n m : ℕ} → ONT n → Set
--    OIsMultiary (ont-nullary _) = ⊥
--    OIsMultiary (ont-multiary _) = ⊤
--    OIsMultiary (ont-app _ _) = ⊤

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

-- A multiary term that needs 0 more arguments,
-- has already received exactly as many arguments as its arity.
getOpIdx-closed 
    : {m : ℕ}
    → (t : ONT 0 m Multiary)
    → m ≡ ar (getOpIdx t)
getOpIdx-closed {m} (ont-app t a) = {! TODO: lemma that ar c ≡ n + m !}

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
    where
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
        --nt-multiary (getOpIdx $ 
        --            (subst (Vec ℕ) (getOpIdx-closed t) (getVec t))
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
            (getVec-appArgs c v (sym eq₂))  ⟩
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
        c-eq : getOpIdx t ≡ c
        c-eq = ?
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

        ONTM : ℕ → ℕ → Set
        ONTM n m = ONT n m Multiary

        lemma₂
            : {n n' m m' : ℕ}
            → (eqₙ : n ≡ n')
            → (eqₘ : m ≡ m')
            → (t : ONT n m Multiary)
            → (getVec (doubleSubst ONTM eqₙ eqₘ t)) ≡ subst (Vec ℕ) eqₘ (getVec t)
        lemma₂ refl refl t = refl

        getVec-appArgs
            : (c : cardToSet ζ)
            → (v : Vec ℕ (ar c))
            → (eq : ar c ≡ ar c + 0)
            → getVec (appArgs (ont-multiary c) v ≤-refl) 
                ≡
              subst (Vec ℕ) eq v
        getVec-appArgs c v eq = ?


    

w∘k≈id : (w ∘ k) ≈ id
w∘k≈id (0 , Nullary , ont-nullary c) = refl
w∘k≈id (suc m , Multiary , t) = ?

--getOpIdx-lemma 
--    : {n : ℕ} 
--    → (t : ONT (suc n)) 
--    → (a : ℕ)
--    → {p : OIsMultiary t}
--    → getOpIdx (ont-app t a) ≡ getOpIdx t {p}
--getOpIdx-lemma {n} (ont-multiary c) a {p} = refl
--getOpIdx-lemma {n} (ont-app t a') a {p} = refl

--ont-app-isMultiary
--    : {n : ℕ}
--    → (t : ONT (suc n))
--    → OIsMultiary t
--ont-app-isMultiary (ont-multiary c) = tt
--ont-app-isMultiary (ont-app t a) = tt

--ont-idx-lemma
--    : {n : ℕ} 
--    → (t : ONT n) 
--    → {p : OIsMultiary t} 
--    → n ≤ (ar $ getOpIdx t {p})
--ont-idx-lemma {n} (ont-multiary c) {p} = ≤-refl
--ont-idx-lemma {n} (ont-app t a) {p} = ≤-trans (n≤1+n n) IH'
--    where
--        IH : suc n ≤ (ar $ getOpIdx t {ont-app-isMultiary t})
--        IH = ont-idx-lemma {suc n} t        
--        IH' : suc n ≤ (ar $ getOpIdx (ont-app t a))
--        IH' = subst (λ x → suc n ≤ ar x) (sym $ getOpIdx-lemma t a) IH

--getVec 
--    : {n : ℕ} 
--    → (t : ONT n) 
--    → {p : OIsMultiary t} 
--    → Vec ℕ ((ar $ getOpIdx t {p}) ∸ n)
--getVec {n} (ont-multiary c) = subst (Vec ℕ) (sym $ n∸n≡0 $ ar c) []
--getVec {n} (ont-app t a) = ans
--    where
--        p : OIsMultiary t
--        p = ont-app-isMultiary t
--        rec : Vec ℕ ((ar $ getOpIdx t {p}) ∸ suc n)
--        rec = getVec t
--        rec' : Vec ℕ (suc $ (ar $ getOpIdx t {p}) ∸ suc n)
--        rec' = a ∷ (getVec t)
--        m : ℕ
--        m = ar $ getOpIdx t {p}
--        m-eq : m ≡ (ar $ getOpIdx (ont-app t a))
--        m-eq = sym $ cong ar $ getOpIdx-lemma t a
--        ans : Vec ℕ ((ar $ getOpIdx (ont-app t a)) ∸ n)
--        ans = subst (Vec ℕ) 
--            (subst (λ x → suc (m ∸ suc n) ≡ x ∸ n) 
--                m-eq (S[m∸Sn]≡m∸n {m} {n} $ ont-idx-lemma t)
--            ) rec'

--pile-args
--    : {n : ℕ}
--    → (t : ONT n)
--    → Vec ℕ n
--    → ONT 0
--pile-args-rec
--    : {n m : ℕ}
--    → (t : ONT n)
--    → m ≤ n
--    → Vec ℕ m
--    → ONT (n ∸ m)
--pile-args {n} t v = subst ONT (n∸n≡0 n) $ pile-args-rec {n} {n} t (≤-refl) v

--pile-args-rec {n} {0} t _ [] = t
--pile-args-rec {suc n} {suc m} t Sm≤Sn (a ∷ as) = ont-app rec' a
--    module PileArgsRec where
--        rec : ONT (suc n ∸ m)
--        rec = pile-args-rec {suc n} {m} t (≤-trans (n≤1+n m) Sm≤Sn) as
--        rec' : ONT (suc (n ∸ m))
--        rec' = subst ONT (∸-suc (s≤s⁻¹ Sm≤Sn)) rec
        

----------------------------------------------------------------------------------
---- k and w are each other's inverse.
----------------------------------------------------------------------------------
--rm-subst-idx
--    : {n m : ℕ} 
--    → (t : ONT n) 
--    → (eq : n ≡ m)
--    → {p : OIsMultiary t}
--    → {q : OIsMultiary (subst ONT eq t)}
--    → getOpIdx (subst ONT eq t) {q} ≡ getOpIdx t {p}
--rm-subst-idx (ont-multiary _) refl {tt} {tt} = refl
--rm-subst-idx (ont-app _ _) refl {tt} {tt} = refl

--rm-subst-OIsMultiary
--    : {n m : ℕ} 
--    → (t : ONT n) 
--    → (eq : n ≡ m)
--    → OIsMultiary (subst ONT eq t) ≡ OIsMultiary t
--rm-subst-OIsMultiary (ont-nullary _) refl = refl
--rm-subst-OIsMultiary (ont-multiary _) refl = refl
--rm-subst-OIsMultiary (ont-app _ _) refl = refl

--pile-args-rec-isMultiary
--    : (c : cardToSet ζ)
--    → (m : ℕ)
--    → (p : m ≤ ar c)
--    → (v : Vec ℕ m)
--    → OIsMultiary (pile-args-rec (ont-multiary c) p v)
--pile-args-rec-isMultiary c ℕ.zero p [] = tt
--pile-args-rec-isMultiary c (suc m) p (x ∷ xs) = tt

--pile-args-isMultiary
--    : (c : cardToSet ζ)
--    → (v : Vec ℕ (ar c))
--    → OIsMultiary (pile-args (ont-multiary c) v)
--pile-args-isMultiary c v = 
--    subst (λ x → x) (sym eq) (pile-args-rec-isMultiary c (ar c) ≤-refl v)
--    where
--        n : ℕ
--        n = ar c
--        t : ONT n
--        t = ont-multiary c
--        eq : OIsMultiary (pile-args (ont-multiary c) v)
--            ≡
--            OIsMultiary (pile-args-rec (ont-multiary c) ≤-refl v)
--        eq = 
--            begin 
--                OIsMultiary (pile-args t v)    
--            ≡⟨⟩
--               OIsMultiary (subst ONT (n∸n≡0 n) $ pile-args-rec {n} {n} t (≤-refl) v) 
--            ≡⟨  rm-subst-OIsMultiary 
--                (pile-args-rec {n} {n} t (≤-refl) v) (n∸n≡0 n) ⟩
--               OIsMultiary (pile-args-rec {n} {n} t (≤-refl) v) 
--            ∎
            


--pile-args-rec-idx
--    : (c : cardToSet ζ)
--    → (m : ℕ)
--    → (p : m ≤ ar c)
--    → (v : Vec ℕ m)
--    → getOpIdx (pile-args-rec (ont-multiary c) p v) 
--        {pile-args-rec-isMultiary c m p v} ≡ c
--pile-args-rec-idx c ℕ.zero _ [] = refl
--pile-args-rec-idx c (suc m) Sm≤n v@(x ∷ xs) = 
--    begin 
--       getOpIdx (pile-args-rec (ont-multiary c) Sm≤n (x ∷ xs)) {q}
--    ≡⟨⟩
--        getOpIdx (ont-app rec' x)
--    ≡⟨ getOpIdx-lemma rec' x ⟩
--        getOpIdx (rec') {subst-presv-multiary rec eq {q'} }
--    ≡⟨⟩
--        getOpIdx (subst ONT eq rec)
--    ≡⟨ rm-subst-idx rec eq ⟩
--        getOpIdx rec
--    ≡⟨ pile-args-rec-idx c m m≤n xs ⟩
--        c
--    ∎
--        where
--            open PileArgsRec (S c) (m) (ont-multiary c) Sm≤n x xs
--            eq = (∸-suc (s≤s⁻¹ Sm≤n))
--            subst-presv-multiary
--                : {n m : ℕ} 
--                → (t : ONT n) 
--                → (eq : n ≡ m)
--                → {p : OIsMultiary t}
--                → OIsMultiary (subst ONT eq t)
--            subst-presv-multiary (ont-multiary _) refl = tt
--            subst-presv-multiary (ont-app _ _) refl = tt


--            m≤n : m ≤ ar c
--            m≤n = (≤-trans (n≤1+n m) Sm≤n)
--            q = pile-args-rec-isMultiary c (suc m) Sm≤n v 
--            q' = pile-args-rec-isMultiary c m m≤n xs 
    

--pile-args-idx
--    : (c : cardToSet ζ)
--    → (v : Vec ℕ (ar c))
--    → getOpIdx (pile-args (ont-multiary c) v) 
--        {pile-args-isMultiary c v}
--        ≡ c
--pile-args-idx c v = 
--    begin 
--        getOpIdx (pile-args (ont-multiary c) v) 
--    ≡⟨⟩
--        getOpIdx (subst ONT (n∸n≡0 n) $ pile-args-rec {n} {n} t (≤-refl) v)
--    ≡⟨ rm-subst-idx (pile-args-rec {n} {n} t (≤-refl) v) (n∸n≡0 n) ⟩ 
--        getOpIdx (pile-args-rec {n} {n} t (≤-refl) v)
--    ≡⟨  pile-args-rec-idx c (ar c) ≤-refl v ⟩
--        c
--    ∎
--    where
--        n : ℕ
--        n = ar c
--        t : ONT n
--        t = ont-multiary c

--A : Set
--A = Σ[ n ∈ ℕ ](Vec ℕ n)

--pile-args-vec
--    : (c : cardToSet ζ)
--    → (v : Vec ℕ (ar c))
--    → {m : ℕ}
--    → _≡_ {A = A}
--        (ar (getOpIdx (pile-args (ont-multiary c) v) {pile-args-isMultiary c v}) ∸ 0 , 
--             getVec (pile-args (ont-multiary c) v) {pile-args-isMultiary c v})
--        (ar c , v)
--pile-args-vec = ?

--pile-args-rec-vec
--    : (c : cardToSet ζ)
--    → (m : ℕ)
--    → (p : m ≤ ar c)
--    → (v : Vec ℕ m)
--    → _≡_ {A = A}
--        (
--            ar (getOpIdx (pile-args-rec (ont-multiary c) p v)
--                {pile-args-rec-isMultiary c m p v})
--            ∸ (ar c ∸ m)
--        , 
--            getVec (pile-args-rec (ont-multiary c) p v) 
--            {pile-args-rec-isMultiary c m p v}
--        )
--        (m , v)
--pile-args-rec-vec c ℕ.zero p [] = {! !}
--pile-args-rec-vec c (suc m) p v = {! !}

--k∘w≈id : (k ∘ w) ≈ id
--k∘w≈id (nt-nullary c) = refl
--k∘w≈id (nt-multiary c v) = 
--    begin 
--        (k ∘ w) (nt-multiary c v) 
--    ≡⟨⟩
--        k (pile-args (ont-multiary c) v)
--    ≡⟨ {! TODO: lemma that k-pile-args always is the nt-multiary case... Maybe prove in general for OIsMultiary inputs? !} ⟩
--        nt-multiary (getOpIdx t {q}) (getVec t) 
--    ≡⟨⟩
--        f (getOpIdx t , getVec t) 
--    ≡⟨ cong f eq ⟩
--        f (c , v)
--    ≡⟨⟩
--        nt-multiary c v
--    ∎
--    where
--        t : ONT 0
--        t = pile-args (ont-multiary c) v
--        q : OIsMultiary t
--        q = pile-args-isMultiary c v
--        idx-eq : (getOpIdx t) ≡ c
--        idx-eq = pile-args-idx c v
--        B : Set
--        B = Σ[ c ∈ cardToSet ζ ] (Vec ℕ (ar c))
--        f : B → NT
--        f (c , v) = nt-multiary c v

--        eq : (getOpIdx t , getVec t) ≡ (c , v)
--        eq = ?

--        --vec-eq : getVec t ≡ v
--        --vec-eq = ?
    
