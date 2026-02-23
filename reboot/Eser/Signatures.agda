-- Module      : Eser.Signatures
-- Description : Tools for enumerating term algebras over signatures
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties using (¬-not ; not-¬)
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product
--open import Relation.Binary.Structures
open import Data.Fin hiding (_≤_ ; _≤?_ ; _<_ ; _>_ ; _+_)
open import Data.List
open import Data.Vec hiding (restrict)
open import Induction.WellFounded
open import Data.Nat.Induction using (<-Rec)
open import Data.Nat.Properties using (≤-refl ; n<1+n ; <-trans ; m<n⇒0<n) --; ≤-trans ; ≤-<-trans ; n≤0⇒n≡0 
--                                       ; n≤1+n ; m≤n⇒m<n∨m≡n ; _≤?_ ; ≰⇒≥)
--open import Data.Fin.Properties using (toℕ<n)
--open import Relation.Nullary -- Needed for with-abstractions on decidable ≡.
open import Function hiding (_↔_)

--open import Eser.Logic using (elimCaseLeft ; elimCaseRight)
--open import Relation.Nullary
--open ≡-Reasoning
--open import Data.Nat.Properties
--open import Data.Fin
--open import Data.Fin.Properties
--open import Data.Fin.Induction
--open import Data.Empty
--open import Data.List
--open import Data.List.Relation.Unary.AllPairs using (AllPairs)
--open import Data.List.Relation.Unary.All using (All)
--open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix)
--open import Data.List.Membership.Propositional using (_∈_ ; _∉_ )
--open import Data.List.Membership.Propositional.Properties using (∈-lookup)
--open import Data.List.Relation.Unary.Any using (Any)

open import Eser.Definitions using (_≈_)

module Eser.Signatures where

indices : {A : Set} → List A → Set
indices {A} L = Fin (Data.List.length L)
 
-- Equivalence between two types.
-- The stdlib uses an overly general definition
-- what requires also showing `n ≈₁ m → (f n) ≈₂ (f m)`
-- given setoids (N, ≈₁) and (M, ≈₂).
-- We just use propositional equality _≡_ for both the domain and codomain,
record HomotEquivalence (Left Right : Set) : Set where 
    field
        LR : Left → Right
        RL : Right → Left
        homotLRL : (RL ∘ LR) ≈ id
        homotRLR : (LR ∘ RL) ≈ id

_≃_ : Set → Set → Set
A ≃ B = HomotEquivalence A B

--------------------------------------------------------------------------------
-- Signature representations
--------------------------------------------------------------------------------
-- Very terse representation of signatures.
-- Constructors either have arity 0 or suc a
-- (for inductive arguments of their own type;
-- for each multiary constructor with arity `suc a`,
-- the value `a` should be stored in the List ℕ).
-- Constructors either take one external argument from ℕ,
-- or no external arguments.
record TerseSignature : Set where
   field 
        pure-nullary : ℕ
        ℕ-nullary    : ℕ
        pure-multiary : List ℕ
        ℕ-multiary : List ℕ
open TerseSignature

data ConstrKind : Set where
    c-pure-nullary   : ConstrKind
    c-ℕ-nullary      : ConstrKind
    c-pure-multiary  : ConstrKind
    c-ℕ-multiary     : ConstrKind

-- Lookup the arity of a non-nullary constructor in a signature.
arity 
    : (S : TerseSignature) 
    → (indices (pure-multiary S)) ⊎ (indices (ℕ-multiary S))
    → ℕ
--arity _ c-pure-nullary = 0
--arity _ c-ℕ-nullary = 0
arity S (inj₁ idx) = ℕ.suc (Data.List.lookup (pure-multiary S) idx )
arity S (inj₂ idx) = ℕ.suc (Data.List.lookup (ℕ-multiary S)    idx )

-- Term algebra over a TerseSignature.
data TerseFreeTerms (S : TerseSignature) : Set where
    mk-pure-nullary : Fin (pure-nullary S) → TerseFreeTerms S
    mk-ℕ-nullary : Fin (ℕ-nullary S) → ℕ → TerseFreeTerms S
    mk-pure-multiary 
        : (c : indices (pure-multiary S)) 
        → (Vec (TerseFreeTerms S) (ℕ.suc (Data.List.lookup (pure-multiary S) c)))
        → TerseFreeTerms S 
    mk-ℕ-multiary 
        : (c : indices (pure-multiary S)) 
        → (Vec (TerseFreeTerms S) (ℕ.suc (Data.List.lookup (pure-multiary S) c)))
        → ℕ
        → TerseFreeTerms S 

--------------------------------------------------------------------------------
-- Mergings
--
-- The number of ways to merge two lists,
-- of length n and m respectively, into one list,
-- without changing the relative order of the elements in each list.
-- E.g. the mergings of [a a'] with [b b'] are
-- [a a' b b']
-- [a b a' b']
-- [a b b' a']
-- [b a a' b']
-- [b a b' a']
-- [b b' a a']
--------------------------------------------------------------------------------
-- Compute number of ways to merge two lists.
numMergings : ℕ → ℕ → ℕ
-- If one list is empty, there is only one choice.
numMergings 0 m = 1
numMergings n 0 = 1
-- When mergings a∷α with b∷β, there are two options:
-- (1) Either put a as the first element of the merging.
--      Then it remains to merge α with b∷β, so NM(n, m+1) mergings possible.
-- (2) Xor put a after b. Then it remains to merge a∷α with β.
--      So NM(n+1, m) mergings possible.
-- Clearly those two cases are mutually exclusive since only one of a and b can
-- be put first.
numMergings (suc n) (suc m) = numMergings n (ℕ.suc m) + numMergings (ℕ.suc n) m


-- Inductive type explicitly encoding all possible mergings.
-- Note how it corresponds to the explanation of the recursive case of
-- numMergings.
data Merging {A : Set} {B : Set} : List A → List B → Set where
    -- Also captures the case Merging [] []
    BetaTriv : (α : List A) → Merging α []
    -- Does NOT capture the case Merging [] []
    AlphaTriv : (b : B) → (β : List B) → Merging [] (b ∷ β)
    -- Take a merging γ of α and β and extend it to (a ∷ γ).
    AFirst : (a : A) → (α : List A) → (β : List B) → Merging α β
        → Merging (a ∷ α) β
    -- Take a merging γ of α and β and extend it to (b ∷ γ).
    BFirst : (b : B) → (α : List A) → (β : List B) → Merging α β
        → Merging α (b ∷ β)

-- Same as `Merging`, but the arguments are now vectors.
VMerging 
    : {A B : Set}
    → {n m : ℕ} 
    → (α : Vec A n) 
    → (β : Vec B m) 
    → Set
VMerging α β = Merging (toList α) (toList β)

MergingFinTheo
    : {A B : Set}
    → (n m : ℕ) 
    → (α : Vec A n) 
    → (β : Vec B m) 
    → VMerging α β ≃ Fin (numMergings n m)
MergingFinTheo n m α β = ?
    
--------------------------------------------------------------------------------
-- Representation of term algebras that reveals much more about the choices
-- one needs to make when constructing a term.
--------------------------------------------------------------------------------

-- `<-Rec` in Data.Nat.Induction should do the same, but it confused me how to
-- apply it.
<-rec : {ℓ : Level} → (P : ℕ → Set ℓ)
    → ((n : ℕ) → ((m : ℕ) → (m < n) → P m) → P n)
    → (n : ℕ) → P n
<-rec {ℓ} P rec n = lemma n (Data.Nat.Induction.<-wellFounded n)
    where
        lemma : (n : ℕ) → Acc _<_ n → P n
        lemma n (acc Accn) = rec n (λ m → λ m<n → lemma m (Accn m<n) )
        
0<n⇒pred[n]<n
    : {n : ℕ}
    → 0 < n
    → Data.Nat.pred n < n
0<n⇒pred[n]<n {0} ()
0<n⇒pred[n]<n {suc n} 0<n = s≤s (≤-refl {n})

ssn<m⇒n<m
    : {n m : ℕ}
    → ℕ.suc (ℕ.suc n) < m
    → n < m
ssn<m⇒n<m {n} {ℕ.suc 0} (s≤s ()) 
ssn<m⇒n<m {n} {ℕ.suc (ℕ.suc m)} SSn<SSm = 
    let n<m : n < m
        n<m = s<s⁻¹ (s<s⁻¹ SSn<SSm)
    in
    let m<SSm : m < ℕ.suc (ℕ.suc m)
        m<SSm = <-trans (n<1+n m) (n<1+n (ℕ.suc m))
    in
    <-trans n<m m<SSm


TeleTerms : (S : TerseSignature) → Set
TeleTerms S = Σ[ i ∈ ℕ ] ( round S i )
    where
        kindCaseDistinction : (S : TerseSignature) 
            → (n : ℕ) 
            → ConstrKind 
            → ((m : ℕ) → (m < n) → Set)
            → Set
        round : TerseSignature → ℕ → Set
        round S = <-rec (λ i → Set) 
            (λ i → λ rec → 
            Σ[ ck ∈ ConstrKind ] kindCaseDistinction S i ck rec)

        kindCaseDistinction S i c-pure-nullary rec
            = Σ[ c ∈ Fin (pure-nullary S) ] i ≡ 0
        kindCaseDistinction S i c-ℕ-nullary rec
            = Σ[ c ∈ Fin (ℕ-nullary S) ] Σ[ n ∈ ℕ ] (n < i)
            --^ n < i : value n may only be used in round (suc n).
            -- Note: this forces i > 0, 
            -- so we do not need to store this explicitly.
        kindCaseDistinction S i c-pure-multiary rec 
            = 
            Σ[ hᵢ ∈ i > 0 ] 
            --^ To avoid an α in round 0 constisting of
            -- round 0 elements.
            Σ[ c ∈ indices (pure-multiary S) ]
            Σ[ m ∈ Fin (arity S (inj₁ c)) ]
            -- α is a vector whose length is in the range [1, ..., m]
            -- of terms of round (i ∸ 1). We use Well-Founded recursion to
            -- define `round (i - 1)`.
            Σ[ lenα ∈ Fin (toℕ m) ]
            Σ[ α ∈ Vec 
                    (rec (Data.Nat.pred i) (0<n⇒pred[n]<n hᵢ) ) -- round (i - 1)
                    (ℕ.suc (toℕ lenα)) -- A length in [1, ..., m]
            ] 
            -- β is a vector of length m - |α| (so |α| + |β| ≡ m)
            -- with elements from `round 0 ⊎ round 1 ⊎ ... ⊎ round (i ∸ 2).
            -- Note that α and β do not share elements,
            -- and their union always contains at least one element
            -- from round (i ∸ 1). β can be empty.
            Σ[ β ∈ Vec 
                (Σ[ j ∈ ℕ ] Σ[ hⱼ ∈ ℕ.suc (ℕ.suc j) < i ] rec j (ssn<m⇒n<m hⱼ)) 
                ((toℕ m) ∸ Data.Vec.length α) 
            ]
            VMerging α β
        -- Same as previous case, but now also an n < i,
        -- which in turn makes hᵢ redundent (it guarrantees i > 0
        -- otherwise no such n exists).
        kindCaseDistinction S i c-ℕ-multiary rec
            = 
            Σ[ n ∈ ℕ ] 
            Σ[ hₙ ∈ n < i ] 
            Σ[ c ∈ indices (ℕ-multiary S) ]
            Σ[ m ∈ Fin (arity S (inj₂ c)) ]
            Σ[ lenα ∈ Fin (toℕ m) ]
            Σ[ α ∈ Vec 
                (rec (Data.Nat.pred i) (0<n⇒pred[n]<n (m<n⇒0<n {n} {i} hₙ)) ) 
                (ℕ.suc (toℕ lenα)) 
            ]
            Σ[ β ∈ Vec 
                (Σ[ j ∈ ℕ ] Σ[ hⱼ ∈ ℕ.suc (ℕ.suc j) < i ] rec j (ssn<m⇒n<m hⱼ))
                ((toℕ m) ∸ Data.Vec.length α)
            ]
            VMerging α β

--------------------------------------------------------------------------------
-- Correspondence theorems:
--
-- 1. TerseFreeTerms and TeleTerms are in bijection, i.e., represent the same
--  term algebra (up to renaming elements).
-- 2. All nested Σs in TeleTerms are finite sets, only the outermost quantifies
--  over ℕ. That is, for all S and i, we have: round S i ≃ Fin k for some k.
-- 3. Corollary of 1. and 2.: TerseFreeTerms ≃ TeleTerms ≃ ℕ
--------------------------------------------------------------------------------

FreeTerms≃TeleTerms 
    : (S : TerseSignature)
    → TerseFreeTerms S ≃ TeleTerms S
FreeTerms≃TeleTerms S = ?
