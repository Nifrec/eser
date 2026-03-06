-- Module      : Eser.Signature.Definitions
-- Description : Tools for enumerating term algebras over signatures
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- The 'RoundedTerms' implementation replaces the older 'TeleTerms'
-- implementation.
open import Data.List.Relation.Unary.Any using (here ; there)
open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties using (¬-not ; not-¬)
open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Unit
open import Data.Empty
open import Relation.Unary using (Decidable)
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Data.Fin hiding (_≤_ ; _≤?_ ; _<_ ; _>_ ; _+_)
open import Data.List
open import Data.List.Properties using (map-∘ ; length-map)
open import Data.Vec hiding (restrict ; length ; map)
open import Induction.WellFounded
open import Data.Nat.Induction using (<-Rec)
open import Data.Nat.Properties using (≤-refl ; n<1+n ; <-trans ; m<n⇒0<n ; <⇒≢
    ; ≤-trans ) 
open import Data.Vec.Properties using (length-toList) 
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Function hiding (_↔_)
open ≡-Reasoning
open import Data.List.Membership.Propositional using (_∈_ ; _∉_ )
open import Data.List.Membership.Propositional.Properties using (∈-length)
open import Data.List.Extrema.Nat

open import Eser.Logic using (elimCaseRight)
open import Eser.Definitions using (_≈_ ; indices ; _≃_ ; HomotEquivalence)
open HomotEquivalence
open import Eser.Mergings using (Merging ; unmergeMax ; UnmergeMaxOutp 
    ; mergelenLemma ; VMerging ; compileMerging ; compileMembership
    ; compileMembershipMapCongr)
open import Eser.ListMaxima using (nonemptyThenHasMax)

module Eser.Signature.Definitions where

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
getArity 
    : (S : TerseSignature) 
    → (indices (pure-multiary S)) ⊎ (indices (ℕ-multiary S))
    → ℕ
getArity S (inj₁ idx) = ℕ.suc (Data.List.lookup (pure-multiary S) idx )
getArity S (inj₂ idx) = ℕ.suc (Data.List.lookup (ℕ-multiary S)    idx )

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

RoundedTerms : TerseSignature → Set
data Round (S : TerseSignature) : ℕ → Set
RoundedTerms S = Σ[ n ∈ ℕ ] (Round S n)

data Round S where
    -- Nullary constructors without external-ℕ-argument.
    pure-atomic 
        : Fin (pure-nullary S)      --^ Constructor identity.
        → Round S 0
    -- Nullary constructors with exernal-ℕ-argument.
    ℕ-atomic 
        : (n : ℕ)                   --^ Round index (minus one).
        → Fin (ℕ-nullary S)         --^ Constructor identity.
        → Fin (ℕ.suc n)             --^ External ℕ-argument in [0, ..., n].
        → Round S (ℕ.suc n)
    -- Multiary constructor without external-ℕ-argument.
    pure-inductive
        : (n : ℕ)                   
            --^ Round index (minus one).
        → (i : indices (pure-multiary S)) 
            --^ Constructor identity.
        → (m : Fin (getArity S (inj₁ i))) 
            --^ Number (minus one) of arguments from previous round.
        → (α : Vec (Round S n) (ℕ.suc (toℕ m)))
            --^ Actual arguments from previous round (never empty!).
        → (β : Vec (Σ[ ℓ ∈ ℕ ] ((ℓ < n) × Round S ℓ)) 
                   (getArity S (inj₁ i) ∸ (ℕ.suc (toℕ m))))
            --^ Remaining arguments from at least two rounds ago.
        → VMerging α β
            --^ Interleaving of arguments in α and β
        → Round S (ℕ.suc n)
    -- Multiary constructor with external-ℕ-argument that is at least two
    -- smaller than the current round. These MUST take at least one inductive
    -- argument from the previous, like in pure-multiary.
    -- Combinations of this constructor with only arguments from 
    -- at least two rounds ago have already been covered by previous rounds!
    ℕ-inductive-prevRoundArg
        : (n : ℕ)                   
            --^ Round index (minus one).
        → (i : indices (ℕ-multiary S)) 
            --^ Constructor identity.
        → (m : Fin (getArity S (inj₂ i))) 
            --^ Number (minus one) of arguments from previous round.
        → (α : Vec (Round S n) (ℕ.suc (toℕ m)))
            --^ Actual arguments from previous round (never empty!).
        → (β : Vec (Σ[ ℓ ∈ ℕ ] ((ℓ < n) × Round S ℓ)) 
                   (getArity S (inj₂ i) ∸ (ℕ.suc (toℕ m))))
            --^ Remaining arguments from at least two rounds ago.
        → VMerging α β
            --^ Interleaving of arguments in α and β.
        → Fin n
            --^ External-ℕ-argument in [0, ..., n-1].
        → Round S (ℕ.suc n)
    -- Multiary constructor for round suc n whose external-ℕ-argument is n.
    -- We have not seen this constructor combined with external argument n
    -- before in any previous round, so we must also consider all combinations
    -- of this constructor, n, and any arguments from previous rounds;
    -- including combinations that do not take any argument from the previous
    -- round.
    -- That the external-ℕ-argument is n is implicit.
    ℕ-inductive-maxℕArg
        : (n : ℕ)                   
            --^ Round index (minus one), n is also the external-ℕ-argument.
        → (i : indices (ℕ-multiary S)) 
            --^ Constructor identity.
        → (lenα : Fin (ℕ.suc (getArity S (inj₂ i))))
            --^ Number of arguments from previous round,
            --  in range [0, ..., arity].
        → (α : Vec (Round S n) (toℕ lenα))
            --^ Actual arguments from previous round (can be empty).
        → (β : Vec (Σ[ ℓ ∈ ℕ ] ((ℓ < n) × Round S ℓ)) 
                   (getArity S (inj₂ i) ∸ (toℕ lenα)))
            --^ Remaining arguments from at least two rounds ago.
        → VMerging α β
            --^ Interleaving of arguments in α and β.
        → Round S (ℕ.suc n)
