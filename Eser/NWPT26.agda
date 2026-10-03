-- Module      : Eser.NFPT26
-- Description : Façade file giving pointers to the library
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- This file gives pointers to the definitions and theorems
-- mentioned in the NWPT2026 abstract.

-- The --safe option makes sure that Agda throws an error when cheating
-- (e.g., leaving proofs unfinished, introducing axioms, etc.)
{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)
open import Data.Nat hiding (_/_)
open import Data.Product
open import Data.Sum
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Eser.NWPT26 where

--------------------------------------------------------------------------------
-- Notation
--------------------------------------------------------------------------------
-- Equivalences
-- _≃_ is defined as _↔_ from the standard library, but I found `_↔_`
-- misleading, it looks more like the weaker condition of functions both ways,
-- and also define it as such in Eser.Aux.
open import Eser.Equivalences.Notation using (_≃_)
open import Eser.Aux using (_↔_)

-- Homotopy
-- f ≈ g if f and g give the same output on each input
-- (for all f , g : A → B, we have f ≈ g iff (a : A) → f a ≡ g a).
open import Eser.Aux using (_≈_)

--------------------------------------------------------------------------------
-- §1 Quotients over enumerable types
--------------------------------------------------------------------------------
-- Definitions of decidable equivalence relations and normal-form functions:
open import Eser.EqRel.Definitions using (NFFun) renaming (DecEquiv to EqRel)

-- Conversions between decidable equivalence relations
-- and normal-form functions.
open import Eser.EqRel.Conversions using (RelToFun ; FunToRel)

-- Theorem 1.1 is split into two lemmas in the implementation:
open import Eser.EqRel.Correspondences renaming 
    ( FRFHomot to theorem-1-part-1 
    ; RFRHomot to theorem-1-part-2 )

--------------------------------------------------------------------------------
-- Quotients
--------------------------------------------------------------------------------
-- The definition of a quotient is exactly as in the paper:
open import Eser.Quotients using (_/_)
_ : {A : Set} → (A ≃ ℕ) → NFFun → Set
_ = _/_

-- That the quotients defined above have all the properties
-- of 'definable quotients' (as defined in Nuo Li (2014)
-- are proven in the following module:
open Eser.Quotients.Properties 
    using ([_] ; sound ; emb ; complete ; stable ; effective ; qind)
    renaming (quotLift to lift
             ; deceq to quotients-have-decidable-equalities
             ; ≡-irrel to quotients-have-proof-irrelevant-equalities
             )

--------------------------------------------------------------------------------
-- §2 Enumerating inductive types
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Encoding of ℕ∞ (cardinalities)
--------------------------------------------------------------------------------
-- Brief showcase of how we can encode sets of different cartinalities
-- as terms of type ℕ∞.
-- * suc∞ is just ℕ.suc on finite numbers and the identity on ∞
-- * cardToSet c is always a subset of ℕ, so we can inject back into the natural
--      numbers. This is done with `cardToℕ`.
open import Eser.Card using (ℕ∞ ; cardToSet ; suc∞ ; cardToℕ)
open ℕ∞ -- Gives constructors `fin : ℕ → ℕ∞` and `∞ : ℕ∞`.

variable 
    n : ℕ

card-example-0 : cardToSet (fin 0) ≡ ⊥
card-example-0 = refl
card-example-Sn : cardToSet (fin (ℕ.suc n)) ≡ Fin (ℕ.suc n)
card-example-Sn = refl
card-example-∞ : cardToSet ∞ ≡ ℕ
card-example-∞ = refl

--------------------------------------------------------------------------------
-- Signatures
--------------------------------------------------------------------------------

-- Definition of a Signature.
-- (Note: this module also defines the deprecated 'OpenTerms' representation of
-- term algebras, used for a previous enumeration algorithm).
open import Eser.Signature.Definitions using (Signature ; arity) 

-- Current definition of the term algebra and enumeration algorithm
-- (`sigenum` works for all signatures, `inductiveCase` for signatures with at
-- least one nullary and at least multiary constructor; this is the special case
-- described in the abstract).
open import Eser.NewSigStream using (Term ; sigenum)
    renaming (inductiveCase to theorem-2)
open Eser.NewSigStream.InductiveCaseImpl using (code-term ; decode-term)
open import Eser.NatCoding using ( code-pair' ; code-sum' ; code-vec 
                                 ; decode-pair' ; decode-sum' ; decode-vec)
    
--------------------------------------------------------------------------------
-- §3 Building normalisation functions
--------------------------------------------------------------------------------
-- An "extension sequence" (Exence) is a sequence of NFRestrs that are
-- extensions of each other.
open import Eser.Filters.Base using (NFRestr ; NFS ; Exence)

-- Theorem 3.1 is split into two lemmas in the implementation:
open import Eser.Filters.Conversions.NFFunToExence
    using (restrict+ ; combine) -- The functions NFFun ↔ Exence
    renaming ( theo-combine∘restrict+ to theorem-3-part-1
             ; theo-restrict+∘combine to theorem-3-part-2)

--------------------------------------------------------------------------------
-- Filters
--------------------------------------------------------------------------------
-- While still work-in-progress, many properties of filters
-- are already established in submodules of Eser.Filter.
open import Eser.Filters.Base using (Filter)

-- We implemented congruence as a filter and proved that the filter corresponds
-- to the 'classical' defintion of congruence.
import Eser.Filters.Congruence
open Eser.Filters.Congruence.ReplaceResp
    renaming ( ReplaceRespLocal to congruence-filter
             ; ReplaceRespGlobal to congruence-classical
             ; theo-ReplaceResp-left to correspondence-part-1
             ; theo-ReplaceResp-right to correspondence-part-2 )

