-- Module      : Eser.Signature.Definitions
-- Description : The well-founded is-arg and is-subterm relations
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Given a signature with a constructor c with arity ≥ 1,
-- a term t constructed by applying arguments to c
-- has at least one argument t', which is in some sense 'smaller'
-- denoted `t' « t`.
-- t' itself may have arguments, and so may these arguments in turn;
-- all these are 'subterms' of t, i.e. all t'' s.t. `t'' «* t`
-- where _«*_ the transitive closure of _«_.
--
-- Both _«_ and _«*_ are well-founded, which is convenient when
-- defining recursive functions on terms.
-- Proving well-foundedness requires recursion itself,
-- leading to a chicken-egg problem.
-- Luckily, we can implement the recursion in the well-foundedness proof
-- also based on the 'height' of a term, which means we can use WF-recursion on
-- (ℕ, <) instead.

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
open import Data.Vec.Membership.Propositional using (_∈_ ; _∉_ )
open import Data.List.Extrema.Nat using (max)

open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
    renaming (wellFounded to TransWellFounded)
open import Eser.Signature.Definitions
open import Eser.Definitions using (indices)

module Eser.Signature.Subterm {S : TerseSignature} where

-- `a « t` iff t is build as a contructor with (among others) argument a.
_«_ : Rel (TerseFreeTerms S) 0ℓ
a « mk-pure-nullary _ = ⊥           --^ Nullary terms have no argument.
a « mk-ℕ-nullary _ _ = ⊥            --^ Nullary terms have no argument.
a « mk-pure-multiary c L = a ∈ L    --^ L is the list of arguments.
a « mk-ℕ-multiary c L _ = a ∈ L     --^ L is the list of arguments.

-- The 'subterm' relation is the transitive closure of _«_.
_«*_ : Rel (TerseFreeTerms S) 0ℓ
_«*_ = TransClosure _«_ 

«-WellFounded : WellFounded _«_
«-WellFounded t = acc f
    where
        f : {k : TerseFreeTerms S} → k « t → Acc _«_ k
        f {k} k∈Lt = ?

«*-WellFounded : WellFounded _«*_
«*-WellFounded = TransWellFounded _«_ «-WellFounded

open TerseSignature

-- PartialTerms n are the partially constructed terms
-- that still need n inductive arguments.
-- PartialTerms 0 are exactly the closed terms of the term algebra.
data PartialTerms (S : TerseSignature) : ℕ →  Set where
    mk-pure-nullary : Fin (pure-nullary S) → PartialTerms S 0
    mk-ℕ-nullary : Fin (ℕ-nullary S) → ℕ → PartialTerms S 0
    argless-pure-multiary 
        : (c : indices (pure-multiary S)) 
        → PartialTerms S (ℕ.suc (Data.List.lookup (pure-multiary S) c))
    argless-ℕ-multiary 
        : (c : indices (pure-multiary S)) 
        → ℕ
        → PartialTerms S (ℕ.suc (Data.List.lookup (pure-multiary S) c))
    giveArg
        : {n : ℕ}
        → PartialTerms S (ℕ.suc n) --^ Term still needing at least 1 more arg.
        → PartialTerms S 0         --^ Next argument to give: a closed term.
        → PartialTerms S n

-- The height of a term is 0 for nullary constructors and otherwise
-- 1 + (max height of an argument).
height : TerseFreeTerms S → ℕ
height (mk-pure-nullary _)    = 0
height (mk-ℕ-nullary _ _)     = 0
--height (mk-pure-multiary c L) = ℕ.suc (max 0 (map height (toList L)))
height (mk-pure-multiary c (x ∷ L)) = ℕ.suc (height x)
height (mk-ℕ-multiary c (x ∷ L) _) = ℕ.suc (height x)
--height (mk-ℕ-multiary c L _)  = ℕ.suc (max 0 (map height (toList L)))


--termsAcc : {h : ℕ} → (t : TerseFreeTerms S) → (height t ≡ h) → Acc _«_ t
--termsAcc {h} t height≡h = acc ?
