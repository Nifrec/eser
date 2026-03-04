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
open import Data.Fin hiding (_≤_ ; _≤?_ ; _<_ ; _>_ ; _+_ )
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
open import Induction

open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
    renaming (wellFounded to TransWellFounded)
open import Eser.Signature.Definitions
open import Eser.Definitions using (indices)

module Eser.Signature.Subterm  where

-- #TODO: remove
module FailedTerseFreeTermsVersion {S : TerseSignature} where
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

--------------------------------------------------------------------------------
-- Retry: partial terms. Now we can define height and well-foundedness of the
-- subterm relation.
--------------------------------------------------------------------------------

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

AllPartialTerms : (S : TerseSignature) → Set
AllPartialTerms S = Σ[ n ∈ ℕ ](PartialTerms S n)

ClosedTerms : (S : TerseSignature) → Set
ClosedTerms S = PartialTerms S 0

-- #TODO: move to own file. Maybe contribute to stdlib?
module IndexHeterogeneousTransClosure 
    {I : Set}
    {A : {I} → Set}
    where

    -- Generalisation of `TransClosure` from 
    -- Relation.Binary.Construct.Closure.Transitive
    -- to relations that are heretogeneous in the indices of the underlying
    -- type.
    --
    -- Don't confuse this with the "indexed relations"
    -- in the stdlib in Relation.Binary.Indexed.Homogeneous,
    -- There the related elements are of type `I → Set`, and `A ≗ I → Set`.
    -- In this file we have a very different situation:
    -- the base type instead is `A : I → Set`, so the related elements
    -- live in `A i`, each for some fixed `i`.
    data ITransClosure (_∼_ : {i j : I} → A {i} → A {j} → Set) 
                      : {i j : I} → A {i} → A {j} → Set where
        direct 
            : {i j : I} 
            → {a : A {i}} 
            → {b : A {j}} 
            → (a ∼ b) 
            → ITransClosure _∼_ a b
        composed --^ a∼b and b∼⁺c then a∼⁺c.
            : {i j k : I} 
            → {a : A {i}} 
            → {b : A {j}} 
            → {c : A {k}}
            → a ∼ b
            → ITransClosure _∼_ b c
            → ITransClosure _∼_ a c

    -- Predicate that an index-heterogeneous relation is transitive.
    ITransitive : (_∼_ : {i j : I} → A {i} → A {j} → Set) → Set
    ITransitive _∼_ = 
              {i j k : I}
            → {a : A {i}} 
            → {b : A {j}} 
            → {c : A {k}}
            → a ∼ b
            → b ∼ c
            → a ∼ c

    -- Theorem that the indexed-transitive-closure is actually transitive.
    ITransClosureTransitivity
        : (_∼_ : {i j : I} → A {i} → A {j} → Set) 
        → ITransitive (ITransClosure _∼_)
    ITransClosureTransitivity _∼_ {a = a} {b = b} {c = c} (direct a∼b) b∼⁺c 
        = composed a∼b b∼⁺c
    ITransClosureTransitivity _∼_ {a = a} {b = b} {c = c} 
        (composed {a = a} {b = z} {c = b} a∼z z∼⁺b) b∼⁺c = 
            let z∼⁺c = ITransClosureTransitivity _∼_ z∼⁺b b∼⁺c
            in
            composed a∼z z∼⁺c

    IWfRec : (_∼_ : {i j : I} → A {i} → A {j} → Set) 
           → RecStruct (Σ[ i ∈ I ](A {i})) 0ℓ 0ℓ
    -- {i : I} (x : A i)
    IWfRec _∼_ P (i , x) = (j : I) → (y : A {j}) → y ∼ x → P (j , y)

    data IAcc (_∼_ : {i j : I} → A {i} → A {j} → Set) (i,x : Σ[ i ∈ I ](A {i}) )
              : Set where
        iacc : (rs : IWfRec _∼_ (IAcc _∼_) i,x) → IAcc _∼_ i,x

    --data IAcc (_∼_ : {i j : I} → A {i} → A {j} → Set) {i : I} (x : A {i}) : Set where
    --    iacc : (rs : IWfRec _∼_ (IAcc _∼_) {i} x) → IAcc _∼_ {i} x

    -- Generalised 'accessibility' predicate.
    --
    --IAcc 
    --    : (_∼_ : {i j : I} → A {i} → A {j} → Set) 
    --    → {i : I} 
    --    → A i
    --    → Set
    --IAcc _∼_ {i} x = {j : I} → {y : A j} → y ∼ x → IAcc _∼_ {j} y

    -- The ITransClosure preserves Well-Foundedness.
    ITransWellFounded
        : (_∼_ : {i j : I} → A {i} → A {j} → Set) 
        → WellFounded _∼_
        → WellFounded (ITransClosure _∼_)
    ITransWellFounded = ?

open IndexHeterogeneousTransClosure

module _ {S : TerseSignature} where
    -- Is-argument-of-relation: 
    -- `a « t` iff t is build as a contructor with (among others) argument a.
    -- a is an arument of (giveArg t a₁) if it is the last 
    -- argument (a₁) or an earlier argument, i.e., an arg of t.
    -- This relation also concerns non-closed-terms, it was easier to define it
    -- this way.
    -- The relation is defined as a heterogeneous relation between PartialTerms
    -- of possibly different indices. The simpler homogeneous definition
    -- commented out below is rejected by the termination checker:
    --_«_ : Rel (AllPartialTerms S) 0ℓ
    --a « (0 , mk-pure-nullary _)           = ⊥
    --a « (0 , mk-ℕ-nullary _ _)            = ⊥
    --a « (suc n , argless-pure-multiary _) = ⊥
    --a « (suc n , argless-ℕ-multiary _ _)  = ⊥
    --a « (n , giveArg t a₁)            = (a ≡ (0 , a₁)) ⊎ (a « (ℕ.suc n , t))
    _«_ : {n m : ℕ} → (PartialTerms S n) → (PartialTerms S m) → Set
    a « mk-pure-nullary _           = ⊥
    a « mk-ℕ-nullary _ _            = ⊥
    a « argless-pure-multiary _     = ⊥
    a « argless-ℕ-multiary _ _      = ⊥
    _«_ {0} {m} a (giveArg t a₁)    = (a ≡ a₁) ⊎ (a « t)
    _«_ {suc n} {m} a _             = _ 
    --^ a is not closed, so not a valid argument to anything!

    -- The 'subterm' relation is the transitive closure of _«_.
    -- We cannot use `TransClosure` from 
    -- Relation.Binary.Construct.Closure.Transitive,
    -- because our relation is heterogenerous in the ℕ-indices.
    _«*_ : {n m : ℕ} → (PartialTerms S n) → (PartialTerms S m) → Set
    _«*_ {n} {m} = ITransClosure _«_ {n} {m}

    «AllAcc : {n : ℕ} → (t : PartialTerms S n) → IAcc (_«_ {n}) (n , t)
    «AllAcc {0} (mk-pure-nullary x) = iacc λ {j y ()}
    «AllAcc {0} (mk-ℕ-nullary x x₁) = iacc λ {j y ()}
    «AllAcc {n} (argless-pure-multiary c) = iacc λ { j y () }
    «AllAcc {n} (argless-ℕ-multiary c x) = iacc λ { j y () }
    «AllAcc {0} t@(giveArg t' a) = 
        iacc ?
        where
            f : (j : ℕ) (y : PartialTerms S ℕ.zero) → y « giveArg t' a → IAcc _«_ (j , y)
            f 0 a (inj₁ refl) = «AllAcc {0} a
            f (suc j) a (inj₁ refl) = {! «AllAcc {ℕ.suc j} a !}
               --^ Wait this does not make sense. Now a : PartialTerms S 0
               -- and a : PartialTerms S (ℕ.suc j). That is not possible!
            f j y (inj₂ y«t') =
                        let rec = «AllAcc {ℕ.suc 0} t'
                        in -- TODO: eliminate this and apply it to y«t':
                        {!   !}  
    «AllAcc {suc n} t@(giveArg t' a) = iacc λ { j y x → {! !} }

    _«σ_ : Rel (AllPartialTerms S) 0ℓ
    (j , a) «σ (i , t) = a « t

    «σ-WellFounded : WellFounded _«σ_
    «σ-WellFounded t = acc f
        where
            f : {y : AllPartialTerms S} → y «σ t → Acc _«σ_ y
            f {y} (y«t) = ? -- Can't recurse here 
                            -- cuz can't expose y as building block of t

    --«-WellFounded : WellFounded _«_
    --«-WellFounded t = acc f
    --    where
    --        f : {k : PartialTerms S} → k « t → Acc _«_ k
    --        f {k} k∈Lt = ?

    --«*-WellFounded : WellFounded _«*_
    --«*-WellFounded = ITransWellFounded _«_ {! «-WellFounded !}
