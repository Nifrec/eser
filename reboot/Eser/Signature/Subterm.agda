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
-- #TODO: remark all only proven for Set₀ but can probably be generalised.
module IndexHeterogeneousTransClosure 
    {I : Set}
    {A : I → Set}
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
    data ITransClosure (_∼_ : {i j : I} → A i → A j → Set) 
                      : {i j : I} → A i → A j → Set where
        direct 
            : {i j : I} 
            → {a : A i} 
            → {b : A j} 
            → (a ∼ b) 
            → ITransClosure _∼_ a b
        composed --^ a∼b and b∼⁺c then a∼⁺c.
            : {i j k : I} 
            → {a : A i} 
            → {b : A j} 
            → {c : A k}
            → a ∼ b
            → ITransClosure _∼_ b c
            → ITransClosure _∼_ a c

    -- Predicate that an index-heterogeneous relation is transitive.
    ITransitive : (_∼_ : {i j : I} → A i → A j → Set) → Set
    ITransitive _∼_ = 
              {i j k : I}
            → {a : A i} 
            → {b : A j} 
            → {c : A k}
            → a ∼ b
            → b ∼ c
            → a ∼ c

    -- Theorem that the indexed-transitive-closure is actually transitive.
    ITransClosureTransitivity
        : (_∼_ : {i j : I} → A i → A j → Set) 
        → ITransitive (ITransClosure _∼_)
    ITransClosureTransitivity _∼_ {a = a} {b = b} {c = c} (direct a∼b) b∼⁺c 
        = composed a∼b b∼⁺c
    ITransClosureTransitivity _∼_ {a = a} {b = b} {c = c} 
        (composed {a = a} {b = z} {c = b} a∼z z∼⁺b) b∼⁺c = 
            let z∼⁺c = ITransClosureTransitivity _∼_ z∼⁺b b∼⁺c
            in
            composed a∼z z∼⁺c

    -- The predecessor-structure over the union of `_∼_ i j` 
    -- over all indices i and j.
    IWFRec : (_∼_ : {i j : I} → A i → A j → Set) 
           → RecStruct (Σ[ i ∈ I ](A i)) 0ℓ 0ℓ
    -- {i : I} (x : A i)
    IWFRec _∼_ P (i , x) = (j : I) → (y : A j) → y ∼ x → P (j , y)

open IndexHeterogeneousTransClosure

-- x : A i is accessible (from i) if all y s.t. y ∼ x are also accessible (from
-- j), for *any* index j s.t. y : A j.
data IAcc {I : Set} {A : I → Set} 
    (_∼_ : {i j : I} → A i → A j → Set) (i,x : Σ[ i ∈ I ](A i) ) : Set where
    iacc : (rs : IWFRec _∼_ (IAcc _∼_) i,x) → IAcc _∼_ i,x

IWellFounded : {I : Set} {A : I → Set} (_∼_ : {i j : I} → A i → A j → Set) → Set
IWellFounded {I} {A} _∼_ = {i : I} → (x : A i) → IAcc {I} {A} _∼_ (i , x)

-- Now we mimick Induction.WellFounded of the stdlib, but then for IWellFounded.
-- For the moment only for level 0ℓ, which is all I need.
module ISome {I : Set} {A : I → Set} {_∼_ : {i j : I} → A i → A j → Set} where
    iWFRecBuilder : SubsetRecursorBuilder (IAcc {I} {A} _∼_) (IWFRec _∼_)
    iWFRecBuilder P f x (iacc rs) j y y∼x = 
        -- * P is a predicate on Σ[i∈I](Ai).
        -- * f proves that `Rec P ⊆' P`, i.e., if Py for all y∼x then Px.
        -- The goal is to prove that (IAcc _∼_) ⊆' (Rec P),
        -- i.e., that if x is accessible then P holds for all y s.t. y∼x.
        -- By definition of accessibility of x, it follows from y∼x
        -- that also y is accessible.
        -- A recursive call on the accessibility of y (to iWFRecBuilder) 
        -- then proves that `Rec P y` holds, i.e, that Pz holds for all z∼y.
        let RecPY : (k : I) → (z : A k) → z ∼ y → P (k , z)
            RecPY = iWFRecBuilder P f (j , y) (rs j y y∼x)
        in
        -- We then input that to f to prove Py, which was to be shown.
        f (j , y) RecPY
        -- Why does the termination checker not complain?
        -- Because `rs` is a strictly smaller building block that `iacc rs`,
        -- and we are not applying rs to any function
        -- (instead we apply something TO rs, intuitively taking something out
        -- of it, instead of building something on top of it!)
    
    -- Now we get an induction principle that can be used to show a precidate P
    -- holds on all accessible elements. 
    -- Intuitively it requires showing 
    -- {i : I} → (x : A i) → ({j : I} → (y : A j) → y ∼ x → P y) → P x
    -- to conclude the 'P holds on all accessible elements':
    -- {i : I} → (x : A i) → Acc _∼_ x → P x.
    -- The actual implementation uses tuples
    -- Σ[ i ∈ I ](A i) instead of {i : I} → (x : A i).
    iWFRec : SubsetRecursor (IAcc {I} {A} _∼_) (IWFRec _∼_)
    iWFRec = subsetBuild iWFRecBuilder

-- As in the standard library, the previous induction principle can be
-- strengthened to *All points in Σ[ i ∈ I ](A i)* if all points are accessible.
-- Accessibility of all points (IWellFounded) is an argument to the module.
-- This is a fairly trivial corollary of ISome, which proves an induction
-- principle for "all accessible elements", which in this context are just all
-- elements.
module IAll 
    {I : Set} 
    {A : I → Set} 
    {_∼_ : {i j : I} → A i → A j → Set}
    (IWF : IWellFounded {I} {A} _∼_)
    where
    iWFRecBuilder : RecursorBuilder (IWFRec _∼_)
    iWFRecBuilder P f (i , x) = ISome.iWFRecBuilder P f (i , x) (IWF x) 
    --
    -- Now we get an induction principle that can be used to show a precidate P
    -- holds UNIVERSALLY.
    -- Intuitively it requires showing 
    -- {i : I} → (x : A i) → ({j : I} → (y : A j) → y ∼ x → P y) → P x
    -- to conclude the 'P holds on all elements':
    -- {i : I} → (x : A i) → P x.
    -- The actual implementation uses tuples
    -- Σ[ i ∈ I ](A i) instead of {i : I} → (x : A i).
    iWFRec : Recursor (IWFRec _∼_)
    iWFRec = build iWFRecBuilder

-- If x is accessible and y∼x then y is accessible.
elimIAcc
    : {I : Set} 
    → {A : I → Set} 
    → {_∼_ : {i j : I} → A i → A j → Set} 
    → {i : I}
    → {x : A i}
    → IAcc {I} {A} _∼_ (i , x)
    → {j : I}
    → {y : A j}
    → y ∼ x
    → IAcc {I} {A} _∼_ (j , y)
elimIAcc (iacc rs) {j = j} {y = y} y∼x = rs j y y∼x

-- If x is _∼_ accessible then x is also accessible in the transitive closure of
-- _∼_.
IAccImplIAccTransClosure
    : {I : Set} 
    → {A : I → Set} 
    → (_∼_ : {i j : I} → A i → A j → Set) 
    → {i : I}
    → (x : A i)
    → IAcc {I} {A} _∼_ (i , x)
    → IAcc {I} {A} (ITransClosure {I} {A} _∼_) (i , x)
IAccImplIAccTransClosure {I} {A} _∼_ {i} x (iacc rs) = iacc f
    where
        f 
            : (j : I) 
            → (y : A j)
            → ITransClosure {I} {A} _∼_ y x 
            → IAcc {I} {A} (ITransClosure {I} {A} _∼_) (j , y)
        f j y (direct y∼x) = 
            let yIAcc : IAcc {I} {A} _∼_ (j , y)
                yIAcc = rs j y y∼x
            in
            IAccImplIAccTransClosure _∼_ y yIAcc
        f j y (composed {j = k} {b = z} y∼z z∼⁺x) = 
            let zIAccTrans : IAcc {I} {A} (ITransClosure {I} {A} _∼_) (k , z)
                zIAccTrans = f k z z∼⁺x
            in
            let y∼⁺z : ITransClosure {I} {A} _∼_ y z
                y∼⁺z = direct y∼z
            in
            elimIAcc zIAccTrans y∼⁺z

-- The ITransClosure preserves IWell-Foundedness.
-- Obviously, since the definition of accessibility requires all
-- predecessors of x under the transitive closure to be accessible.
-- Hence accessibility of _«_ implies accessibility of _«*_.
ITransIWellFounded
    : {I : Set} 
    → {A : I → Set} 
    → (_∼_ : {i j : I} → A i → A j → Set) 
    → IWellFounded {I} {A} _∼_
    → IWellFounded {I} {A} (ITransClosure {I} {A} _∼_)
ITransIWellFounded {I} {A} _∼_ IWF {i} x 
    = IAccImplIAccTransClosure {I} {A} _∼_ {i} x (IWF x)

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
    _«_ {suc n} {m} a _             = ⊥ 
    --^ a is not closed, so not a valid argument to anything!

    -- The 'subterm' relation is the transitive closure of _«_.
    -- We cannot use `TransClosure` from 
    -- Relation.Binary.Construct.Closure.Transitive,
    -- because our relation is heterogenerous in the ℕ-indices.
    _«+_ : {n m : ℕ} → (PartialTerms S n) → (PartialTerms S m) → Set
    _«+_ {n} {m} = ITransClosure _«_ {n} {m}

    «AllAcc 
        : {n : ℕ} 
        → (t : PartialTerms S n) 
        → IAcc {ℕ} {PartialTerms S} (_«_) (n , t)
    «AllAcc {0} (mk-pure-nullary x) = iacc λ {j y ()}
    «AllAcc {0} (mk-ℕ-nullary x x₁) = iacc λ {j y ()}
    «AllAcc {n} (argless-pure-multiary c) = iacc λ { j y () }
    «AllAcc {n} (argless-ℕ-multiary c x) = iacc λ { j y () }
    «AllAcc {n} t@(giveArg t' a) = iacc f
        where
            f : (j : ℕ) → (y : PartialTerms S j) → y « giveArg t' a → IAcc _«_ (j , y)
            f ℕ.zero y (inj₁ refl) = «AllAcc {0} a
            f ℕ.zero y (inj₂ y«t') = 
                let IAccT' : IAcc _«_ (ℕ.suc n , t')
                    IAccT' = «AllAcc {ℕ.suc n} t'
                in
                elimIAcc IAccT' y«t'
            f (ℕ.suc j) y ()

    «-WellFounded : IWellFounded {ℕ} {PartialTerms S} _«_
    «-WellFounded t = «AllAcc t

    «+-WellFounded : IWellFounded {ℕ} {PartialTerms S} _«+_
    «+-WellFounded = ITransIWellFounded _«_ «-WellFounded
