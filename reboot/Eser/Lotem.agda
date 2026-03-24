-- Module      : Eser.Lih
-- Description : Outline of the "Later is heavier -- Open Terms" strategy
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- This file sketches the "Later is heaver" (Lih) approach,
-- the variant using OpenTerms and giveArg (Lotem : L'ih - O'penT'E'rms M'ix);
-- see the deprecated `Lih.adga` for the approach using vectors
-- to represent the arguments to closed terms (which doesn't represent open
-- terms at all).
--
-- Lih has its own distinctive reprentation of signatures (finitary W-types)
-- and a proof outline for showing term algebras are equivalent to ℕ.
-- This open-terms-version of Lih also has a distinctive representation of terms
-- over a signature: Agda-constructors can only apply one argument at a time to
-- a signature-constructor.
-- Ideas developed in March 2026,
-- after the 11 March discussion with supervisors pointed out the previous
-- approach was overly complicated and that things could have been done more
-- general.

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)
open import Data.Vec 

open import Function
open import Relation.Binary.Reasoning.Syntax

open import StreamGrids.Card

open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties

module Eser.Lotem where

postulate IGotProofOnPaper : {Whatever : Set} → Whatever
postulate StillTODO : {Whatever : Set} → Whatever

--------------------------------------------------------------------------------
-- New encoding of signatures
--
-- Let ℕ∞ = ℕ  ∪ {∞}.
-- A signature consists of two things:
-- 1. A number of nullary constructors, μ.
--      The collection of nullary constructors is either `Fin μ` if μ ∈ ℕ
--      xor ℕ if μ = ∞.
-- 2. A number of multiary constructors, together with a function that
--      assigns to each such constructor the number-of-arguments-minus-one.
--      Again, the set of constructors is either `Fin ζ` xor ℕ.
--
-- Particularities of this representation:
-- * No external ℕ-arguments are needed, since we can unfold constructors
--      that take a ℕ-argument into ℕ-many distinct constructors, one for each
--      argument. Note that, with this trick, we can unfold any constructor
--      taking a finite number of arguments from finite and/or enumerable sets
--      into at most ℕ-many constructors.
-- * Constructors are not sorted by their arity.
--      This allows to have arbitrary many constructors of each arity,
--      and also to have no upper bound on the maximum arity.
-- * We can ealisy recognise empty and finite term algebras:
--      * Signature 0 ζ has an empty term algebra.
--      * Signature (suc∞ μ) 0 has a finite term algebra.
--      * Signature (suc∞ μ) (suc ζ) has a term algebra equivalent to ℕ.
--------------------------------------------------------------------------------

Signature : ℕ∞ → ℕ∞ → Set
Signature μ ζ = cardToSet ζ → ℕ

-- Lookup the arity of a constructor in a signature.
arity : {μ ζ : ℕ∞} → {S : Signature μ ζ} → (c : cardToSet ζ) → ℕ
arity {S = S} c = ℕ.suc (S c)

--------------------------------------------------------------------------------
-- Closed terms over a signature
--
-- Closed terms are either a nullary constructor or a multiary constructor
-- of arity m with a vector of m terms as arguments.
--
-- We annotate every term with a 'weight' to make enumerating terms easier.
-- Note that the weights pose no constraints on term formation,
-- they are just calculated after giving arguments to constructors.
-- So it is still easy to see that we can create the same terms 
-- as without using weights.
-- Rules of weights: the weight of a term is the sum of:
--      * 1 
--      * the index of the constructor (in cardToSet μ or cardToSet ζ resp.).
--      * the sum of the weights of the inductive arguments.
-- Adding the '1' ensures that all constructors (even unary ones) 
-- are always heavier than any of their arguments.
--
-- The original 'Lih.agda' file used only closed terms,
-- and stored inductive arguments as a vector (whose length matches the
-- arity of the used constructor); this was to be compared against the
-- alternative of a function `args : arity → Terms S`:
-- * If two vectors have equal elements, then they are equal.
--      For functions this is not the case, at least not without assuming
--      function extensionality, and this would allow to build 'distinct'
--      terms with the same arguments.
-- * Because of the previous point, proving the isomorphism from Terms to ℕ
--      is easier.
-- * Functions allow to define a subterm relation, since the termination checker
--      is OK with evaluating a function, but not with the _∈_ relation on
--      vectors. On the subterm relation one can define well-founded recursion.
--      However, this all is not necessary, since we can still do 
--      well-founded (ℕ , <) recursion on the weights; subterms have lower
--      weights anyway!
--
-- In hindsight, vectors were not so convenient during enumeration because
-- counting the number of possible vectors of lighter arguments, whose sum
-- of weights is the current term's weight, is a lot of work to implement in
-- Agda (it is possible, since <-rec on the weights allows to show the arguments
-- come from finite sets, and then some combinatorics, etc.
-- But the number of data conversions, arithmetic rewrites and other things that
-- that thorny is Agda, just wasn't fun).
--
-- Open terms allow to represent constructors with a few arguments applied,
-- but not as many as their arity.
-- Now arguments are given one-by-one, and the combinatorial problem
-- is simplified to just counting the number of arguments a
-- and open terms t such that wₐ + wₜ ≡ w.
-- We use <-rec to show both a and t are drawn from finite sets.
--------------------------------------------------------------------------------

-- OpenTerms S w n are the terms over signature S
-- * whose total weight (so far) is w
-- * that still need n more arguments to become a closed term
--      (i.e., to become a constructor with exactly as many inductive
--      arguments as its own arity).
data OpenTerms {μ ζ : ℕ∞} (S : Signature μ ζ) : ℕ → ℕ → Set where
    mk-nullary 
        : (c : cardToSet μ) 
        → OpenTerms S (ℕ.suc $ cardToℕ c) 0
    mk-multiary 
        : (c : cardToSet ζ) 
        → OpenTerms S (ℕ.suc $ cardToℕ c) (arity {μ} {ζ} {S = S} c)
    -- Give a closed term as next argument to a strictly open term.
    giveArg 
        : {wₜ : ℕ} 
        → {wₐ : ℕ} 
        → {m : ℕ} 
        → (t : OpenTerms {μ} {ζ} S wₜ (ℕ.suc m))
        → (a : OpenTerms {μ} {ζ} S wₐ 0)
        → OpenTerms {μ} {ζ} S (wₐ + wₜ) m
    
-- Closed terms: open terms needing no more arguments.
ClosedTerms : {μ ζ : ℕ∞} (S : Signature μ ζ) → ℕ → Set
ClosedTerms {μ} {ζ} S w =  OpenTerms {μ} {ζ} S w 0

-- *All* closed terms over S.
AllTerms : {μ ζ : ℕ∞} (S : Signature μ ζ) → Set
AllTerms {μ} {ζ} S = Σ[ w ∈ ℕ ] (ClosedTerms {μ} {ζ} S w)

-- #TODO: maybe move to new file 'TermsProperties' or so?
-- All terms have at least weight 1.
noWeightlessTerms 
    : {μ ζ : ℕ∞} 
    → (S : Signature μ ζ) 
    → (n : ℕ)
    → OpenTerms {μ} {ζ} S 0 n
    → ⊥ 
noWeightlessTerms {μ} {ζ} S n t = ?

--------------------------------------------------------------------------------
-- Main theorem : all term algebras over these Signatures are enumerable
--
-- Proof strategy:
-- * Show that the inhabited weights, i.e., `Terms w` such that there exists
--      a `t : Terms w`, are all ≃ to `Fin (suc (z w))`
--      for some `(z w) : ℕ`.
--      (This is the hardest part and the only part that I have not entirely
--      worked out all the details on paper, it still requires solving a
--      combinatorial problem. See paper sheet (Lih 7)).
-- * Create a 'jump' function that, given one inhabited weight,
--      outputs the next inhabited weight, plus a proof that all weights
--      inbetween are not inhabited.
-- * To be able to implement this jump function in a terminating way, 
--      define an 'upper bound' function that gives, 
--      for all inhabited weights `w : ℕ`,
--      an `h : ℕ` such that `Terms (w + 1 + h)` is also inhabited
--      (h might not be the minimum, but it allows us to use h as 'fuel'
--      when defining the 'jump' function: it never needs to try more than
--      the first next h weights).
-- * Prove a general theorem that `AllTerms` is _≃_ to the sum over only
--      the weights reached by the jump function.
-- * Prove a general theorem that `Σ[ n ∈ ℕ ] Fin (suc (z n)) ≃ ℕ`.
--------------------------------------------------------------------------------

-- The term algebra of a signature with only nullary constructors
-- is isomorphic to just the set of the nullary constructors.
-- This is either Fin μ (if μ is finite) or ℕ (if μ = ∞).
closedTermAlgEnum
    : {μ : ℕ∞}
    → (S : Signature μ (fin 0))
    → AllTerms {μ} {fin 0} S ≃ cardToSet μ
closedTermAlgEnum = StillTODO

-- The term algebra of a signature without nullary constructors
-- is always empty. There are no atomic terms, and therefore also no arguments
-- to multiary constructors.
emptyTermAlgEmpty
    : {ζ : ℕ∞}
    → (S : Signature (fin 0) ζ )
    → (AllTerms {fin 0} {ζ} S) ≃ ⊥
emptyTermAlgEmpty = StillTODO

-- The term algebra of a signature with at least one nullary constructor a
-- (so an atomic term) and at least one multiarty constructor c
-- is always isomorphic to ℕ, since we can aways construct:
-- t₀ ≔ a
-- t₁ ≔ c(a , ..., a )
-- t₂ ≔ c(t₁, ..., t₂)
-- t₃ ≔ c(t₃, ..., t₃)
-- etc.
infTermAlgEnum
    : {μ ζ : ℕ∞}
    → (S : Signature (suc∞ μ) (suc∞ ζ))
    → (AllTerms {suc∞ μ} {suc∞ ζ} S) ≃ ℕ
--^ See below for the proof

-- Combining the three above lemmas: every term algebra
-- is isomorphic to either `Fin n` for some n ∈ ℕ xor isomorphic to ℕ.
-- That is equivalent to saying, isomorphic to `cardToSet z` for some z ∈ ℕ∞.
everyTermAlgEnum
    : {μ ζ : ℕ∞}
    → (S : Signature μ ζ)
    → Σ[ z ∈ ℕ∞ ](AllTerms {μ} {ζ} S ≃ cardToSet z)
everyTermAlgEnum {μ} 
                 {fin 0} 
                 S = (μ , closedTermAlgEnum {μ} S)
everyTermAlgEnum {fin 0} 
                 {ζ} 
                 S = (fin 0 , emptyTermAlgEmpty {ζ} S)
everyTermAlgEnum {μ@(fin (ℕ.suc x))} 
                 {ζ@(fin (ℕ.suc y))} 
                 S = (∞ , infTermAlgEnum {fin x} {fin y} S)
everyTermAlgEnum {μ@(fin (ℕ.suc x))} 
                 {∞} 
                 S = (∞ , infTermAlgEnum {fin x} {∞} S)
everyTermAlgEnum {∞} 
                 {fin (ℕ.suc y)} 
                 S = (∞ , infTermAlgEnum {∞} {fin y} S)
everyTermAlgEnum {∞} 
                 {∞} 
                 S = (∞ , infTermAlgEnum {∞} {∞} S)
--------------------------------------------------------------------------------
-- Jump theorem: given a function that jumps between inhabited finite types,
-- then the sum of all those types is equivalent to ℕ.
--------------------------------------------------------------------------------
-- `iter f n a` returns fⁿ(a), i.e., f applied n times starting from a.
iter : {A : Set} → (A → A) → ℕ → A → A
iter {A} f 0 a = a
iter {A} f (suc n) a = f (iter f n a)

jumpTheorem
    : {A : Set}
    -- ^ Type of 'points' the jumping function can visit.
    → (a₀ : A)
    -- ^ Starting point.
    → (j : A → A)
    -- ^ Function to jump between points.
    → (z : A → ℕ)
    -- ^ Sizes of visited types, minus one.
    → Σ[ n ∈ ℕ ](Fin $ ℕ.suc $ z (iter j n a₀)) ≃ ℕ
jumpTheorem = IGotProofOnPaper -- Sheet "Lih 10".

--------------------------------------------------------------------------------
-- Skip-over-⊥s theorem
-- A sum over a family of types is equivalent to the sum
-- over the same types except with the empty ones left out.
--
-- One could prove a more general statement than presented here,
-- but this version is most convenient for our use case.
--------------------------------------------------------------------------------

-- A function that jumps from one to the next inhabited type
-- given an ℕ-indexed family of types.
InhabitJumper : {C : ℕ → Set}  → Set
InhabitJumper {C} 
    = {w : ℕ} 
    → C w
    → Σ[ h ∈ ℕ ] (
       --^ Jumping distance (minus one).
       (C $ w + 1 + h) 
       --^ The destination is inhabited, ...
       × 
       ((x : ℕ) → (w < x × x < w + 1 + h) → ¬ C x) 
       --^ ... but intermediate points are not.
    )
-- Note: the argument `C w` might seem redundant.
-- For my use case it could indeed be avoided,
-- but the implementation of an actual jumper simplifies a lot if we can
-- depart from the latest inhabited point.
-- The alternative is to take multiple jumps from the first inhabited points,
-- until one reaches the first point beyond w; this is more work to prove right
-- in Agda.

-- Iterate an InhabitJumper from an inhabited starting point n₀,
-- and give the point reached after n jumps.
-- (In out use case (see below), we'll have ¬ C 0 but C 1 is inhabited, 
-- so we start with n₀ ≔ 1).
J-iter : {C : ℕ → Set} → (n₀ : ℕ) → C n₀ → (J : InhabitJumper {C}) → ℕ → ℕ
J-iter {C} n₀ t₀ J 0 = n₀
--J-iter {C} n₀ t₀ J (suc n) = proj₁ $ depGIter g J' n (n₀ , t₀)
J-iter {C} n₀ t₀ J (suc n) = proj₁ $ iter J' n (n₀ , t₀)
    where
        J' : Σ[ w ∈ ℕ ] C w → Σ[ w ∈ ℕ ] C w
        J' (w , t) = 
            let (h , t' , _) = J {w} t
            in
            (w + 1 + h , t')

jumpOver⊥s
    : (C : ℕ → Set)
    → (J : InhabitJumper {C})
    → (¬ C 0)
    → (t₀ : C 1)
    → (Σ[ w ∈ ℕ ] C w) ≃ (Σ[ n ∈ ℕ ] (C $ J-iter 1 t₀ J n))
jumpOver⊥s _ _ _ _ = IGotProofOnPaper -- See sheet "Lih 11" backside

-- Special case of the jumpTheorem where 
-- the jump function is implemented via an InhabitJumper,
-- and the starting point is C 1.
jumpTheoremInhabitJumper
    : {C : ℕ → Set}
    -- ^ Type of 'points' the jumping function can visit.
    → (a₀ : C 1)
    -- ^ Proof the starting point 1 is inhabited.
    → (J : InhabitJumper {C})
    -- ^ Function to jump between points.
    → (z : ℕ → ℕ)
    -- ^ Sizes of visited points, minus one.
    → Σ[ n ∈ ℕ ](Fin $ ℕ.suc $ z (J-iter {C} 1 a₀ J n)) ≃ ℕ
jumpTheoremInhabitJumper = IGotProofOnPaper -- Sheet "Lih 10".

--------------------------------------------------------------------------------
-- Theorem: there are finitely many terms of a fixed weight
--
-- I.e., `Terms w ≃ Fin (ż w)` for all w ∈ ℕ for some ż : ℕ → ℕ
--------------------------------------------------------------------------------

-- The main statement is as follows:
ZTheorem : {μ ζ : ℕ∞} → (S : Signature (μ) (ζ))
    → Σ[ ż ∈ (ℕ → ℕ → ℕ) ](
        (w : ℕ) → (n : ℕ) → (OpenTerms {μ} {ζ} S w n) ≃ (Fin $ ż w n)
        )
ZTheorem = StillTODO

-- The cases where S's term algebra is finite are easy,
-- the special case where S's term algebra is infinite
-- is the real work:
ZTheoremInhab : {μ ζ : ℕ∞} → (S : Signature (suc∞ μ) (suc∞ ζ))
    → Σ[ z ∈ (ℕ → ℕ → ℕ) ](
        (w : ℕ) 
        → (n : ℕ) 
        → (OpenTerms {suc∞ μ} {suc∞ ζ} S w n) ≃ (Fin $ ℕ.suc $ z w n)
        )
ZTheoremInhab = StillTODO

-- But I will prove the latter via a collection of sublemmas.
module ZSublemmas (μ ζ : ℕ∞) (S : Signature (suc∞ μ) (suc∞ ζ)) where

    OT = OpenTerms {suc∞ μ} {suc∞ ζ} S

    -- Strategy:
    -- OT 0 n is uninhabited because there's simply no constructor for weight w.
    -- OT 1 n is a singleton (Fin 1) if n ≡ 0 or if a constructor with index 0
    -- has arity n; only these have weight 1. 
    -- OT w n for w ≥ 2 is the hard case:
    -- 1. OT w n ≡ (OT⁰ w n) ⊎ (OTᵉ w n) ⊎ (OTᵃ w n)
    --      where 
    --          OT⁰ w n are the terms in OT w n made with mk-nullary.
    --          OT⁼ w n are the terms in OT w n made with mk-multiary,
    --              i.e., constructors without any aguments applied.
    --          OTᵃ w n are the terms in OT w n made with giveArg,
    --              i.e., constructors with one or more arguments applied.
    -- 2. OT⁰ w (suc n) ≃ Fin 0 always, 
    --      because nullary constructors don't need arguments. 
    --    OT⁰ w 0 ≃ Fin 1 if there are at least w nullary constructors,
    --      and OT⁰ w 0 ≃ ⊥ otherwise; 
    --      only the term with index w-1 has weight w,
    --      but it doesn't exist if the set of nullary constructors
    --      is smaller than Fin w.
    -- 3. OTᵉ w n ≃ Fin 1 if there are at least w constructors
    --      and the constructor with index w-1 has arity n.
    --      Otherwise OTᵉ w n ≃ Fin 0

-- #TODO Finish this

--------------------------------------------------------------------------------
-- Big picture proof of infTermAlgEnum
--------------------------------------------------------------------------------

infTermAlgEnum {μ} {ζ} S = 
    --------------------------------------
    -- Unpacking earlier results
    --------------------------------------
    let C = ClosedTerms {suc∞ μ} {suc∞ ζ} S in
    let ¬C0 : C 0 → ⊥ -- All terms have at least weight 1.
        ¬C0 = noWeightlessTerms {suc∞ μ} {suc∞ ζ} S 0
    in
    let J : InhabitJumper {C}
        J = ?
    in
    -- There is at least one nullary constructor; let a₀ be the corresponding
    -- term. We need a subst to remind Agda that it always has weight 1.
    let a₀ : C 1
        a₀ =
            let H : (ℕ.suc $ cardToℕ $ cardToZero μ) ≡ 1
                H = ?
            in
            subst C H (mk-nullary (cardToZero μ))
    in
    let j : ℕ → ℕ
        j = J-iter {C} 1 a₀ J 
    in
    let (z' , Cw-to-Finz') = ZTheoremInhab {μ} {ζ} S
    in
    -- We're only interested in terms taking 0 more arguments:
    let z = λ w → z' w 0 in
    let Cw-to-Finz = λ w → Cw-to-Finz' w 0 in
    --------------------------------------
    -- Actual proof: chain of _≃_'s
    --------------------------------------
    begin 
        (Σ[ w ∈ ℕ ] C w)
    -- 1. Filter away uninhabited weights.
    ≃⟨ jumpOver⊥s C J ¬C0 a₀ ⟩
        (Σ[ n ∈ ℕ ] C (j n))
    -- 2. Show every inhabited weight is _≃_ to a nonempty finite set.
    ≃⟨ rewr-≃-under-Σ $ Cw-to-Finz ∘ j ⟩
        (Σ[ n ∈ ℕ ] (Fin $ ℕ.suc $ z $ j n))
    -- 3. A ℕ-indexed sum of nonempty finite sets is _≃_ to ℕ.
    ≃⟨ jumpTheoremInhabitJumper {C} a₀ J z ⟩
        ℕ
    ∎
    

