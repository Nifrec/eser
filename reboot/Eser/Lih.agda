-- Module      : Eser.Lih
-- Description : Outline of the "Later is heavier" strategy
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- This file sketches the "Later is heaver" approach,
-- which has its own distinctive reprentation of signatures (finitary W-types)
-- and a proof outline for showing term algebras are equivalent to ℕ.
-- Ideas developped in the period 11-18 March 2026,
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

open import Function renaming (_⇔_ to _≃_)
open import Relation.Binary.Reasoning.Syntax

open import StreamGrids.Card

module Eser.Lih where

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
-- Arguments are stored in a vector; this is to be compared against the
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
--------------------------------------------------------------------------------

-- Given a vectors of pairs (w , a), take the sum of the first projections.
weightSum : {A : ℕ → Set} → {n : ℕ} → Vec (Σ[ w ∈ ℕ ] A w) n → ℕ
weightSum {A} {0} v = 0
weightSum {A} {suc n} ((w , a) ∷ v) = w + weightSum v

data Terms {μ ζ : ℕ∞} (S : Signature μ ζ) : ℕ → Set where
    mk-nullary : (n : cardToSet μ) → Terms S (ℕ.suc (cardToℕ n))
    mk-multiary 
        : (c : cardToSet ζ) 
        → (v : Vec (Σ[ w ∈ ℕ ] Terms {μ} {ζ} S w) (arity {μ} {ζ} {S} c))
        → Terms S (1 + cardToℕ c + weightSum v)

AllTerms : {μ ζ : ℕ∞} →  (S : Signature μ ζ) → Set
AllTerms {μ} {ζ} S = Σ[ w ∈ ℕ ] Terms {μ} {ζ} S w


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
    → Σ[ z ∈ ℕ∞ ](AllTerms {μ} {ζ} S) ≃ cardToSet z
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
    → Σ[ n ∈ ℕ ](Fin $ ℕ.suc $ z (iter j n a₀))
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

--------------------------------------------------------------------------------
-- Theorem: there are finitely many terms of a fixed weight
--
-- I.e., `Terms w ≃ Fin (ż w)` for all w ∈ ℕ for some ż : ℕ → ℕ
--------------------------------------------------------------------------------

-- The main statement is as follows:
ZTheorem : {μ ζ : ℕ∞} → (S : Signature (μ) (ζ))
    → Σ[ ż ∈ (ℕ → ℕ) ](
        (w : ℕ) → (Terms {μ} {ζ} S w) ≃ (Fin $ ż w)
        )
ZTheorem = StillTODO

-- The cases where S's term algebra is finite are easy,
-- the special case where S's term algebra is infinite
-- is the real work:
ZTheoremInhab : {μ ζ : ℕ∞} → (S : Signature (suc∞ μ) (suc∞ ζ))
    → Σ[ z ∈ (ℕ → ℕ) ](
        (w : ℕ) → (Terms {suc∞ μ} {suc∞ ζ} S w) ≃ (Fin $ ℕ.suc $ z w)
        )
ZTheoremInhab = StillTODO

-- But I will prove the latter via a collection of sublemmas.
module ZSublemmas (μ ζ : ℕ∞) (S : Signature (suc∞ μ) (suc∞ ζ)) where

    C = Terms {suc∞ μ} {suc∞ ζ} S

    -- Strategy:
    -- C 0 is uninhabited because there's simply no constructor for weight w.
    -- C 1 is a singleton, i.e. Fin 1;
    --      only the nullary constructor with index 0 has weight 1.
    -- C w for w ≥ 2 is the hard case:
    -- 1. C w ≡ (C⁰ w) ⊎ (C⁺ w)
    --      where 
    --          C⁰ w are the terms of weight w made with a nullary constructor.
    --          C⁼ w are the terms of weight w made with a multiary constructor.
    -- 2. C⁰ w ≃ Fin 1 if there are at least w nullary constructors,
    --      and C⁰ w ≃ ⊥ otherwise; only the term with index w-1 has weight w,
    --      but it doesn't exist if the set of nullary constructors
    --      is smaller than Fin w.
    -- 3. C⁺ w ≃ Σ[ C ∈ {0, ..., w-1} ](
    --      --^ Later constructors are too heavy already.
    --      --  (If there are fewer than w constructors this set should be even
    --      --  smaller)
    --           Σ[ v ∈ Vec (Σ[k∈ℕ] (k < w) × (C k)) (arity c) ]
    --      -- Vector of arguments, each having at most weight w∸1.
    --          weightSum v ≡ w ∸ 1 ∸ c
    --      )
    --      Idea: a term (mk-multiary c v) ∈ C⁺ w
    --          of weight w must have w = c + 1 + weightSum(v).
    --          So weightSum v ≡ w ∸ 1 ∸ c (since w ≥ 2).
    --          Since the weightSum is greater or equal to the weight
    --          of any element, and since it has at least one element
    --          (arity c ≥ 1), no element can have weight greater than w∸1.
    -- 4. The number of choices c ∈ {0, ..., w-1} is finite
    --      and computable, and the number of Vectors of a fixed length (arity
    --      c) over a finite set is finite
    --      (by the induction hypothesis, C k ≃ Fin (1 + z k) since k < w).
    --      So the RHS in 3. is finite.
    -- 5. To count the number of vectors in the inner-Σ in the LHS of 3.
    --      we need to solve the following combinatorial problem:
    --
    --      Given a w ∈ ℕ and for each 0 ≤ k ≤ w - 1 a number Bₖ of balls
    --      of weight k,
    --      in how many ways can we choose N balls such that their total weight
    --      is w? (order matters, the same ball may be chosen multiple times).
    --      (in our case:  N ≔ arity c  and  Bₖ = C k ≃ Fin (1 + z k) )

-- #TODO Finish this

--------------------------------------------------------------------------------
-- Big picture proof of infTermAlgEnum
--------------------------------------------------------------------------------
infTermAlgEnum {μ} {ζ} S = ?
