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
-- Ideas developed in March & April 2026,
-- after the 11 March discussion with supervisors pointed out the previous
-- approach was overly complicated and that things could have been done more
-- general.

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Induction
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
open import Data.Fin.Properties using (fromℕ<-toℕ ; toℕ-fromℕ< ; toℕ-injective)

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Card
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Aux

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
--      * Signature (suc∞ μ) (suc∞ ζ) has a term algebra equivalent to ℕ.
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
noWeightlessTerms {μ} {ζ} S n t = ? -- #TODO: mave prove OT S w n → w > 0 first.

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
ZP  : {μ ζ : ℕ∞} 
    → (S : Signature (μ) (ζ))
    → (w : ℕ) 
    → Set
ZP {μ} {ζ} S w = (n : ℕ) → Σ[ z ∈ ℕ ]( OpenTerms {μ} {ζ} S w n ≃ Fin z )

-- #TODO: move splits stuff to other file
Splits : ℕ → Set
Splits w = Σ[ x ∈ ℕ ] Σ[ y ∈ ℕ ](ℕ.suc x + ℕ.suc y ≡ w)
splitsSize : ℕ → ℕ
splitsSize 0 = 0
splitsSize 1 = 0
splitsSize (suc (suc w)) = ℕ.suc w

-- Given two splits with the same x, the entire splits must be equal.
-- I.e., the first component fixes the rest of the data uniquely as well,
-- at least up to _≡_.
-- (Almost equivalently: for fixed x and w, 
--  the type Σ[ y ∈ ℕ ](ℕ.suc x + ℕ.suc y ≡ w) is proof-irrelevant).
splitsEqLemma
    : (w : ℕ)
    → (s s' : Splits w)
    → proj₁ s ≡ proj₁ s'
    → s ≡ s'
splitsEqLemma w (x , y , p) (x , y' , p') refl =
    let y≡y' : y ≡ y'
        y≡y' = suc-injective  
               $ +-injective {ℕ.suc x} {ℕ.suc y} {ℕ.suc y'} (trans p (sym p'))
    in
    sublemma y≡y' p p'
    where
        sublemma
            : {y y' : ℕ}
            → (y ≡ y')
            → (p : ℕ.suc x + ℕ.suc y ≡ w)
            → (p' : ℕ.suc x + ℕ.suc y' ≡ w)
            → (x , y , p) ≡ (x , y' , p')
        sublemma {y} {y} refl p p' = cong (λ p → (x , y , p)) (≡-irrelevant p p')

-- If (x , y) is a split of w then x < (w-1).
splitsToSmaller
    : (w' : ℕ)
    --→ (x y : ℕ)
    --→ (p : ℕ.suc x + ℕ.suc y ≡ w)
    → (s : Splits (ℕ.suc w'))
    → (proj₁ s < w')
splitsToSmaller w' (x , y , p) 
    = s≤s⁻¹ (≤begin
        ℕ.suc (ℕ.suc x)
        ≤⟨ m≤m+n (ℕ.suc $ ℕ.suc x) y ⟩
        ℕ.suc (ℕ.suc x) + y
        ≤-Reasoning.≡⟨ sym $ +-suc (ℕ.suc x) y ⟩
        ℕ.suc x + ℕ.suc y
        ≤-Reasoning.≡⟨ p ⟩
        ℕ.suc w'
        ≤∎)
        where open ≤-Reasoning renaming (begin_ to ≤begin_ ; _∎ to _≤∎)
splitsFin : (w : ℕ) → Splits w ≃ Fin (splitsSize w)
splitsFin 0 = mk≃' f f⁻¹ invˡ invʳ
    where -- Trivial proof, Agda can already infer both types are empty!
    f : Splits 0 → Fin (splitsSize 0)
    f ()
    f⁻¹ : Fin (splitsSize 0) → Splits 0
    f⁻¹ ()
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {()}
    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {()}
splitsFin 1 = mk≃' f f⁻¹ invˡ invʳ
    where -- 1+x + 1+y ≡ 1 has no solution! But we do need to tell that Agda.
    f : Splits 1 → Fin (splitsSize 1)
    f (x , y , p) = ⊥-elim $ ¬1+m+1+n≡1 p
    f⁻¹ : Fin (splitsSize 1) → Splits 1
    f⁻¹ ()
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {()}
    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {(x , y , p)} = ⊥-elim $ ¬1+m+1+n≡1 p
splitsFin w@(suc w'@(suc w'')) = mk≃' f f⁻¹ invˡ invʳ
    where
    f : Splits w → Fin (splitsSize w)
    f s = fromℕ< (splitsToSmaller w' s)
    f⁻¹ : Fin (splitsSize w) → Splits w
    f⁻¹ x = 
        let -- (y , p) : Σ[ y ∈ Fin (ℕ.suc w) ](toℕ x + toℕ y ≡ w)
            (y , p) = finOppositeSuc w' x
        in
        (toℕ x , toℕ y , p)
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {x} {s} refl = 
        ≡begin 
            f s
        ≡⟨⟩ -- Definition f
            fromℕ< (splitsToSmaller w' s)
        ≡⟨ fromℕ<-toℕ x (splitsToSmaller w' s) ⟩
            x
        ≡∎
    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {s@(x , y , p)} {x'} refl =
        let (x'' , y'' , p'') = f⁻¹ $ f s in
        let H : x'' ≡ x
            H = ≡begin 
                    x''
                ≡⟨⟩
                    (proj₁ $ f⁻¹ $ f s)
                ≡⟨⟩ -- Definition f
                    (proj₁ $ f⁻¹ $ fromℕ< (splitsToSmaller w' s))
                ≡⟨⟩ -- Definition f⁻¹
                    (toℕ $ fromℕ< (splitsToSmaller w' s))
                ≡⟨ toℕ-fromℕ< {x} (splitsToSmaller w' s) ⟩
                    x
                ≡∎
        in
        ≡begin 
            (x'' , y'' , p'')
        ≡⟨ splitsEqLemma w (x'' , y'' , p'') (x , y , p) H ⟩
            (x , y , p)
        ≡∎


split<Left : (m : ℕ) → (s : Splits m) → (ℕ.suc (proj₁ s) < m)
split<Left m s = posSummandsThenSmaller wₜ+wₐ≡m
    where
        wₜ = ℕ.suc (proj₁ s)
        wₐ = ℕ.suc (proj₁ ( proj₂ s))
        wₜ+wₐ≡m = proj₂ (proj₂ s)

split<Right : (m : ℕ) → (s : Splits m) → (ℕ.suc (proj₁ (proj₂ s)) < m)
split<Right m s = posSummandsThenSmaller wₐ+wₜ≡m
    where
        wₜ = ℕ.suc (proj₁ s)
        wₐ = ℕ.suc (proj₁ ( proj₂ s))
        wₜ+wₐ≡m = proj₂ (proj₂ s)
        wₐ+wₜ≡m = subst (λ x → x ≡ m) (+-comm wₜ wₐ) wₜ+wₐ≡m

-- The following definitions semantically belong to the ZTheoremProof
-- module below, but are easier to define when the arguments of the module
-- can be treated as variables instead.

module ZTheoremProof
    {μ ζ : ℕ∞}
    (S : Signature μ ζ)
    where

    OT = OpenTerms {μ} {ζ} S
    ZP' : (w : ℕ) → Set
    ZP' w = ZP {μ} {ζ} S w

    IsNullary : {w : ℕ} → {n : ℕ} → OT w n → Set
    IsNullary (mk-nullary _) = ⊤
    IsNullary (mk-multiary _) = ⊥
    IsNullary (giveArg _ _) = ⊥

    IsEmptyMultiary : {w : ℕ} → {n : ℕ} → OT w n → Set
    IsEmptyMultiary (mk-nullary _) = ⊥
    IsEmptyMultiary (mk-multiary _) = ⊤
    IsEmptyMultiary (giveArg _ _) = ⊥

    IsGiveArg : {w : ℕ} → {n : ℕ} → OT w n → Set
    IsGiveArg (mk-nullary _) = ⊥
    IsGiveArg (mk-multiary _) = ⊥
    IsGiveArg (giveArg _ _) = ⊤

    isNullaryNoArgs 
        : {w : ℕ} 
        → {n : ℕ} 
        → (t : OT w n)
        → IsNullary t
        → n ≡ 0
    isNullaryNoArgs {w} {0} (mk-nullary c) p = refl

    -- Sublemma of lemma isNullaryWeight below.
    -- For isNullaryWeight, either
    -- use (t : OT w 0) and Σ[ c ∈ cardToSet μ ] (fin (w ∸ 1) <∞ μ),
    -- which has an annoying _∸_ but allows to pattern
    -- match t to `mk-nullary c`,
    -- xor
    -- use (t : OT (ℕ.suc w) 0) and Σ[ c ∈ cardToSet μ ] (fin w <∞ μ),
    -- in which case Agda fails to rule out the giveArg case and we don't get c
    -- via pattern matching. `getNullaryConstr` then gives c anyway.
    getNullaryConstr
        : {w : ℕ} 
        → (t : OT w 0)
        → IsNullary t
        → Σ[ c ∈ cardToSet μ ]( w ≡ ℕ.suc (cardToℕ c) )
    getNullaryConstr {w} (mk-nullary c) p = (c , H)
        where
            H : w ≡ ℕ.suc (cardToℕ c)
            H = refl

    isNullaryWeight
        : {w : ℕ} 
        → (t : OT (ℕ.suc w) 0)
        → IsNullary t
        → fin w <∞ μ
    isNullaryWeight {w} t p =
        let (c , Sw≡Sc) = getNullaryConstr t p
        in
        let w≡c : fin w ≡ fin (cardToℕ c)
            w≡c = cong fin $ suc-injective Sw≡Sc
        in
        subst (λ x → x <∞ μ) (sym w≡c) (smallerThanCard c)

    isNullaryUnderSubst
        : {w : ℕ}
        → {c : cardToSet μ}
        → (p : (ℕ.suc (cardToℕ c) ≡ w))
        → IsNullary (subst (λ x → OT x 0) p (mk-nullary c))
    isNullaryUnderSubst refl = tt

        

    giveArgUnderSubst
        : {w wₐ wₜ : ℕ}
        → {n : ℕ}
        → (p : (ℕ.suc wₐ + ℕ.suc wₜ ≡ w))
        → (t : OpenTerms {μ} {ζ} S (ℕ.suc wₜ) (ℕ.suc n))
        → (a : OpenTerms {μ} {ζ} S (ℕ.suc wₐ) 0)
        → IsGiveArg (subst (λ x → OT x n) p (giveArg t a))
    giveArgUnderSubst refl t a = tt

    OT-Nul : ℕ → ℕ → Set
    OT-Nul w n = Σ[ t ∈ OT w n ] (IsNullary t)

    OT-Mul : ℕ → ℕ → Set
    OT-Mul w n = Σ[ t ∈ OT w n ] (IsEmptyMultiary t)

    OT-Arg : ℕ → ℕ → Set
    OT-Arg w n = Σ[ t ∈ OT w n ] (IsGiveArg t)

    -- Trivial sublemma: OT w n is an Agda-inductive type, and hence the sum
    -- over all of its Agda-constructors of the subsets of the terms
    -- constructed with that constructor.
    ZsubDecompo : (w : ℕ) → (n : ℕ) → OT w n ≃ (OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n)
    ZsubDecompo w n = mk≃ {to = to} {from = from} inv
        where 
            to : OT w n → (OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n)
            to t@(mk-nullary _) = inj₁ (t , tt)
            to t@(mk-multiary _) = inj₂ $ inj₁ (t , tt)
            to t@(giveArg _ _) = inj₂ $ inj₂ (t , tt)

            from : (OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n) → OT w n
            from (inj₁ (t , _)) = t
            from (inj₂ (inj₁ (t , _))) = t
            from (inj₂ (inj₂ (t , _))) = t
            invˡ : Inverseˡ _≡_ _≡_ to from
            invˡ {inj₁ (mk-nullary _ , tt)} {t} refl = refl
            invˡ {inj₂ (inj₁ (mk-multiary _ , tt))} {t} refl = refl
            invˡ {inj₂ (inj₂ (giveArg _ _ , tt))} {t} refl = refl
            invʳ : Inverseʳ _≡_ _≡_ to from
            invʳ {mk-nullary _} {x} refl = refl
            invʳ {mk-multiary _} {x} refl = refl
            invʳ {giveArg _ _} {x} refl = refl
            inv : Inverseᵇ _≡_ _≡_ to from
            inv = (invˡ , invʳ)
 
    isNullaryInhabited
        : {w : ℕ}
        → (H : fin w <∞ μ)
        → OT-Nul (ℕ.suc w) 0
    isNullaryInhabited {w} H = 
        let c : cardToSet μ
            c = proj₁ $ cardFrom<∞ H
        in
        let Sc≡Sw : ((ℕ.suc $ cardToℕ c) ≡ ℕ.suc w)
            Sc≡Sw = cong ℕ.suc (proj₂ $ cardFrom<∞ H)
        in
        let t : OpenTerms {μ} {ζ} S (ℕ.suc w) 0
            t = subst (λ x → OpenTerms {μ} {ζ} S x 0) Sc≡Sw (mk-nullary c)
        in
        (t , isNullaryUnderSubst Sc≡Sw)

    --isNullaryContr
    --    : {w : ℕ} 
    --    → (t : OT w 0)
    --    → (p : IsNullary t)
    --    → t ≡  subst (λ x → OpenTerms {μ} {ζ} S x 0) 
    --            (proj₂ $ getNullaryConstr t p) (mk-nullary $ proj₁ $ getNullaryConstr t p)
    --isNullaryContr t H p = ?

    --getNullaryConstrStrong
    --    : {w : ℕ} 
    --    → (t : OT w 0)
    --    → IsNullary t
    --    → Σ[ c ∈ cardToSet μ ]( w ≡ ℕ.suc (cardToℕ c) × t ≡ mk-nullary c)
    --getNullaryConstrStrong {w} (mk-nullary c) p = (c , H , refl)
    --    where
    --        H : w ≡ ℕ.suc (cardToℕ c)
    --        H = refl

    getNullaryConstrLemma
        : {w : ℕ} 
        → (c : cardToSet μ)
        → (proj₁ $ getNullaryConstr  (mk-nullary c) tt) ≡ c
    getNullaryConstrLemma {w} c = refl


    --lemma
    --    : {w : ℕ} 
    --    → (c : cardToSet μ)
    --    → (t : OT w 0)
    --    → IsNullary t
    --    → (H : (ℕ.suc $ cardToℕ c) ≡ w)
    --    → t ≡ subst (λ x → OT x 0) H (mk-nullary c)
    --lemma c (mk-nullary c') p H = 
    --    let c≡c' = cardToℕ-injective $ suc-injective H
    --    in
    --    ?

    isNullaryUnique'
        : (wt : Σ[ w ∈ ℕ ](OT w 0))
        → (w't' : Σ[ w ∈ ℕ ](OT w 0))
        → IsNullary (proj₂ wt)
        → IsNullary (proj₂ w't')
        → (H : proj₁ wt ≡ proj₁ w't')
        → wt ≡ w't'
    isNullaryUnique' (w , mk-nullary c) (w' , mk-nullary c') p p' H =
        let c≡c' : c ≡ c'
            c≡c' = cardToℕ-injective $ suc-injective H
        in
        cong (λ c → ((ℕ.suc $ cardToℕ c) , mk-nullary c)) c≡c'
        
    isNullaryUnique
        : {w w' : ℕ} 
        → (t : OT w 0)
        → (t' : OT w' 0)
        → IsNullary t
        → IsNullary t'
        → (H : w' ≡ w)
        → t ≡ (subst (λ w → OT w 0) H t') 
    isNullaryUnique {w} {w'} t t' p p' refl = 
        let wt≡wt' : (w , t) ≡ (w , t') 
            wt≡wt' = isNullaryUnique' (w , t) (w' , t') p p' refl
        in
        meh wt≡wt' 
        where
            meh : {w : ℕ} 
                → {t t' : OT w 0}
                → (w , t) ≡ (w , t')
                → t ≡ t'
            meh {w} {w'} refl = refl

    --isNullaryUnique {w} {w'} t@(mk-nullary c) t'@(mk-nullary c') p p' refl = 
    --    let k = getNullaryConstr {w} t p in
    --    let k' = getNullaryConstr {w'} t' p' in ?
        --≡begin 
        
        --≡⟨  ⟩
        
        --≡∎
        

    ---- There is at most one nullary term of weight w,
    ---- and it is the nullary term constructed via constructor w∸1
    --isNullaryUnique
    --    : {w : ℕ} 
    --    → (t t' : OT w 0)
    --    --→ (H : fin w <∞ μ)
    --    → IsNullary t
    --    → IsNullary t'
    --    → t ≡ t'
    --isNullaryUnique {w} t t' p p' = 
    --    let wt≡wt' : (w , t) ≡ (w , t') 
    --        wt≡wt' = isNullaryUnique' (w , t) (w , t') p p' refl
    --    in
    --    let t≡t' : t ≡ t'
    --        t≡t' = meh {w} {w} t t' wt≡wt'
    --    in
    --    ?

    isNullaryIrrelevant
        : {w n : ℕ}
        → (t : OT w n)
        → (p p' : IsNullary t)
        → p ≡ p'
    isNullaryIrrelevant {w} {n} (mk-nullary c) tt tt = refl

    OT-Nul-Irrelevant'
        : {w n : ℕ}
        → {t t' : OT w n}
        → (p : IsNullary t)
        → (p' : IsNullary t')
        → t ≡ t'
        → (t , p) ≡ (t' , p')
    OT-Nul-Irrelevant' {t = t} p p' refl = 
        cong (λ p → (t , p)) $ isNullaryIrrelevant t p p'
        
    
    OT-Nul-Irrelevant
        : {w n : ℕ}
        → (t t' : OT-Nul w n)
        → t ≡ t'
    OT-Nul-Irrelevant {w} {0} (t , p) (t' , p') = 
        let t≡t' : t ≡ t'
            t≡t' = isNullaryUnique t t' p p' refl
        in
        OT-Nul-Irrelevant' p p' t≡t' 

module ZTheoremProofViaVars where

    open ZTheoremProof

    -- Size of the subset of OpenTerms w n that are created with the mk-nullary
    -- constructor. They never take any arguments (for n > 0 it is uninhabited)
    -- and their weight is 1 + their index in μ (the set of nullary
    -- constructors).
    Z-Nul' 
        : (μ ζ : ℕ∞)
        → (S : Signature μ ζ)
        → (w n : ℕ)
        → ℕ
    Z-Nul' μ ζ S w (suc n)  = 0 -- No nullary constructors take arguments.
    Z-Nul' μ ζ S 0 0        = 0 -- All terms have weight at least one.
    -- A nullary term with weight `suc w` has index w in `cardToSet μ`.
    -- If the latter is ℕ then this term always exists; 
    -- but if `cardToSet μ` is `Fin m` then it only exists if `w < m`.
    Z-Nul' μ ζ S (suc w) n  = if does ((fin w) <∞? μ) then 1 else 0

    Eq-Nul' 
        : (μ ζ : ℕ∞)
        → (S : Signature μ ζ)
        → (w n : ℕ)
        → Σ[ z ∈ ℕ ] (OT-Nul {μ} {ζ} S w n ≃ Fin z)
    Eq-Nul' μ ζ S w (suc n) = (0 , ≃-trans equiv (≃-sym fin0))
        where
            equiv : OT-Nul {μ} {ζ} S w (ℕ.suc n) ≃ ⊥
            equiv = mk≃' f f⁻¹ invˡ invʳ
                where
                f : OT-Nul {μ} {ζ} S w (ℕ.suc n) → ⊥
                f (t , p) = 1+n≢0 $ isNullaryNoArgs S t p
                f⁻¹ : ⊥ → OT-Nul {μ} {ζ} S w ( ℕ.suc n)
                f⁻¹ ()
                invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
                invˡ {()} {y}
                invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
                invʳ {y} {()}
    Eq-Nul' μ ζ S 0 0 = (0 , ≃-trans equiv (≃-sym fin0))
        where
            equiv : OT-Nul {μ} {ζ} S 0 0 ≃ ⊥
            equiv = mk≃' f f⁻¹ invˡ invʳ
                where
                f : OT-Nul {μ} {ζ} S 0 0 → ⊥
                f (t , _) = noWeightlessTerms {μ} {ζ} S 0 t
                f⁻¹ : ⊥ → OT-Nul {μ} {ζ} S 0 0
                f⁻¹ ()
                invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
                invˡ {()} {y}
                invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
                invʳ {y} {()}
    Eq-Nul' μ ζ S (suc w) 0 with (fin w <∞? μ)
    ... | no ¬p = (0 ,  ≃-trans equiv (≃-sym fin0))
        where 
            equiv : OT-Nul {μ} {ζ} S (ℕ.suc w) 0 ≃ ⊥
            equiv = mk≃' f f⁻¹ invˡ invʳ
                where
                f : OT-Nul {μ} {ζ} S (ℕ.suc w) 0 → ⊥
                f (t , isNullaryT) = ¬p (isNullaryWeight S t isNullaryT)
                f⁻¹ : ⊥ → OT-Nul {μ} {ζ} S (ℕ.suc w) 0
                f⁻¹ () 
                invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
                invˡ {()} {y}
                invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
                invʳ {y} {()}
    ... | yes p = (1 , equiv)
        where 
            equiv : OT-Nul {μ} {ζ} S (ℕ.suc w) 0 ≃ Fin 1
            equiv = mk≃' f f⁻¹ invˡ invʳ
                where
                f : OT-Nul {μ} {ζ} S (ℕ.suc w) 0 → Fin 1
                f _ = Fin.zero
                f⁻¹ : Fin 1 → OT-Nul {μ} {ζ} S (ℕ.suc w) 0
                f⁻¹ _ = isNullaryInhabited S p 
                invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
                invˡ {Fin.zero} {y} refl = refl
                invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
                invʳ {t} {Fin.zero} refl = OT-Nul-Irrelevant S (f⁻¹ Fin.zero) t

    Z-Mul = ?


-- Implementation of the proof for the ZTheorem for the case where w ≥ 1.
    -- Submodule that also assumes a given weight w and num-remaining-args n
    -- plus the ability to perfrom Well-Founded recursion on w.
module WithArgs
    {μ ζ : ℕ∞}
    (S : Signature μ ζ)
    (w-1 : ℕ)
    (rec : {w' : ℕ} → (w' < ℕ.suc w-1) → ZP {μ} {ζ} S w')
    (n : ℕ) 
    where

    open ZTheoremProof {μ} {ζ} S
    open ZTheoremProofViaVars

    w = ℕ.suc w-1
    Z-Nul = proj₁ $ Eq-Nul' μ ζ S w n
    Eq-Nul = proj₂ $ Eq-Nul' μ ζ S w n 

    Eq-Mul : ? -- OT-Mul w n ≃ Fin Z-Mul
    Eq-Mul = ?

    Zₜ : (s : Splits w) → (n : ℕ) → ℕ
    Zₜ s n = proj₁ (rec (split<Right w s) (ℕ.suc n))

    Hₜ  : (s : Splits w) 
        → (n : ℕ) 
        → (OT (ℕ.suc $ proj₁ $ proj₂ s) (ℕ.suc n)) ≃ (Fin $ Zₜ s n )
    Hₜ s n = proj₂ (rec (split<Right w s) (ℕ.suc n))

    Zₐ : (s : Splits w) → ℕ
    Zₐ s = proj₁ (rec (split<Left w s) 0)

    Hₐ  : (s : Splits w) 
        → (OT (ℕ.suc (proj₁ s)) 0) ≃ (Fin $ Zₐ s )
    Hₐ s = proj₂ (rec (split<Left w s) 0)

    Eq-split
        : (n : ℕ)
        → (s : Splits w)
        →   (
                (OT (ℕ.suc (proj₁ (proj₂ s))) (ℕ.suc n)) 
                × 
                (OT (ℕ.suc (proj₁ s)) 0)
            )
            ≃ 
            ((Fin $ Zₜ s n ) × (Fin $ Zₐ s ))
    Eq-split n s = ≃-× (Hₜ s n) (Hₐ s) 

    OT-Arg-Unfolded : ℕ → ℕ → Set
    OT-Arg-Unfolded w n = (Σ[ (wₐ , wₜ , p) ∈ (Splits w) ]( 
                       (OT (ℕ.suc wₜ) (ℕ.suc n)) × (OT (ℕ.suc wₐ) 0)))

    -- This needs to be defines for all (w , n)
    -- otherwise we cannot pattern match the input to f
    -- to something of the form `giveArg t a`, since w would be
    -- fixed and Agda can't assume arbitrary wₜ and wₐ if there
    -- is a constraint wₜ + wₐ ≗ w for non-variable w. 
    Eq-Arg-FirstStep : (w n : ℕ) → OT-Arg w n ≃ OT-Arg-Unfolded w n
    Eq-Arg-FirstStep w n = mk≃' f f⁻¹ invˡ invʳ
        where
        f : (OT-Arg w n) → OT-Arg-Unfolded w n
        f (giveArg {suc wₜ} {suc wₐ} t a , tt) = ((wₐ , wₜ , refl) , t , a)
        f (giveArg {ℕ.zero} {wₐ} t a , tt) = ⊥-elim $ noWeightlessTerms S (ℕ.suc n) t
        f (giveArg {wₜ} {ℕ.zero} t a , tt) = ⊥-elim $ noWeightlessTerms S 0 a
        f⁻¹ : OT-Arg-Unfolded w n → (OT-Arg w n)
        f⁻¹ ((wₐ , wₜ , p) , t' , a) = 
            let t = subst (λ x → OT x n) p (giveArg t' a)
            in (t , giveArgUnderSubst p t' a)
        invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
        invˡ {(wₐ , wₜ , refl) , t , a} {ta , isGiveArg} refl = refl
        invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
        invʳ {giveArg {ℕ.zero} {wₐ} t a , tt} {x} p = ⊥-elim $ noWeightlessTerms S (ℕ.suc n) t
        invʳ {giveArg {wₜ} {ℕ.zero} t a , tt} {x} p = ⊥-elim $ noWeightlessTerms S 0 a
        invʳ {giveArg {ℕ.suc wₜ} {ℕ.suc wₐ} t a , tt} {(wₐ , wₜ , refl) , t , a} refl = 
            let H = proj₂ $ f⁻¹ ((wₐ , wₜ , refl) , t , a) in
            ≡begin 
                f⁻¹ ((wₐ , wₜ , refl) , t , a) 
            ≡⟨⟩
                ((giveArg t a) , tt)
            ≡∎

    -- It's easier to compute Z-Arg and prove the equivalence
    -- in one go, than to define Z-Arg beforehand.
    Z-Eq-Arg : Σ[ z ∈ ℕ ]( OT-Arg w n ≃ Fin z)
    Z-Eq-Arg = 
        let getSplit : Fin (splitsSize w) → Splits w
            getSplit = Inverse.from (splitsFin w)
        in
        let
            f : Fin (splitsSize w) → ℕ
            f x = (Zₜ (getSplit x) n) * (Zₐ (getSplit x))
        in
        let Z-Arg : ℕ
            Z-Arg = proj₁ (fin-Σ-fun (splitsSize w) f)
        in
        (Z-Arg , 
        (begin 
            OT-Arg w n
        ≃⟨ ≃-refl ⟩
            (Σ[ t ∈ OT w n ] (IsGiveArg t))
        ≃⟨ Eq-Arg-FirstStep w n ⟩
            (Σ[ (wₐ , wₜ , p) ∈ (Splits w) ]( 
                (OT (ℕ.suc wₜ) (ℕ.suc n)) × (OT (ℕ.suc wₐ) 0)
                )
            )
        ≃⟨ rewr-≃-rightOf-Σ (Eq-split n) ⟩
            (Σ[ s ∈ (Splits w) ]((Fin $ Zₜ s n ) × (Fin $ Zₐ s )))
        ≃⟨ rewr-≃-indexOf-Σ-dep (splitsFin w) ⟩
            (Σ[ x ∈ Fin (splitsSize w) ](
                (Fin $ Zₜ (getSplit x) n ) × (Fin $ Zₐ (getSplit x) )))
        -- Use (Fin a) × (Fin b) ≃ Fin (a * b).
        ≃⟨ rewr-≃-rightOf-Σ (λ x → fin-×-* (Zₜ (getSplit x) n) (Zₐ (getSplit x))) ⟩
            (Σ[ x ∈ Fin (splitsSize w) ](
                (Fin $ (Zₜ (getSplit x) n) * (Zₐ (getSplit x)))))
        ≃⟨ proj₂ (fin-Σ-fun (splitsSize w) f) ⟩
            Fin (proj₁ (fin-Σ-fun (splitsSize w) f) )
        ∎
        ))
        
    Z-Arg : ℕ
    Z-Arg = proj₁ Z-Eq-Arg
    Eq-Arg : OT-Arg w n ≃ Fin Z-Arg
    Eq-Arg = proj₂ Z-Eq-Arg

    z : ℕ
    z = Z-Nul + Z-Mul + Z-Arg

    zEquiv : OT w n ≃ Fin z
    zEquiv =
        begin 
            OT w n
        ≃⟨ ZsubDecompo w n ⟩
            ((OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n))
        ≃⟨ rewr-≃-under-⊎-3 Eq-Nul Eq-Mul Eq-Arg ⟩
            (Fin Z-Nul ⊎ Fin Z-Mul ⊎ Fin Z-Arg)
        ≃⟨ rewr-≃-under-⊎-right (fin-⊎-+ Z-Mul Z-Arg) ⟩
            (Fin Z-Nul ⊎ Fin (Z-Mul + Z-Arg ))
        ≃⟨ fin-⊎-+ Z-Nul (Z-Mul + Z-Arg) ⟩
            Fin (Z-Nul + (Z-Mul + Z-Arg))
        ≃⟨ fin-+-assoc Z-Nul Z-Mul Z-Arg ⟩
            Fin (Z-Nul + Z-Mul + Z-Arg)
        ≃⟨ ≃-refl ⟩
            Fin z
        ∎

-- The main statement is as follows:
ZTheorem 
    : {μ ζ : ℕ∞} 
    → (S : Signature (μ) (ζ))
    → (w : ℕ) 
    → (n : ℕ) 
    → Σ[ z ∈ ℕ ]((OpenTerms {μ} {ζ} S w n) ≃ (Fin z))
ZTheorem {μ} {ζ} S w = <-rec (ZP S) f w
    where
        f : (w : ℕ) → (rec : {w' : ℕ} → w' < w → ZP {μ} {ζ} S w') → ZP {μ} {ζ} S w
        f 0 _ = λ n → (0 , ?) -- #TODO: proof that OT 0 n is always empty.
        f (suc w) rec n = (z , p)
            where
                z = {! ZTheoremProof.z {μ} {ζ} S w rec n !}
                p = {! ZTheoremProof.equiv {μ} {ζ} S w rec n !}



-- Alternative presentation of the ZTheorem: give the sizes of the finite
-- sets as a function z : (w : ℕ) → (n : ℕ) → (<size of OT w n> : ℕ).
-- (The ZTheorem uses WF < recursion on w, so it's more convenient to take w as
-- argument there, rather than nesting it below the Σ[ z ∈ ... ] ...).
Z   : {μ ζ : ℕ∞} 
    → (S : Signature (μ) (ζ))
    → Σ[ z ∈ (ℕ → ℕ → ℕ) ](
        (w : ℕ) → (n : ℕ) → ((OpenTerms {μ} {ζ} S w n) ≃ (Fin $ z w n)))
Z {μ} {ζ} S = (z , p)
    where
        z = λ w → λ n → proj₁ (ZTheorem {μ} {ζ} S w n)
        p = λ w → λ n → proj₂ (ZTheorem {μ} {ζ} S w n)

--------------------------------------------------------------------------------
-- ZTheoremInhav and module ZSublemmas are deprecated.
-- #TODO: remove all this (first salvage the nice parts)
--------------------------------------------------------------------------------

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
    -- 1. OT 0 n ≃ Fin 0 since there are terms of weight 0.
    -- 2. for w = suc ŵ:
    --  OT w n ≡ (OT⁰ w n) ⊎ (OTᵉ w n) ⊎ (OTᵃ w n)
    --      where 
    --          OT⁰ w n are the terms in OT w n made with mk-nullary.
    --          OT⁼ w n are the terms in OT w n made with mk-multiary,
    --              i.e., constructors without any aguments applied.
    --          OTᵃ w n are the terms in OT w n made with giveArg,
    --              i.e., constructors with one or more arguments applied.
    -- 3. OT⁰ w (suc n) ≃ Fin 0 always, 
    --      because nullary constructors don't need arguments. 
    --    OT⁰ w 0 ≃ Fin 1 if there are at least w nullary constructors,
    --      and OT⁰ w 0 ≃ ⊥ otherwise; 
    --      only the term with index w-1 has weight w,
    --      but it doesn't exist if the set of nullary constructors
    --      is smaller than Fin w.
    -- 3. OTᵉ w n ≃ Fin 1 if there are at least w constructors
    --      and the constructor with index w-1 has arity n.
    --      Otherwise OTᵉ w n ≃ Fin 0
    -- 4. showing OTᵃ w n ≃ Fin (żᵃ w n) is the only hard case.
    --      How many open terms of the form `giveArg t a`
    --      of weight w needing n more arguments exist?
    --      Well note the following data is required to build such a term:
    --          - weights wₜ and wₐ such that wₐ + wₜ ≡ w.
    --              There are w-1 = ŵ such choices (see point 6 below).
    --          - A base term t ∈ OT wₜ (suc n) ≃ Fin(ż wₜ n)
    --          - An argument a ∈ OT wₐ 0       ≃ Fin(ż wₐ 0)
    --      The last two equivalences can be obtained via Well-Founded (ℕ, <)
    --      recursion on w when defining the ZTheoremInhab via <-rec;
    --      the reasoning is as follows:
    --      since both weights are inhabited we must have wₜ ≥ 1 and wₐ ≥ 1, 
    --      so if w ≡ wₐ + wₜ then both wₐ < w and wₜ < w must hold. 
    --      Consequently, we can make recursive calls with arguments wₐ and wₜ.
    -- 5. So define 
    --  OTᵃ w n ≔ Σ[(wₜ,wₐ,p) ∈ Splits w](OT wₜ (suc n)) × (OT wₐ 0)
    --          ≃ Σ[Fin( ŵ )] Fin(ż wₜ n) × Fin(ż wₐ 0)
    -- 6. Here `Splits w` (for any w ≗ suc ŵ) is the set of splits of w into 
    --      two non-zero numbers that sum to w.
    --      Formally:
    --          Splits w ≔ Σ[x ∈ ℕ]Σ[y ∈ ℕ](suc x + suc y ≡ w)
    --      Note that x ∈ {0, ..., w-2} ≃ Fin w-1 ≃ Fin ŵ,
    --      and choosing an x fixes the only
    --      possible choice of y already as 
    --          suc y ≡ w - suc x = ŵ - x
    --              so
    --          y ≡ ŵ - x - 1
    --      which has exactly one solution for all x ∈ {0, ..., ŵ-1},
    --      if ŵ ≥ 1 and none if ŵ ≡ 0, but then x ∈ ⊥ anyway.
    --      Hence the solutions are in bijection to the choice of x ∈ Fin ŵ.

    --_<∞b_ : ℕ∞ → ℕ∞ → Bool
    --_<∞b_ = ? 
    ----^ Just a placeholder. Maybe it's better to prove `Decidable _<∞_`.

    --z⁰ : ℕ → ℕ → ℕ
    --z⁰ w (suc n) = 0 -- No nullary constructors take arguments.
    --z⁰ 0 0 = 0       -- All terms have weight at least one.
    --z⁰ (suc w) 0 = if (fin $ ℕ.suc w) <∞b (suc∞ ζ) then 1 else 0

    ---- The definition below doesn't type check, since we don't know
    ---- if w ≡ c. Need decide: either define OT⁰ ≔ Fin (z⁰ n w)
    ---- xor add a `w ≡ cardToℕ c` and a subst in the final equaltion.
    --OT⁰ : ℕ → ℕ → Set
    --OT⁰ w n = Fin (z⁰ n w)

    --Splits : ℕ → Set
    --Splits w = Σ[ x ∈ ℕ ] Σ[ y ∈ ℕ ](ℕ.suc x + ℕ.suc y ≡ w)
    --splitsSize : ℕ → ℕ
    --splitsSize 0 = 0
    --splitsSize 1 = 1
    --splitsSize (suc (suc w)) = ℕ.suc w
    --splitsFin : (w : ℕ) → Splits w ≃ Fin (splitsSize w)
    --splitsFin w = ?

    --OTᵃ : ℕ → ℕ → Set
    --OTᵃ w n = Σ[ (wₜ , wₐ , p) ∈ Splits w ] (OT wₜ (ℕ.suc n)) × (OT wₐ 0)
    --zᵃ : ℕ → ℕ → ℕ
    --zᵃ w n = ? 
    --    --^ should be ℕ-sum_{wₜ , wₐ , p ∈ Splits W} (z wₜ (suc n)) * (z wₐ 0)
    --    --^ This needs two <-rec recursive calls.
    
    --Eq-OTᵃ : ℕ → ℕ → Set
    --Eq-OTᵃ w n = OTᵃ w n ≃ Fin (zᵃ w n)

    --OTᵉ : ℕ → ℕ → Set
    --OTᵉ 0 n = ⊥
    --OTᵉ w@(suc w') n = Σ[ c ∈ cardToSet (suc∞ ζ) ] 
    --                        ((fin w) <∞ (suc∞ ζ)) 
    --                        × (arity {suc∞ μ} {suc∞ ζ} {S} c ≡ n) 
    --                        × cardToℕ c ≡ w'
    --zᵉ : ℕ → ℕ → ℕ
    --zᵉ = ? -- 1 if (w ≤ ζ and arity (w - 1) ≡ n) else 0.
    --Eq-OTᵉ : ℕ → ℕ → Set
    --Eq-OTᵉ w n = OTᵉ w n ≃ Fin (zᵉ w n)

    --ZsubDecompo
    --    : (w n : ℕ)
    --    → OT w n ≃ (OT⁰ w n) ⊎ (OTᵉ w n) ⊎ (OTᵃ w n)
    --ZsubDecompo w n = ? -- make case distinction on constructors, see Lotem 4.

    --ż : ℕ → ℕ → ℕ
    --ż w n = (z⁰ w n) + (zᵉ w n) + (zᵃ w n)

    --ZMain
    --    : (w n : ℕ)
    --    → OT w n ≃ Fin (ż w n)
    --ZMain w n =
    --    begin 
    --        OT w n
    --    ≃⟨ ZsubDecompo w n ⟩
    --        ((OT⁰ w n) ⊎ (OTᵉ w n) ⊎ (OTᵃ w n))
    --    ≃⟨ ? ⟩ -- Use Eq-OT̂* for * ∈ {0,a,e} and some ⊎-congruence lemmas.
    --        (Fin (z⁰ w n) ⊎ Fin (zᵉ w n) ⊎ Fin (zᵃ w n))
    --    ≃⟨ ? ⟩ -- General lemma about summing Fin sets 
    --           -- (applied under ≃-under-⊎-rewriting)
    --           -- Maybe first sum the left and middle, if that's more convenient
    --           -- with associativity.
    --        (Fin (z⁰ w n) ⊎ Fin (zᵉ w n + zᵃ w n))
    --    ≃⟨ ? ⟩
    --        Fin (z⁰ w n + zᵉ w n + zᵃ w n)
    --    ≃⟨ ≃-refl ⟩
    --        Fin (ż w n)
    --    ∎
        
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
    ≃⟨ rewr-≃-rightOf-Σ $ Cw-to-Finz ∘ j ⟩
        (Σ[ n ∈ ℕ ] (Fin $ ℕ.suc $ z $ j n))
    -- 3. A ℕ-indexed sum of nonempty finite sets is _≃_ to ℕ.
    ≃⟨ jumpTheoremInhabitJumper {C} a₀ J z ⟩
        ℕ
    ∎
    

