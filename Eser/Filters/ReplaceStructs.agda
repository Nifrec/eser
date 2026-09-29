-- Module     : Eser.Filters.ReplaceStructs
-- Description : Implementation-indendent abstraction of term algebras.
-- Copyright  : (c) Lulof Pirée, 2026
-- License    : AGPL-v3
-- Maintainer : Lulof Pirée
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_ ; _≟_ ; _≤?_ )
open import Data.Bool.Properties using (T-≡)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open ≡-Reasoning
open import Relation.Nullary
open import Relation.Binary.Definitions using (Decidable ; DecidableEquality 
    ; tri< ; tri≈ ; tri>)
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_ ; id)
open import Data.Maybe
open import Data.Maybe.Properties using (just-injective)

open import Data.Nat.Properties using (
    ≤-refl 
    ; ≤-trans 
    ; <-trans
    ; n≤1+n 
    ; ≡⇒≡ᵇ
    ; <-irrelevant
    ; n<1+n
    ; n≮0
    ; <-≤-trans
    ; ≤-<-trans
    ; m≤n⇒m<n∨m≡n
    ; n≮n
    ; ≰⇒>
    )

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun ; FunToRel)
open import Eser.Aux using (_↔_ ; _≈_ ; doubleSubst ; irrel-×-closure ; uip
    ; restIsProofIrrel
    )
open import Eser.Logic using 
    (true≢false 
    ; ≡→≡ᵇ 
    ; ≡ᵇ→≡ 
    ; decEqReflection
    ; decEqCoReflection
    ; is-false-to-not-true
    ; not-true-to-is-false
    )
open import Eser.NatTriples

open import Eser.Filters.Base
open import Eser.Filters.Properties
open import Eser.Filters.Resurface
open import Eser.Filters.PointwiseProperties
open import Eser.Filters.Conversions.NFFunToExence

module Eser.Filters.ReplaceStructs where

--------------------------------------------------------------------------------
-- Replacement Structures
--------------------------------------------------------------------------------
-- Terse encoding of an enumerable type A with a 'is-argument-of'
-- relation _⊂_. We omit the bijection A ≃ ℕ and work on ℕ directly.
-- Arguments must be smaller in the enumertion than the term containing them.
-- There is a `replace` operation such that `replace y x x'`
-- represents the term `y` with argument `x` substituted by `x'`.
-- We abstract from most implementation details of `replace`,
-- and do not even distinguish between replacing a 
-- single or all occurrences of `x`.
-- Replacing an argument by a smaller one must result
-- in a term that is overall smaller.
--
-- Implementation note
-- I first used the following fields:
--      _⊂_ : ℕ → ℕ → Set
--      ⊂-dec : Decidable _⊂_
-- but then a `ReplaceStruct` becomes a Set₁, and I feared this may become an
-- annoyance further down the road.

record ReplaceStruct : Set where
    field
        _is-arg-of_ : ℕ → ℕ → Bool

        -- Arguments are always smaller than the whole construction.
        ⊂-resp-< : (y x : ℕ) → x is-arg-of y ≡ true → x < y

        replace : ℕ → ℕ → ℕ → ℕ

        -- Replacing an argument by a smaller alternative reduces
        -- the size of the whole construction.
        replace-< 
            : (y x x' : ℕ) 
            → (x is-arg-of y ≡ true) 
            → (x' < x) 
            → (replace y x x' < y)

        -- Replacing one argument keeps the other arguments in place.
        keep 
            : (y x x' z : ℕ) 
            → (z is-arg-of y ≡ true) 
            → (x ≢ z)
            → (z is-arg-of (replace y x x') ≡ true)
        
        -- Negative analog of keep : when replacing x with x', and x'≢z,
        -- then z does not become an argument.
        nospawn 
            : (y x x' z : ℕ) 
            → (z is-arg-of y ≡ false) 
            → (x' ≢ z)
            → (z is-arg-of (replace y x x') ≡ false)

        -- When performing two non-overlapping replacements
        -- (the replacement of one is not the replacecant of the other),
        -- their order does not matter.
        -- The only case where this axiom adds something new is when both
        -- x ⊂ y and z ⊂ y. The cases when either or both x or z is not an arg
        -- of y are derivable from the other axioms; see the 'real' comm rule as
        -- a lemma below.
        halfcomm
            : (y x x' z z' : ℕ) 
            → x is-arg-of y ≡ true
            → z is-arg-of y ≡ true
            → x ≢ z
            → x ≢ z'
            → z ≢ x'
            → (replace (replace y z z') x x') ≡ (replace (replace y x x') z z')

        noeff
            : (y x x' : ℕ) 
            → (x is-arg-of y ≡ false) 
            → y ≡ replace y x x'

        eff
            : (y x x' : ℕ)
            → (x is-arg-of y ≡ true)
            → x' is-arg-of (replace y x x') ≡ true

        -- The 'real' cut rule follows from this and the other rules, 
        -- see below as a lemma.
        halfcut
            : (y x z a : ℕ)
            → replace (replace y x a) a z ≡ replace (replace y x z) a z

        id-rep
            : (y x : ℕ)
            → replace y x x ≡ y

        -- The replacement completely replaces ALL instances of an argument.
        complete
            : (y x x' : ℕ)
            → x ≢ x'
            → (x is-arg-of y ≡ true) 
            → (x is-arg-of (replace y x x')) ≡ false
--open ReplaceStruct

module ReplaceStructLemmas (T : ReplaceStruct) where
    open ReplaceStruct T
    rep : ℕ → ℕ → ℕ → ℕ
    rep = replace

    infixl 100 #_
    #_ : {b : Bool} → ¬ (b ≡ true) → b ≡ false
    #_ = not-true-to-is-false

    _⊂_ : ℕ → ℕ → Set
    _⊂_ n m = (_is-arg-of_ ) n m ≡ true

    _⊄_ : ℕ → ℕ → Set
    n ⊄ m = (_is-arg-of_ ) n m ≡ false

    _⊂?_ : (n m : ℕ) → Dec (n ⊂ m)
    n ⊂? m = ⊂?-cases (_is-arg-of_  n m) refl
        where
            ⊂?-cases : (b : Bool) → (_is-arg-of_  n m ≡ b) → Dec (n ⊂ m)
            ⊂?-cases true p = true because ofʸ p
            ⊂?-cases false p = false because ofⁿ 
                (is-false-to-not-true p)

    -- 'Full' comm rule without the x ⊂ y and z ⊂ y premises.
    comm
        : (y x x' z z' : ℕ) 
        → x ≢ z
        → x ≢ z'
        → z ≢ x'
        → (rep (rep y z z') x x') ≡ (rep (rep y x x') z z')
    comm y x x' z z' x≢z x≢z' z≢x' = cases (x ⊂? y) (z ⊂? y)
        where
            cases 
                : (Dec (x ⊂ y)) 
                → (Dec (z ⊂ y)) 
                → (rep (rep y z z') x x') ≡ (rep (rep y x x') z z')
            cases (yes x⊂y) (yes z⊂y) = 
                halfcomm y x x' z z' x⊂y z⊂y x≢z x≢z' z≢x'
            cases (no x⊄y) (no z⊄y)
                =
                begin 
                    rep (rep y z z') x x'
                ≡⟨ cong (λ y' → rep y' x x') $ sym $ noeff y z z' (# z⊄y) ⟩
                    rep y x x'
                ≡⟨ noeff (rep y x x') z z' z⊄ryxx' ⟩
                    rep (rep y x x') z z'
                ∎
                where
                    z⊄ryxx' : z is-arg-of (rep y x x') ≡ false
                    z⊄ryxx' = nospawn y x x' z (# z⊄y) (≢-sym z≢x') 
            cases (no x⊄y) (yes z⊂y) =
                begin 
                    rep (rep y z z') x x'
                ≡⟨ sym $ noeff (rep y z z') x x' x⊄ryzz' ⟩
                    rep y z z'
                ≡⟨ cong (λ y' → rep y' z z')
                    $ noeff y x x' (# x⊄y) ⟩
                    rep (rep y x x') z z'
                ∎
                where
                    x⊄ryzz' : x ⊄ rep y z z'
                    x⊄ryzz' = nospawn y z z' x (# x⊄y) (≢-sym x≢z')

            cases (yes x⊂y) (no z⊄y) = sym $
                begin 
                    rep (rep y x x') z z'
                ≡⟨ sym $ noeff (rep y x x') z z' z⊄ryxx' ⟩
                    rep y x x'
                ≡⟨ cong (λ y' → rep y' x x')
                    $ noeff y z z' (# z⊄y) ⟩
                    rep (rep y z z') x x'
                ∎
                where
                    z⊄ryxx' : z ⊄ rep y x x'
                    z⊄ryxx' = nospawn y x x' z (# z⊄y) (≢-sym z≢x')
        
    cut
        : (y x z a : ℕ)
        → a ⊄ y
        → rep (rep y x a) a z ≡ rep y x z
    cut y x z a a⊄y = 
        begin 
            rep (rep y x a) a z
        ≡⟨ halfcut y x z a ⟩
            rep (rep y x z) a z
        ≡⟨ eq (z ≟ a ) ⟩
            rep y x z
        ∎
        where
            eq : Dec (z ≡ a) → rep (rep y x z) a z ≡ rep y x z
            eq (yes refl) = id-rep (rep y x z) a
            eq (no z≢a) = sym $ noeff (rep y x z) a z a⊄y'
                where
                    a⊄y' : a  ⊄ (rep y x z)
                    a⊄y' = nospawn y x z a a⊄y z≢a

    idempotent
        : (y x x' x'' : ℕ)
        → x ≢ x'
        → rep (rep y x x') x x'' ≡ rep y x x'
    idempotent y x x' x'' x≢x' = sym $ noeff (rep y x x') x x'' x⊄yx
        where
            x⊄yx : x ⊄ (rep y x x')
            x⊄yx with x ⊂? y
            ... | yes x⊂y = complete y x x' x≢x' x⊂y
            ... | no ¬x⊂y = ans
                where
                    x⊄y = not-true-to-is-false ¬x⊂y
                    y≡yx : y ≡ rep y x x'
                    y≡yx = noeff y x x' x⊄y

                    ans : x ⊄ (rep y x x')
                    ans = subst (x ⊄_) y≡yx x⊄y

        
        
            
    -- Performing one replacement, then another, and then the first one again,
    -- has the same effect as only doing the last two replacements,
    -- provided that the middle replacement does not target the output of the first.
    lemma-replace-wxw
        : (y w w' x x' : ℕ)
        → x ≢ w
        → w' ≢ x
        → replace (replace (replace y w w') x x') w w' 
          ≡ 
          replace (replace y x x') w w'
    lemma-replace-wxw y w w' x x' x≢w w'≢x = 
        cases (w ≟ w') (w ⊂? y) (x ⊂? y) (w ≟ x')
        where
            yx : ℕ
            yx = replace y x x'
            yxw : ℕ
            yxw = replace yx w w'
            yw : ℕ
            yw = replace y w w'
            ywx : ℕ
            ywx = replace yw x x'
            ywxw : ℕ
            ywxw = replace ywx w w'

            cases 
                : Dec (w ≡ w')
                → Dec (w ⊂ y)
                → Dec (x ⊂ y)
                → Dec (w ≡ x')
                → ywxw ≡ yxw
            cases (yes refl) _ _ _ = 
                cong (λ y → rep (rep y x x') w w') (id-rep y w)
            cases (no w≢w') (no w⊄y) _ _ = 
                cong (λ y → rep (rep y x x') w w') (sym $ noeff y w w' 
                $ not-true-to-is-false w⊄y)
            cases (no w≢w') (yes w⊂y) (no x⊄y) _ = 
                begin 
                    rep (rep (rep y w w') x x') w w'
                ≡⟨ cong (λ y → rep y w w') $ sym $ noeff (rep y w w') x x' 
                   $ nospawn y w w' x (not-true-to-is-false x⊄y) w'≢x
                 ⟩
                    rep (rep y w w') w w'
                ≡⟨ idempotent y w w' w' w≢w' ⟩
                    rep y w w'
                ≡⟨ cong (λ y → rep y w w') 
                   $ noeff y x x' 
                   $ not-true-to-is-false x⊄y
                 ⟩
                    rep (rep y x x') w w'
                ∎
                
            cases (no w≢w') (yes w⊂y) (yes x⊂y) (no w≢x') =
                begin 
                    rep (rep (rep y w w') x x') w w'
                ≡⟨ cong (λ y → rep y w w') 
                   $ comm y x x' w w' x≢w (≢-sym w'≢x) w≢x'
                 ⟩
                    rep (rep (rep y x x') w w') w w'
                ≡⟨ idempotent (rep y x x') w w' w' w≢w' ⟩
                    rep (rep y x x') w w'
                ∎
            cases (no w≢w') (yes w⊂y) (yes x⊂y) (yes refl) = 
                begin 
                    rep (rep (rep y w w') x x') w w'
                ≡⟨⟩
                    
                    rep (rep (rep y w w') x w) w w'
                ≡⟨ cut (rep y w w') x w' w w⊄yw ⟩
                    rep (rep y w w') x w'
                ≡⟨ comm y x w' w w' x≢w (≢-sym w'≢x) w≢w' ⟩
                    rep (rep y x w') w w'
                ≡⟨ (sym $ halfcut y x w' w) ⟩
                    rep (rep y x w) w w'
                ≡⟨⟩
                    rep (rep y x x') w w'
                ∎
                where
                    w⊄yw : w ⊄ (rep y w w')
                    w⊄yw = complete y w w' w≢w' w⊂y

    ⊂-irrelevant : Relation.Binary.Irrelevant _⊂_
    ⊂-irrelevant p q = uip p q

-- Unused laws that would also make sense to more strictly describe term
-- algebras:
record ReplaceStructUnneededLawsCollection : Set where
    field
        -- These are copied from ReplaceStruct; 
        -- if ReplaceStructUnneededLawsCollection is ever to be used, 
        -- one had better merge the two records
        -- or give this one a parameter/field of value ReplaceStruct.
        _is-arg-of_ : ℕ → ℕ → Bool
        replace : ℕ → ℕ → ℕ → ℕ

        monotone
            : (y x x' x'' : ℕ)
            → (x is-arg-of y ≡ true) 
            → x' < x''
            → replace y x x' < replace y x x''
    

