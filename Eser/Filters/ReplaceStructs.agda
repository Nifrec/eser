-- Module      : Eser.Filters.ReplaceStructs
-- Description : Implementation-indendent abstraction of term algebras.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

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
        -- Arguments are always smaller than the while construction.
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
            → (x is-arg-of y ≡ true) 
            → (z is-arg-of y ≡ true) 
            → (x ≢ z)
            → (z is-arg-of (replace y x x') ≡ true)
        
        -- Negative analog of keep : when replacing x, and x'≢z,
        -- then z does not become an argument.
        nospawn 
            : (y x x' z : ℕ) 
            → (z is-arg-of y ≡ false) 
            → (x' ≢ z)
            → (z is-arg-of (replace y x x') ≡ false)
        -- When performing two non-overlapping replacements
        -- (the replacement of one is not the replacecant of the other),
        -- their order does not matter.
        comm
            : (y x x' z z' : ℕ) 
            → (x is-arg-of y ≡ true) 
            → (z is-arg-of y ≡ true) 
            → (x ≢ z')
            → (z ≢ x')
            → (replace (replace y z z') x x') ≡ (replace (replace y x x') z z')

        noeff
            : (y x x' : ℕ) 
            → (x is-arg-of y ≡ false) 
            → y ≡ replace y x x'

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
open ReplaceStruct

module ReplaceStructLemmas (T : ReplaceStruct) where
    rep : ℕ → ℕ → ℕ → ℕ
    rep = replace T

    _⊂_ : ℕ → ℕ → Set
    _⊂_ n m = (_is-arg-of_ T) n m ≡ true

    _⊄_ : ℕ → ℕ → Set
    n ⊄ m = (_is-arg-of_ T) n m ≡ false

    _⊂?_ : (n m : ℕ) → Dec (n ⊂ m)
    n ⊂? m = ⊂?-cases (_is-arg-of_ T n m) refl
        where
            ⊂?-cases : (b : Bool) → (_is-arg-of_ T n m ≡ b) → Dec (n ⊂ m)
            ⊂?-cases true p = true because ofʸ p
            ⊂?-cases false p = false because ofⁿ 
                (is-false-to-not-true p)

    cut
        : (y x z a : ℕ)
        → a ⊄ y
        → replace T (replace T y x a) a z ≡ replace T y x z
    cut y x z a a⊄y = 
        begin 
            rep (rep y x a) a z
        ≡⟨ halfcut T y x z a ⟩
            rep (rep y x z) a z
        ≡⟨ eq (z ≟ a ) ⟩
            rep y x z
        ∎
        where
            eq : Dec (z ≡ a) → rep (rep y x z) a z ≡ rep y x z
            eq (yes refl) = id-rep T (rep y x z) a
            eq (no  z≢a) = sym $ noeff T (rep y x z) a z a⊄y'
                where
                    a⊄y' : a  ⊄ (rep y x z)
                    a⊄y' = nospawn T y x z a a⊄y z≢a

    idempotent
        : (y x x' x'' : ℕ)
        → x ≢ x'
        → rep (rep y x x') x x'' ≡ rep y x x'
    idempotent y x x' x'' x≢x' = sym $ noeff T (rep y x x') x x'' x⊄yx
        where
            x⊄yx : x ⊄ (rep y x x')
            x⊄yx with x ⊂? y
            ... | yes x⊂y = complete T y x x' x≢x' x⊂y
            ... | no ¬x⊂y = ans
                where
                    x⊄y = not-true-to-is-false ¬x⊂y
                    y≡yx : y ≡ rep y x x'
                    y≡yx = noeff T y x x' x⊄y

                    ans : x ⊄ (rep y x x')
                    ans = subst (x ⊄_) y≡yx x⊄y

        
        
            
    -- Performing one replacement, then another, and then the first one again,
    -- has the same effect as only doing the last two replacements,
    -- provided that the middle replacement does not target the output of the first.
    lemma-replace-wxw
        : (y w w' x x' : ℕ)
        → w' ≢ x
        → replace T (replace T (replace T y w w') x x') w w' 
          ≡ 
          replace T (replace T y x x') w w'
    lemma-replace-wxw y w w' x x' w'≢x = 
        cases (w ≟ w') (w ⊂? y) (x ⊂? y) (w ≟ x')
        where
            yx  : ℕ
            yx  = replace T y x x'
            yxw : ℕ
            yxw = replace T yx w w'
            yw  : ℕ
            yw  = replace T y w w'
            ywx : ℕ
            ywx = replace T yw x x'
            ywxw : ℕ
            ywxw = replace T ywx w w'

            cases 
                : Dec (w ≡ w')
                → Dec (w ⊂ y)
                → Dec (x ⊂ y)
                → Dec (w ≡ x')
                → ywxw ≡ yxw
            cases (yes refl) _ _ _ = 
                cong (λ y → rep (rep y x x') w w') (id-rep T y w)
            cases (no w≢w') (no w⊄y) _ _ = 
                cong (λ y → rep (rep y x x') w w') (sym $ noeff T y w w' 
                $ not-true-to-is-false w⊄y)
            cases (no w≢w') (yes w⊂y) (no x⊄y) _ = 
                begin 
                    rep (rep (rep y w w') x x') w w'
                ≡⟨ cong (λ y → rep y w w') $ sym $ noeff T (rep y w w') x x' 
                   $ nospawn T y w w' x (not-true-to-is-false x⊄y) w'≢x
                 ⟩
                    rep (rep y w w') w w'
                ≡⟨ idempotent y w w' w' w≢w' ⟩
                    rep y w w'
                ≡⟨ cong (λ y → rep y w w') 
                   $ noeff T y x x' 
                   $ not-true-to-is-false x⊄y
                 ⟩
                    rep (rep y x x') w w'
                ∎
                
            cases (no w≢w') (yes w⊂y) (yes x⊂y) (no w≢x') =
                begin 
                    rep (rep (rep y w w') x x') w w'
                ≡⟨ cong (λ y → rep y w w') 
                   $ comm T y x x' w w' x⊂y w⊂y (≢-sym w'≢x) w≢x'
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
                ≡⟨ comm T y x w' w w' x⊂y w⊂y (≢-sym w'≢x) w≢w' ⟩
                    rep (rep y x w') w w'
                ≡⟨ (sym $ halfcut T y x w' w) ⟩
                    rep (rep y x w) w w'
                ≡⟨⟩
                    rep (rep y x x') w w'
                ∎
                where
                    w⊄yw : w ⊄ (rep y w w')
                    w⊄yw = complete T y w w' w≢w' w⊂y

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
    

