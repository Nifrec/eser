-- Module      : Eser.Vec
-- Description : Additional properties of Vec.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
open import Level hiding (suc)
--open import Data.Bool using (Bool ; true) renaming (T to IsTrue)
open import Data.Nat
open import Data.Nat.Properties
--open import Data.Sum hiding (reduce ; map)
--open import Data.Product hiding (map)
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
--open ≡-Reasoning -- renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Relation.Unary using (_⊆_)
open import Data.Vec
open import Data.Vec.Membership.Propositional as Mem
--open import Data.Vec.Relation.Unary.All as All hiding (_∷_ ; head ; tail ;
--map)
open import Data.Vec.Relation.Unary.Any as Any hiding (head ; tail ; map)
open import Function hiding (_↔_)

open import Eser.NewSigStream.EnumVectors using (weight)

module Eser.Vec where

-- Replace all occurrences of one element in a vector by another element.
replace-all 
    : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → {n : ℕ}
    → (v : Vec A n)
    → A -- Element to replace all occurrences of.
    → A -- Replacement.
    → Vec A n
replace-all {A} _≡?_ v a b = map replace-if-matches v
    module ReplaceAllImpl where
        replace-if-matches : A → A
        replace-if-matches x = cases (x ≡? a)
            module Cases where
                cases : (Dec (x ≡ a)) → A
                cases (yes _) = b
                cases (no _) = x

replace-all-not-member
    : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → {n : ℕ}
    → (v : Vec A n)
    → (x x' : A)
    → x ∉ v
    → replace-all _≡?_ v x x' ≡ v
replace-all-not-member _≡?_ [] x x' x∉v = refl
replace-all-not-member _≡?_ (y ∷ ys) x x' x∉v = 
    begin 
        replace-all _≡?_ (y ∷ ys) x x'
    ≡⟨⟩
        replace-if-matches y ∷ map replace-if-matches ys
    ≡⟨⟩
        cases (y ≡? x) ∷ map replace-if-matches ys
    ≡⟨⟩
        cases (y ≡? x) ∷ replace-all _≡?_ ys x x'
    ≡⟨ cong (cases (y ≡? x) ∷_) $ replace-all-not-member _≡?_ ys x x' x∉ys ⟩
        cases (y ≡? x) ∷ ys
    ≡⟨ cong (λ d → cases d ∷ ys) $ dec-no (y ≡? x) y≢x  ⟩
        cases (no y≢x) ∷ ys
    ≡⟨⟩
        y ∷ ys
    ∎ 
    where
        open ≡-Reasoning
        open ReplaceAllImpl _≡?_ (y ∷ ys) x x'
        open ReplaceAllImpl.Cases _≡?_ (y ∷ ys) x x' y
        y≢x : y ≢ x
        y≢x y≡x = x∉v (Any.here $ sym y≡x)
        x∉ys : x ∉ ys
        x∉ys = x∉v ∘ Any.there


replace-all-weight-<
    : {n : ℕ}
    → {v : Vec ℕ n}
    → {x' x : ℕ}
    → x ∈ v
    → x' < x
    → weight (replace-all _≟_ v x x') < weight v
replace-all-weight-< {suc n'} {x ∷ ys} {x'} {x} (here refl) x'<x = 
    begin-strict
        weight (replace-all _≟_ (x ∷ ys) x x')  
    ≡⟨⟩
        replace-if-matches x + weight (replace-all _≟_ ys x x')  
    ≡⟨⟩
        repl-cases (x ≟ x) + weight (replace-all _≟_ ys x x')  
    ≡⟨ cong (λ d → repl-cases d + weight (replace-all _≟_ ys x x'))
        (dec-yes-irr (x ≟ x) ≡-irrelevant refl)
     ⟩
        repl-cases (yes refl) + weight (replace-all _≟_ ys x x')  
    ≡⟨⟩
        x' + weight (replace-all _≟_ ys x x')  
    ≤⟨ +-monoʳ-≤ x' (rec (x ∈? ys)) ⟩
        x' + weight ys
    <⟨ +-monoˡ-< (weight ys) x'<x ⟩
        x + weight ys
    ≡⟨⟩
        weight (x ∷ ys)
    ∎
    where
        open ≤-Reasoning
        open ReplaceAllImpl _≟_ (x ∷ ys) x x'
        open ReplaceAllImpl.Cases _≟_ (x ∷ ys) x x' x 
            renaming (cases to repl-cases)
        open import Data.Vec.Membership.DecPropositional {A = ℕ} (_≟_) 
            hiding (_∈_)
        rec : (Dec (x ∈ ys)) → weight (replace-all _≟_ ys x x') ≤ weight ys
        rec (yes x∈ys) = (<⇒≤ $ replace-all-weight-< x∈ys x'<x)
        rec (no x∈ys) =
            begin 
                weight (replace-all _≟_ ys x x')
            ≡⟨ cong weight $ replace-all-not-member _≟_ ys x x' x∈ys ⟩
                 weight ys
            ≤⟨ ≤-refl ⟩
                 weight ys
            ∎
replace-all-weight-< {suc n'} {y ∷ ys} {x'} {x} (there x∈ys) x'<x =
    begin-strict
        weight (replace-all _≟_ (y ∷ ys) x x')  
    ≡⟨⟩
        replace-if-matches y + weight (replace-all _≟_ ys x x')  
    ≡⟨⟩
        u + weight (replace-all _≟_ ys x x')  
    <⟨ +-monoʳ-< u $ replace-all-weight-< {n'} {ys} {x'} {x} x∈ys x'<x ⟩
        u + weight ys
    ≤⟨ +-monoˡ-≤ (weight ys) (u≤y (y ≟ x) refl) ⟩
        y + weight ys
    ≡⟨⟩
        weight (y ∷ ys)
    ∎
    where
        open ≤-Reasoning
        open ReplaceAllImpl _≟_ (x ∷ ys) x x'
        open ReplaceAllImpl.Cases _≟_ (x ∷ ys) x x' y
        u : ℕ
        u = replace-if-matches y
        u≤y : (d : Dec (y ≡ x)) → (d ≡ (y ≟ x)) → u ≤ y
        u≤y (yes y≡x) eq = 
            begin 
                replace-if-matches y
            ≡⟨⟩
                cases (y ≟ x)
            ≡⟨ cong cases (sym eq) ⟩
                cases (yes y≡x)
            ≡⟨⟩
                x'
            ≤⟨ <⇒≤ x'<x ⟩
                x
            ≡⟨ sym y≡x ⟩
                y
            ∎
        u≤y (no y≢x) eq =
            begin 
                replace-if-matches y
            ≡⟨⟩
                cases (y ≟ x)
            ≡⟨ cong cases (sym eq) ⟩
                cases (no y≢x)
            ≡⟨⟩
                y
            ∎
    
