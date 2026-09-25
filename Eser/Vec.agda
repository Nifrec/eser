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

        

    
