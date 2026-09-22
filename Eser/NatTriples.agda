-- Module      : Eser.NatTriples
-- Description : Well-founded lexicographical order on ℕ×ℕ×ℕ.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_ ; _≟_ )
open import Data.Bool.Properties using (T-≡)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Nullary
open import Relation.Binary.Definitions 
open import Relation.Unary
open import Relation.Binary.Core using (Rel)
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_ ; id)

open import Level using (0ℓ)
open import Data.Vec
open import Data.Vec.Relation.Binary.Lex.Strict 
    renaming (<-wellFounded to Lex-wellFounded ; <-trans to lex-trans)
open import Data.Nat.Properties
open import Induction.WellFounded
open import Data.Nat.Induction
open import Induction.WellFounded

open import Eser.Aux using (_≈_)

module Eser.NatTriples where

_lex3_ : Rel (Vec ℕ 3) 0ℓ
_lex3_ = Lex-< {0ℓ} {0ℓ} {0ℓ} {ℕ} _≡_ _<_ {3} {3}

toVec : ℕ × ℕ × ℕ → Vec ℕ 3
toVec (n , m , l) = n ∷ m ∷ l ∷ []
toTriple : Vec ℕ 3 → ℕ × ℕ × ℕ
toTriple (n ∷ m ∷ l ∷ []) = (n , m , l)


_<<<_ : Rel (ℕ × ℕ × ℕ) 0ℓ
s <<< t = (toVec s) lex3 (toVec t)

toVec∘toTriple≈id : (toVec ∘ toTriple) ≈ id
toVec∘toTriple≈id (n ∷ m ∷ l ∷ []) = refl

Lex3-rec
    : (P : Vec ℕ 3 → Set)
    → ((t : Vec ℕ 3)
       → ({ s : Vec ℕ 3 } → s lex3 t → P s)
       → P t)
    → ((t : Vec ℕ 3) → P t)
Lex3-rec P H = wfRec 0ℓ P H
    where
        ≡-resp : {x : ℕ} → _<_ x Respects _≡_
        ≡-resp {x} {y} {y} refl x<y = x<y 
        open Induction.WellFounded.All (
            Lex-wellFounded {0ℓ} {ℕ} {0ℓ} {0ℓ} {_≡_} {_<_} trans ≡-resp 
            <-wellFounded {3}) 

<<<-rec
    : (P : (ℕ × ℕ × ℕ) → Set)
    → ((t : (ℕ × ℕ × ℕ))
       → ({ s : (ℕ × ℕ × ℕ) } → s <<< t → P s)
       → P t)
    → ((t : (ℕ × ℕ × ℕ)) → P t)
<<<-rec P H t@(x , y , z) = Lex3-rec (P ∘ toTriple) H' (toVec t)
    where
        H'  : (v : Vec ℕ 3) 
            → ({ w : Vec ℕ 3 } → w lex3 v → P (toTriple w) ) 
            → P (toTriple v)
        H' v IH = H (toTriple v) IH'
            where
                IH' : { s : (ℕ × ℕ × ℕ) } → s <<< (toTriple v) → P s
                IH' {s@(n , m , l)} s<<<v = IH {toVec s} 
                    $ subst (toVec s lex3_) (toVec∘toTriple≈id v) s<<<v

first-<-to-<<<
    : (m n l x y z : ℕ)
    → m < x
    → (m , n , l) <<< (x , y , z)
first-<-to-<<< m n l x y z m<x = this m<x refl

second-<-to-<<<
    : (a n l y z : ℕ)
    → n < y
    → (a , n , l) <<< (a , y , z)
second-<-to-<<< a n l y z n<y = next refl $ this n<y refl

third-<-to-<<<
    : (a b l z : ℕ)
    → l < z
    → (a , b , l) <<< (a , b , z)
third-<-to-<<< a b l z l<z = next refl $ next refl $ this l<z refl
