-- Module      : ITETypes
-- Description : Trying out if-then-else statements in type-level functions
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

module practise.ITETypes where

-- Problem 1: given `f : X → X`,
-- Wanted: dependent function `g : Π(x : X) → if f(x) = x then A else B`
-- where `f : X → X`, `A, B : Set`. 
-- Note: we want judgemental equality here!
--typeOfG : {X : Set} (f : X → X) (A B : Set) → (x : X) → Set
--typeOfG f A B x with f x
--typeOfG f A B x | x = A
--typeOfG f A B x | _ = B

--typeOfG : {X : Set} (f : X → X) (A B : Set) → (x y : X) → Set
--typeOfG f A B x x = A
--typeOfG f A B x y = B

--data Kip (A B X : Set) (f : X → X) : Set where
--    same : 
    
open import Data.Bool
open import Data.List hiding (all)
open import Data.Nat
-- Problem 2: given `P : X → Bool`, we want 
--  `h : Π (l : List X) → if all (x ∈ L) have P(x) then A else B`.
-- I managed to solve this problem!!! :)

-- This apparently already exists! Only with the order of arguments swapped.
-- But that gives me a deprecation warning.
all : {X : Set} → (P : X → Bool) → List X → Bool
all P [] = true
all P (x ∷ xs) = (P x) ∧ (all P xs)

typeOfH : {X : Set} (A B : Set) (P : X → Bool) (l : List X) → Set
typeOfH A B P l with (all P l)
typeOfH A B P l | true = A
typeOfH A B P l | false = B

A : Set
A = ℕ
B : Set
B = Bool
X : Set
X = ℕ
P : X → Bool
P = (λ x → 10 ≡ᵇ x)

h : (l : List X) → (typeOfH A B P l)
h l with (all P l)
h l | true = 0 -- Is in A
h l | false = false -- is in B
