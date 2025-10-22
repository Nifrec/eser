-- Module      : Alphabets
-- Description : Representations of atomic path pieces
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Alphabets are finite, linearly ordered, 
-- non-empty collections of symbols, that serve as atomic path pieces.
-- Paths in a grid are strings over an alphabet.
--------------------------------------------------------------------------------
-- Implementation notes:
-- * I also considered representing alphabets just as a non-0 natural number.
--      `suc n` would then represent the alphabet `Fin (suc n)` with the usual
--      _<_ on natural numbers.
--      But then path pieces have no sensible names,
--      unless one also provides an external naming function
--      `Fin (suc n) → MySetOfNames`.
-- * This definition of Alphabets is not practical.
--      It depends on the non-contructive ≢ 
--      which causes a lot of unnecessary headaches...

module StreamGridsAlphabet where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

data Alphabet (X : Set) : Set 
data notInAlphabet {X : Set} : Alphabet X → X → Set

data Alphabet X where
    least   : X → Alphabet X
    add     : (A : Alphabet X) → (x : X) → notInAlphabet A x → Alphabet X

data notInAlphabet {X} where
    singleton : {x x' : X} → (x ≢ x') → notInAlphabet (least x) x'
    addNew    : (x x' : X) 
              → (x ≢ x') 
              → (A : Alphabet X) 
              → (px : notInAlphabet A x) 
              → (px' : notInAlphabet A x') 
              → (notInAlphabet (add A x px) x')

data αβγAtoms : Set where
   α : αβγAtoms
   β : αβγAtoms
   γ : αβγAtoms

αβγ : Alphabet αβγAtoms
αβγ = 
    let A1 = least α in
    let A2 = addNew α β ? A1 (singleton {α} {β} ?) in
    addNew β γ ? 

      
