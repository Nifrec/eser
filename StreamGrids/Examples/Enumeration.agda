-- Module      : StreamGrids.Examples.Enumeration
-- Description : Examples of enumarable types
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

module StreamGrids.Examples.Enumeration where

-- #TODO: probably not all of these are needed.
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.Empty
open import Data.Fin
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.String
open import Data.Sum
open import Data.Unit
open import Data.Vec
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import StreamGrids.Enumeration


--------------------------------------------------------------------------------
-- A finite set of 3 elements.
--------------------------------------------------------------------------------
data ABC : Set where
    a : ABC
    b : ABC
    c : ABC

-- The order on ABC is a < b < c.
_<ABC_ : Rel ABC 0ℓ
a <ABC b = ⊤
a <ABC c = ⊤
b <ABC c = ⊤
_ <ABC _ = ⊥

numElABC : ℕ∞
numElABC = fin 3

enumABC : ℕ → ABC
enumABC 0 = a
enumABC 1 = b
enumABC _ = c

-- Monotonicity of `enumABC`:
monoABC : 
    (n : ℕ) → 
    ((fin (suc n)) <∞ numElABC) 
    → enumABC n <ABC enumABC (suc n)
monoABC zero p = tt 
    --^ a < b
monoABC (suc zero) p = tt
    --^ b < c
monoABC (2+ n) (s≤s (s≤s (s≤s ())))
    --^ Nothing else to show because we already exceeded numEl

-- Surjectivity of `enumABC`:
surjABC 
    : (x : ABC)
    → Σ[ n ∈ ℕ ]((fin n <∞ numElABC) × (enumABC n ≡ x))
surjABC a = (0 , s≤s z≤n , refl)
surjABC b = (1 , s≤s (s≤s z≤n) , refl)
surjABC c = (2 , ≤-refl , refl)

IsEnumABC : Enumeration ABC _<ABC_ _≡_
IsEnumABC = record {
    numEl = numElABC ;
    enum  = enumABC ;
    monotone = monoABC ;
    surj = surjABC
    }

--------------------------------------------------------------------------------
-- Infinite set: strings over the alphabet {a, b}
-- (NOT isomorphic to binary numbers! 
-- I was initially confused about this!).
-- Encoding: 
--  * empty string is nullary constructor.
--  * appending 'a' or 'b' is a unary constructor.
--  Lexicographical order:
--  <>, a, b, aa, ab, ba, bb, aaa, aab, etc.
--  (so a := 0 and b := 1 doesn't give the binary numbers!)
--------------------------------------------------------------------------------

data AB* : Set where
    empty   : AB*
    appA    : AB* → AB*
    appB    : AB* → AB*

numElAB* : ℕ∞
numElAB* = ∞

len : AB* → ℕ
len empty = zero
len (appA s) = suc (len s)
len (appB s) = suc (len s)

-- Increment a string in {a, b}̂* by interpreting the string as a binary number.
-- Return a string of the same length, and whether or not a carry bit remains.
-- E.g.
-- incrRec  : a   → (b, 0)
--          : b   → (a, 1)
--          : abb → (baa, 0)
--          : bbb → (aaa, 1)
--incrRec : AB* → AB* × Fin 2
--incrRec empty = (empty , suc zero)
--incrRec (appA s) with incrRec s
--... | (s' , zero) = (appA s' , zero)
--... | (s' , suc zero)    = (appB s' , zero)
--incrRec (appB s) with incrRec s
--... | (s' , zero) = (appB s' , zero)
--... | (s' , suc zero)    = (appA s' , suc zero)

OnlyBs : AB* → Set
OnlyBs empty = ⊤
OnlyBs (appA s) = ⊥
OnlyBs (appB s) = OnlyBs s

incrRec : (s : AB*) → (OnlyBs s) ⊎ Σ[ s' ∈ AB* ] (len s ≡ len s')
incrRec empty = inj₁ tt
incrRec (appA s) with incrRec s
... | inj₁ _ = inj₂ (appB s , refl)
... | inj₂ (s' , sameLen) = inj₂ (appA s , refl)
incrRec (appB s) with incrRec s
... | q = ?

----increment : AB* → AB*
----increment s with incrRec s
----... | (s' , zero) = s'
----... | (s' , suc zero) = appA s'
----increment : AB* → AB*
----increment s =
----    let (s' , carry) = incrRec s in
----    if ((toℕ carry) ≡ᵇ zero) then s' else (appA s')

--test1 : increment empty ≡ appA empty
--test1 = refl
--test2 : increment (appB (appA ( empty))) ≡ appB (appB empty)
--test2 = refl
--test3 : increment (appB (appB ( empty))) ≡ appA (appA (appA empty ))
--test3 = refl

--enumAB* : ℕ → AB*
--enumAB* zero = empty
--enumAB* (suc n) = increment (enumAB* n)

---- Testing enumAB* on inputs 0 to 7:
--someNums : List AB*
--someNums 
--    = (enumAB* 0) 
--    ∷ (enumAB* 1) 
--    ∷ (enumAB* 2) 
--    ∷ (enumAB* 3) 
--    ∷ (enumAB* 4) 
--    ∷ (enumAB* 5) 
--    ∷ (enumAB* 6) 
--    ∷ (enumAB* 7) 
--    ∷ []
--expected : List AB*
--expected 
--    = (empty) 
--    ∷ (appA empty)
--    ∷ (appB empty)
--    ∷ (appA (appA empty))
--    ∷ (appA (appB empty))
--    ∷ (appB (appA empty))
--    ∷ (appB (appB empty))
--    ∷ appA (appA (appA empty))
--    ∷ []
--test4 : someNums ≡ expected
--test4 = refl

--_<lex_ : Rel AB* 0ℓ
--empty <lex empty = ⊥
--empty <lex appA y = ⊤
--empty <lex appB y = ⊤
--appA x <lex empty = ⊥
--appA x <lex appA y = x <lex y
--appA x <lex appB y = len x Data.Nat.≤ len y
----^ Note that if y <lex x but len x ≡ len y, 
----  then appA x <lex appB y still holds!
----  a∷s <lex b∷s' for all s, s' with the same length.
--appB x <lex empty = ⊥
--appB x <lex appA y = len x Data.Nat.< len y
----^ b∷s is greater than a∷s' as soon as len s ≥ len s'.
--appB x <lex appB y = x <lex y

--test5 : appA (appB empty) <lex appB (appB empty)
--test5 = ≤-refl
--test6 : ¬ (appA (appB empty) <lex appB (empty))
--test6 = λ { x → n≮0 x }

--monoAB*
--    : (n : ℕ)
--    → (( fin (suc n)) <∞ numElAB*)
--    → enumAB* n <lex enumAB* (suc n)
--monoAB* zero p = tt
--monoAB* (suc n) p with (incrRec (enumAB* n))
--... | empty , zero = tt
--... | empty , suc zero = ≤-refl
--... | appA fst , zero = {! !}
--... | appA fst , suc snd = {! !}
--... | appB fst , snd = {! !}
----monoAB* (suc n) p with (enumAB* (suc n) , enumAB* (suc (suc n)))
----... | empty , empty = {! !}
----... | empty , appA s' = {! !}
----... | empty , appB s' = {! !}
----... | appA s , s' = {! !}
----... | appB s , s' = {! !}
----monoAB* (suc n) p with enumAB* (suc n)
----... | empty = tt
----... | appA q = {! !}
----... | appB q = {! !}

