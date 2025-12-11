module PrefixSuffix where

open import Data.List.Relation.Binary.Prefix.Heterogeneous 
-- The above library defines:
--   data Prefix : REL (List A) (List B) (a ⊔ b ⊔ r) where
--  []  : ∀ {bs} → Prefix [] bs
--  _∷_ : ∀ {a b as bs} → R a b → Prefix as bs → Prefix (a ∷ as) (b ∷ bs)
--  But this does not seem the right definition of a prefix to me,
--  let me show.
--


open import Data.List
open import Data.Nat
open import Relation.Binary.PropositionalEquality

L' : List ℕ
L' = (1 ∷ 1 ∷ [])

L : List ℕ
L = (1 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ [])

lemma : Prefix (_≡_) L' L 
lemma = refl ∷ refl ∷ []

--  Oh I already see!
--  They define a prefix of 
--      a_n ∷ a_{n-1} ∷ a_{n-2} ∷ ... ∷ a_0 ∷ []
--  to be of the form 
--      a_n ∷ a_{n-1} ∷ ... ∷ a_m ∷ []
--  with m ≤ n.
--  I was expecting 
--      a_m ∷ a_{m-1} ∷ a_{m-2} ∷ ... ∷ a_0 ∷ []
--  with m ≤ n.
--  So I want a *suffix* then!

open import Data.List.Relation.Binary.Suffix.Heterogeneous

-- This exports:
--data Suffix : REL (List A) (List B) (a ⊔ b ⊔ r) where
--    here  : ∀ {as bs} → Pointwise R as bs → Suffix as bs
--    there : ∀ {b as bs} → Suffix as bs → Suffix as (b ∷ bs)

L'' : List ℕ
L'' = (0 ∷ 1 ∷ [])

-- Import needed to get the constructors in scope for the proof.
open import Data.List.Relation.Binary.Pointwise
lemma2 : Suffix (_≡_) L'' L
-- Proof: first skip with a bunch of 'there's the prefix of L till
-- the point from which it is onwards exactly the same as L'',
-- then prove pointwise equality (_≡_-equality) on that point.
lemma2 = there (there (there (there (there (there (here (_≡_.refl ∷ _≡_.refl ∷ [])))))))
