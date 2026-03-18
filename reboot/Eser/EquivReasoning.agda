-- In Relation.Binary.PropositionalEquality.Properties there's the stuff below.
-- I want to do it for _≃_ as well!

-- This is a special instance of `Relation.Binary.Reasoning.Setoid`.
-- Rather than instantiating the latter with (setoid A), we reimplement
-- equation chains from scratch since then goals are printed much more
-- readably.
--
--

≃-refl : {A : Set} → (A ≃ A)
≃-refl = StillTODO

-- #TODO: figure out the right arguments to those things to work with _≃_.
-- Or instantiate the setoid version?
module ≃-Reasoning where
  open begin-syntax {A = Set} _≃_ id public
  open ≃-syntax ? ? ? public
  open end-syntax {A = Set} _≃_ ≃-refl public
