-- Module      : PartialRecordMatching
-- Description : Test with pattern matching records
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Short experiment that shows that it is possible to pattern match on
-- only some fields of a record.
--
-- Use case: very convenient when needing to match a Signoid against
-- its cardinality but not all the other fields.

module PartialRecordMatching where

open import Data.Nat
open import Data.List

record Foo : Set where
    constructor mkFoo
    field
        bar : ℕ
        baz : List ℕ
        meh : ℕ

-- We only match on the `baz` field.
-- Note that we don't just get the field value, 
-- but really match on the possible constuctions that may occur in this field.
fooOut : Foo → ℕ
fooOut record {baz = []} = 0
fooOut record {baz = (x ∷ xs)} = suc x
