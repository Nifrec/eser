-- Module      : StreamGrids.Examples.Enumeration
-- Description : Examples of enumarable types
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

module StreamGrids.Examples.Enumeration2 where

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
--  * appending 'a' or 'b' as FIRST character is a unary constructor.
--      So αa = appA(α) where α ∈ {a, b}*.
--  Lexicographical order:
--  <>, a, b, aa, ab, ba, bb, aaa, aab, etc.
--  (so a := 0 and b := 1 doesn't give the binary numbers!)
--------------------------------------------------------------------------------

data AB* : Set where
    empty   : AB*
    appA    : AB* → AB*
    appB    : AB* → AB*

appAinj : {x y : AB*} → appA x ≡ appA y → x ≡ y
appAinj refl = refl

appBinj : {x y : AB*} → appB x ≡ appB y → x ≡ y
appBinj refl = refl

decEqAB* : DecidableEquality AB*
decEqAB* empty empty = yes refl
decEqAB* empty (appA y) = no λ { () }
decEqAB* empty (appB y) = no λ { () }
decEqAB* (appA x) empty = no λ { () }
decEqAB* (appA x) (appA y) with decEqAB* x y
... | yes p = yes (cong appA p)
... | no x≢y = no λ { appAx≡appAy → x≢y (appAinj appAx≡appAy) }
decEqAB* (appA x) (appB y) = no λ { () }
decEqAB* (appB x) empty = no λ { () }
decEqAB* (appB x) (appA y) = no λ { () }
decEqAB* (appB x) (appB y) with decEqAB* x y
... | yes p = yes (cong appB p)
... | no x≢y = no λ { appBx≡appBy → x≢y (appBinj appBx≡appBy) }

numElAB* : ℕ∞
numElAB* = ∞

len : AB* → ℕ
len empty = zero
len (appA s) = suc (len s)
len (appB s) = suc (len s)

_<lex_ : Rel AB* 0ℓ
empty <lex empty = ⊥
empty <lex appA β = ⊤
empty <lex appB β = ⊤
appA α <lex empty = ⊥
appA α <lex appA β = α <lex β
appA α <lex appB β = α ≡ β  ⊎ α <lex β
--^ αa <lex βb holds already if α = β or α <lex β.
appB α <lex empty = ⊥
appB α <lex appA β = α <lex β
--^ αb <lex βa only if α <lex β
appB α <lex appB β = α <lex β
--^ αb <lex βb only if α <lex β

test5 : appA (appB empty) <lex appB (appB empty)
test5 = inj₁ refl
test6 : ¬ (appA (appB empty) <lex appB (empty))
test6 (inj₁ ())
test6 (inj₂ ())

-- (α β γ : AB*) → (α <lex β) → (β <lex γ) → (α <lex γ)
lexTrans : Transitive _<lex_
lexTrans {empty} {appA β} {appA γ} α<β β<γ = tt
lexTrans {empty} {appA β} {appB γ} α<β β<γ = tt
lexTrans {empty} {appB β} {appA γ} α<β β<γ = tt
lexTrans {empty} {appB β} {appB γ} α<β β<γ = tt
lexTrans {appA α} {appA β} {appA γ} α<β β<γ = lexTrans {α} {β} {γ} α<β β<γ
lexTrans {appA α} {appA β} {appB γ} α<β (inj₁ β≡γ) 
    = let α<γ = subst (λ δ → α <lex δ) β≡γ α<β in
    inj₂ α<γ
lexTrans {appA α} {appA β} {appB γ} α<β (inj₂ β<γ)
    = inj₂ (lexTrans {α} {β} {γ} α<β β<γ)
lexTrans {appA α} {appB β} {appA γ} (inj₁ α≡β) β<γ
    = let α<γ = subst (λ δ → δ <lex γ) (sym α≡β) β<γ in
    α<γ
lexTrans {appA α} {appB β} {appA γ} (inj₂ α<β) β<γ 
    = lexTrans {α} {β} {γ} α<β β<γ
lexTrans {appA α} {appB β} {appB γ} (inj₁ α≡β) β<γ
    = let α<γ = subst (λ δ → δ <lex γ) (sym α≡β) β<γ in
    inj₂ α<γ
lexTrans {appA α} {appB β} {appB γ} (inj₂ α<β) β<γ 
    = inj₂ (lexTrans {α} {β} {γ} α<β β<γ)
lexTrans {appB α} {appA β} {appA γ} α<β β<γ = lexTrans {α} {β} {γ} α<β β<γ
lexTrans {appB α} {appA β} {appB γ} α<β (inj₁ β≡γ)
    = let α<γ = subst (λ δ → α <lex δ) β≡γ α<β in
    α<γ
lexTrans {appB α} {appA β} {appB γ} α<β (inj₂ β<γ)
    = lexTrans {α} {β} {γ} α<β β<γ
lexTrans {appB α} {appB β} {appA γ} α<β β<γ = lexTrans {α} {β} {γ} α<β β<γ
lexTrans {appB α} {appB β} {appB γ} α<β β<γ = lexTrans {α} {β} {γ} α<β β<γ

lexIrrefl : Irreflexive _≡_ _<lex_
--lexIrrefl {x} {y} x≡y x<y = ?
lexIrrefl {empty} {empty} p ()
lexIrrefl {empty} {appA x} () q
lexIrrefl {empty} {appB x} () q
lexIrrefl {appA x} {appA y} xa≡ya x<y = 
    let x≡y = appAinj xa≡ya in lexIrrefl x≡y x<y
lexIrrefl {appB x} {appB y} xb≡yb x<y =
    let x≡y = appBinj xb≡yb in lexIrrefl x≡y x<y

lexDec : Decidable _<lex_
lexDec empty empty = no (lexIrrefl {empty} {empty} (refl))
lexDec empty (appA y) = yes tt
lexDec empty (appB y) = yes tt
lexDec (appA x) empty = no λ { () }
lexDec (appA x) (appA y) = lexDec x y
lexDec (appA x) (appB y) with lexDec x y
... | yes x<y = yes (inj₂ x<y)
... | no x≮y with decEqAB* x y
...     | yes x≡y = yes (inj₁ x≡y)
...     | no x≢y = no λ { (inj₁ p) → x≢y p ; (inj₂ q) → x≮y q }
lexDec (appB x) empty = no λ { () }
lexDec (appB x) (appA y) = lexDec x y
lexDec (appB x) (appB y) = lexDec x y

--------------------------------------------------------------------------------
-- Trichotometry and auxiliary lemmas
--------------------------------------------------------------------------------

lexEqImplIncomp : {x y : AB*} → (x ≡ y) → ¬ (x <lex y)
lexEqImplIncomp {x} {y} refl = lexIrrefl {x} refl

x<y→xa<ya : {x y : AB*} → (x <lex y) → (appA x <lex appA y)
x<y→xa<ya {x} {y} p = p

x<y⊎y<x→xa<ya⊎ya<xa 
    : {x y : AB*} 
    → (x <lex y ⊎ y <lex x) 
    → (appA x <lex appA y ⊎ appA y <lex appA x)
x<y⊎y<x→xa<ya⊎ya<xa {x} {y} (inj₁ p) = inj₁ (x<y→xa<ya {x} {y} p)
x<y⊎y<x→xa<ya⊎ya<xa {x} {y} (inj₂ p) = inj₂ (x<y→xa<ya {y} {x} p)

-- Previous two lemmas with appB i.o. appA
x<y→xb<yb : {x y : AB*} → (x <lex y) → (appB x <lex appB y)
x<y→xb<yb {x} {y} p = p

x<y⊎y<x→xb<yb⊎yb<xb 
    : {x y : AB*} 
    → (x <lex y ⊎ y <lex x) 
    → (appB x <lex appB y ⊎ appB y <lex appB x)
x<y⊎y<x→xb<yb⊎yb<xb {x} {y} (inj₁ p) = inj₁ (x<y→xb<yb {x} {y} p)
x<y⊎y<x→xb<yb⊎yb<xb {x} {y} (inj₂ p) = inj₂ (x<y→xb<yb {y} {x} p)

lexNeqImplComp : {x y : AB*} → (x ≢ y) → (x <lex y) ⊎ (y <lex x)
--lexNeqImplComp {x} {y} x≢y = ?
lexNeqImplComp {empty} {empty} x≢y = 
    let contradiction = x≢y (refl) in ⊥-elim contradiction
lexNeqImplComp {empty} {appA y} x≢y = inj₁ tt
lexNeqImplComp {empty} {appB y} x≢y = inj₁ tt
lexNeqImplComp {appA x} {empty} x≢y = inj₂ tt
lexNeqImplComp {appA x} {appA y} xa≢ya =
    let rec = lexNeqImplComp x≢y in
    x<y⊎y<x→xa<ya⊎ya<xa {x} {y} rec
    where 
        x≢y : x ≢ y
        x≢y x≡y = xa≢ya (cong appA x≡y)
lexNeqImplComp {appA x} {appB y} x≢y = {! !} -- use lexDec!!!
lexNeqImplComp {appB x} {empty} x≢y = inj₂ tt
lexNeqImplComp {appB x} {appA y} x≢y = {!  !}
lexNeqImplComp {appB x} {appB y} xb≢yb =
    let rec = lexNeqImplComp x≢y in
    x<y⊎y<x→xb<yb⊎yb<xb {x} {y} rec
    where 
        x≢y : x ≢ y
        x≢y x≡y = xb≢yb (cong appB x≡y)

lexTri : Trichotomous _≡_ _<lex_
lexTri x y with decEqAB* x y
... | yes x≡y = 
    let x≮y = lexEqImplIncomp x≡y in
    let y≮x = lexEqImplIncomp (sym x≡y) in
    tri≈ x≮y x≡y y≮x
... | no x≢y with (lexDec x y) -- don't do `with`, use lemma above!
...     | yes p = ?
...     | no q = ?

--------------------------------------------------------------------------------
-- Incrementing strings (getting the next string in lexicographical order).
-- This gives, inductively, an enumeration of all strings.
--------------------------------------------------------------------------------
increment : AB* → AB*
increment empty = appA empty
increment (appA s) = appB s
increment (appB s) = appA (increment s)

test1 : increment empty ≡ appA empty
test1 = refl
test2 : increment (appB (appA ( empty))) ≡ appA (appB empty)
test2 = refl
test3 : increment (appB (appB ( empty))) ≡ appA (appA (appA empty ))
test3 = refl

enumAB* : ℕ → AB*
enumAB* zero = empty
enumAB* (suc n) = increment (enumAB* n)

-- Testing enumAB* on inputs 0 to 7:
someNums : List AB*
someNums 
    = (enumAB* 0) 
    ∷ (enumAB* 1) 
    ∷ (enumAB* 2) 
    ∷ (enumAB* 3) 
    ∷ (enumAB* 4) 
    ∷ (enumAB* 5) 
    ∷ (enumAB* 6) 
    ∷ (enumAB* 7) 
    ∷ []
expected : List AB*
expected 
    = (empty) 
    ∷ (appA empty)
    ∷ (appB empty)
    ∷ (appA (appA empty))
    ∷ (appB (appA empty))
    ∷ (appA (appB empty))
    ∷ (appB (appB empty))
    ∷ appA (appA (appA empty))
    ∷ []
test4 : someNums ≡ expected
test4 = refl

incrMakesBigger : (α : AB*) →  α <lex increment α
incrMakesBigger empty = tt
incrMakesBigger (appA α) = inj₁ refl
incrMakesBigger (appB α) = incrMakesBigger α

incrMono : (α β : AB*) → (α <lex β) → increment α <lex increment β
incrMono empty (appA empty) p = inj₁ refl
incrMono empty (appA (appA β)) p = inj₂ tt
incrMono empty (appA (appB β)) p = inj₂ tt
incrMono empty (appB empty) p = tt
incrMono empty (appB (appA β)) p = tt
incrMono empty (appB (appB β)) p = tt
incrMono (appA α) (appA β) p = p
incrMono (appA α) (appB β) (inj₁ α≡β) = 
    let β<incrβ = incrMakesBigger β in
    subst (λ δ → δ <lex increment β) (sym α≡β) β<incrβ
incrMono (appA α) (appB β) (inj₂ α<β) =
    let β<incrβ = incrMakesBigger β in
    lexTrans {α} {β} {increment β} α<β β<incrβ
incrMono (appB x) (appA y) p with (decEqAB* (increment x) y)
... | yes q = inj₁ q
... | no q = inj₂ ?
incrMono (appB α) (appB β) p = incrMono α β p

--incrMono : (α β : AB*) → (α <lex β) → increment α <lex increment β
--incrMono empty (appA empty) p = inj₁ refl
--incrMono empty (appA (appA β)) p = inj₂ tt
--incrMono empty (appA (appB β)) p = inj₂ tt
--incrMono empty (appB empty) p = tt
--incrMono empty (appB (appA β)) p = tt
--incrMono empty (appB (appB β)) p = tt
--incrMono (appA α) (appA β) p = p
--incrMono (appA α) (appB β) (inj₁ α≡β) = 
--    let β<incrβ = incrMakesBigger β in
--    subst (λ δ → δ <lex increment β) (sym α≡β) β<incrβ
--incrMono (appA α) (appB β) (inj₂ α<β) =
--    let β<incrβ = incrMakesBigger β in
--    lexTrans {α} {β} {increment β} α<β β<incrβ
--incrMono (appB empty) (appA (appA empty)) p = inj₁ refl
--incrMono (appB empty) (appA (appA (appA β))) p = inj₂ tt
--incrMono (appB empty) (appA (appA (appB β))) p = inj₂ tt
--incrMono (appB empty) (appA (appB empty)) p = inj₂ (inj₁ refl)
--incrMono (appB empty) (appA (appB (appA β))) p = inj₂ (inj₂ tt)
--incrMono (appB empty) (appA (appB (appB β))) p = inj₂ (inj₂ tt)
--incrMono (appB (appA α)) (appA (appA β)) p = inj₂ p
--incrMono (appB (appA α)) (appA (appB β)) (inj₁ x) 
--    = inj₁ (cong (λ δ → appB δ) x)
--incrMono (appB (appA α)) (appA (appB β)) (inj₂ y) = inj₂ y 
--incrMono (appB (appB empty)) (appA (appA (appA empty))) p = inj₁ refl
--incrMono (appB (appB empty)) (appA (appA (appA (appA β)))) p = inj₂ tt
--incrMono (appB (appB empty)) (appA (appA (appA (appB β)))) p = inj₂ tt
--incrMono (appB (appB empty)) (appA (appA (appB empty))) p = inj₂ (inj₁ refl)
--incrMono (appB (appB empty)) (appA (appA (appB (appA β)))) p = inj₂ (inj₂ tt)
--incrMono (appB (appB empty)) (appA (appA (appB (appB β)))) p = inj₂ (inj₂ tt)
--incrMono (appB (appB (appA α))) (appA (appA (appA β))) p = inj₂ p 
--incrMono (appB (appB (appA α))) (appA (appA (appB β))) (inj₁ x) = 
--    inj₁ (cong (λ δ → appA (appB δ)) x)
--incrMono (appB (appB (appA α))) (appA (appA (appB β))) (inj₂ y) = inj₂ y
--incrMono (appB (appB (appB α))) (appA (appA (appA empty))) p = {! !}
--incrMono (appB (appB (appB α))) (appA (appA (appA (appA β)))) p = {! !}
--incrMono (appB (appB (appB α))) (appA (appA (appA (appB β)))) p = {! !}
--incrMono (appB (appB (appB α))) (appA (appA (appB β))) p = {! !}
--incrMono (appB (appB α)) (appA (appB β)) p = {! !}
--incrMono (appB α) (appB β) p = incrMono α β p

monoAB*
    : (n : ℕ)
    → (( fin (suc n)) <∞ numElAB*)
    → enumAB* n <lex enumAB* (suc n)
monoAB* zero p = tt
-- Goal: increment (enumAB* n) <lex enumAB* (2+ n)
-- But that's (by def of `increment`) the same as:
-- Goal: increment (enumAB* n) <lex increment (enumAB* (suc n))
-- So it suffices to show that `increment` is monotone, and then we can simply
-- apply this monoticity to the induction hypothesis.
monoAB* (suc n) p = ?
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

