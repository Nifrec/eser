# How to use the Well-Founded recursion tools of the stdlib
The stdlib gives a lot of tools for getting Well-Founded recursion principles
out of a Well-Founded relation, but those tools are poorly documented and
confusingly typed (too many layers of abstraction).

*This text assumes you already know how to prove a relation is WF, i.e., that
all elements are accessible.*

## Recursion structures
In `Relation.Unary.PredicateTransformer`:
```agda
PT : Set a → Set b → (ℓ₁ ℓ₂ : Level) → Set _
PT A B ℓ₁ ℓ₂ = Pred A ℓ₁ → Pred B ℓ₂
```
This is the type of functions that map a predicate on `A` into
a predicate on `B`.
I think of things like `All` and `Any` that lift a predicate on `A`
into a predicate on `List A`.

In `Induction`:
```agda
-- A RecStruct describes the allowed structure of recursion. The
-- examples in Data.Nat.Induction should explain what this is all
-- about.

RecStruct : Set a → (ℓ₁ ℓ₂ : Level) → Set _
RecStruct A = PT A A
```
The comment is a bit obscure, but it is to be used as follows.
You first choose your type `A` (for example, `ℕ`),
and design a function `Rec : RecStruct A` that lifts predicates on `A`
into other predicates on `A`.
This will be used as follows.
For any predicate `P` on `A` you get another predicate `Q := Rec A P`
with the intent that, for all `a ∈ A`, `Q a → P a`.

### Natural numbers example
For example, consider mathematical induction on `ℕ`.
We know that, to prove `(n : ℕ) → P n`, we need to show
`P 0` and `P n → P (S n)`. So `Q 0 := ⊤` and `Q (S n) := P n`.
Indeed, `Data.Nat.Induction` defines exactly this:
```agda
-- Ordinary induction

Rec : ∀ ℓ → RecStruct ℕ ℓ ℓ
Rec ℓ P zero    = ⊤
Rec ℓ P (suc n) = P n
```

## Recursor builder
The recursor builder gives the type of the induction principle.
It does not prove the induction principle (i.e., giving a term of that type),
only the *type* thereof.
In `Induction`:
```agda
-- A recursor builder constructs an instance of a recursion structure
-- for a given input.

RecursorBuilder : RecStruct A ℓ₁ ℓ₂ → Set _
RecursorBuilder Rec = ∀ P → Rec P ⊆′ P → Universal (Rec P)
```
If `Q := Rec P`, then `Rec P ⊆′ P` means `(a : A) → Q a → P a`,
as explained above, which encodes the usual premises of the induction principle.
And `Universal (Rec P)` just means `(a : A) → Q a`,
i.e., showing the premises of the induction principle always hold.
In `Induction` we also have a slight variant, which has final type that
expresses that `P` instead of `Q` always holds: the desired output of our
induction principle!
```agda
-- A recursor can be used to actually compute/prove something useful.

Recursor : RecStruct A ℓ₁ ℓ₂ → Set _
Recursor Rec = ∀ P → Rec P ⊆′ P → Universal P
```

Showing that all premises (`Q a`) 
always hold and that the premises imply the desired predicates (`Q a → P a`)
allows to conclude that `P a` always hold:
after all, given some `a`, we just plug in the proof of `Q a` to the proof of `Q
a → P a` and get `P a`.
This lemma is also in `Induction`:
```agda
-- And recursors can be constructed from recursor builders.

build : RecursorBuilder Rec → Recursor Rec
build builder P f x = f x (builder P f x)
```
Note that `f` is a proof that `(a : A) → (Q a → P a)`,
and `builder` gives a proof that this implies `Universal Q`,
so `builder P f x : Q x` and hence feeding that to `f x : Q x → P x`
gives a term of type `P x`, as desired!

### Back to natural numbers
In `Data.Nat.Induction`:
```agda
recBuilder : RecursorBuilder (Rec ℓ)
recBuilder P f zero    = _
recBuilder P f (suc n) = f n (recBuilder P f n)

rec : Recursor (Rec ℓ)
rec = build recBuilder
```
Which gives our familiar induction principle in `rec`.
Note that `recBuilder P f zero` should be of type `Univeral Q 0 ≗ Q 0 ≗ ⊤`,
so is trivial.
`recBuilder P f (suc n)` should be of type `Universal Q (suc n) ≗ Q (suc n)`,
and `f n : Q n → P n` and `recBuilder P f n : Univeral Q n ≗ Q n`,
so this indeed gives a term of type `P n`, which is the same type as `Q (suc
n)`, as desired.

## Well-Founded recursion
The stdlib gives standard tools to extract a recursion structure
and induction principle out of a Well-Founded relation.

In `Induction.WellFounded`:
```agda
-- When using well-founded recursion you can recurse arbitrarily, as
-- long as the arguments become smaller, and "smaller" is
-- well-founded.

WfRec : Rel A r → ∀ {ℓ} → RecStruct A ℓ _
WfRec _<_ P x = ∀ {y} → y < x → P y
```
Here we get that `Q x` is defined as '`P` holds for all smaller elements',
i.e., `(y : A) → y < x → P y`. 
For a WF-relation we know that these elements are all accessible,
i.e., that the set of small elements is finite.

You can apply it to the subset of accessible elements or to the the whole type,
if all elements are acessible; I will explain the latter here.
```agda
-- Well-founded induction for all elements, assuming they are all
-- accessible:

module All {_<_ : Rel A r} (wf : WellFounded _<_) ℓ where

  wfRecBuilder : RecursorBuilder (WfRec _<_ {ℓ = ℓ})
  wfRecBuilder P f x = Some.wfRecBuilder P f x (wf x)

  wfRec : Recursor (WfRec _<_)
  wfRec = build wfRecBuilder

  wfRec-builder = wfRecBuilder
```
`wfRecBuilder P f x = Some.wfRecBuilder P f x (wf x)` builds for each `x : A`
the `Q` as explained above for all `_< x` accessible elements.

### How to use it for your own WF-relation
`Data.Nat.Induction` gives a clear example:
```agda
module _ {ℓ : Level} where
  open WF.All <-wellFounded ℓ public
    renaming ( wfRecBuilder to <-recBuilder
             ; wfRec        to <-rec
             )
    hiding (wfRec-builder)
```
where `<-wellFounded : WellFounded _<_` is a proof that your desired relation is
well-founded. 
Now `<-rec` is the desired induction principle.
(Note you can also get the recursion structure, i.e., the '`Q'`, as
```agda
<-Rec : RecStruct ℕ ℓ ℓ
<-Rec = WfRec _<_
```
but you probably rarely need this).

### Example instantiation
The predicate and defined function (just constant `(0, 0)` really)
are boring, but this does show how the types normalise 
and how it recovers the strong induction principle.
Note that the type of `f` is computed via `WfRec`.
```agda
P : ℕ → Set
P n = ℕ × ℕ

test : (n : ℕ) → P n
test = <-rec {0ℓ} P f
    where
        f : (x : ℕ) → ({y : ℕ} → (y < x) → P y) → P x
        f 0 rec = (0 , 0)
        f (suc n) rec = rec {n} (n<1+n n)
```
