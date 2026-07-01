# Indexed Inductive Types Cardinality problems
Author: Lulof Pirée
Date:   1 July 2026

For some indexed inductive types (IITs) it is easy to see their cardinality is
that of ℕ.
For example vectors:
```agda
data Vec (A : Set) : (n : ℕ) → Set where
    empty : Vec A 0
    cons  : {n : ℕ} → (a : A) → Vec A n → Vec A (suc n)
```
As soon as you have some `a : A` and some vector `Vec A n` of **any index** `n`
you can create infinitely many terms with `cons`.

The construction of open terms is already different, because it adds constraints
on the recursive arguments.
In simplified notation, let `Snul` and `Smul` be the types of nullary and
multiary operators of a signature `S`, and let `ar : Smul → ℕ` give the
arity-minus-one. Then:
```agda
data OT : (n : ℕ) → Set where
    nul : Snul → OT 0
    mul : (t : Smul) → OT (suc (ar t))
    giveArg : {n : ℕ} → OT (suc n) → OT 0 → OT n
```
Here, we do not know if we can apply `giveArg` given some open term,
because we need an open term **specifically of index 0**.
In this example it is still easy to figure out when they exist
(namely exactly when `Snul` is inhabited).

But we can make this also arbitrarily hard.
```agda
data P : (n : ℕ) → Set where
    a : P 7
    b : P 8 → P 4
    c : {n : ℕ} → P n → P (13 + n) → P (2 + n)
    d : {n : ℕ} → P (5 + n) → P 117 → P (7 + n)
    d : {n : ℕ} → P (6 + n) → P (7 + n)

```
I cannot immediately tell if there are infinitely many terms constructible.
Nor whether a term of `P 221` can be constructed.

**Theorem**
*There does not exist an algorithm for checking whether an*
*natural-number indexed inductive type `X : ℕ → Set`*
*has finite or infinite cardinality.*

*Proof sketch*
Reduction to the halting problem; for contradiction assume `f` to be such an
algorithm.

Take an arbitrary Turing machine `M` (on alphabet `Bool`)
(with states `Q`, initial state `q0`, halting states `QH`, transition function
`d`)
and an input string `x : List Bool`.
Let `X : ℕ → Set` be the IIT where `X n` denotes that "*`M` on input `x` has not
halted after `n` steps*.
We can implement it roughly like this:
```agda
data X : (n :ℕ) → Set where
    start : `q0 \notin QH` → X 0
    step  : {n : ℕ} → (p : X n) → d(transition M x p n) \notin QH → X (suc n)
```
where `(transition M x p n)` computes the next state of `M` starting from the
state and tape reached after `n` steps on input `x` (which is well-defined; the
argument `p` ensures this), which is a simple inductive function we can define
by mutual induction.
    
Now `f` can tell whether `X` has infinitely terms or only finitely many,
i.e., whether `M` on `x` halts or not. So `f` solves the halting problem:
contradiction! QED.
