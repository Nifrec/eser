# A taxonomy of "IsNF"
5 January 2026, writing out thoughts and reflections on normal forms.

## Defining NF via constuctors used in the choice
An element is a normal form if it is either the root choicelog
or added to the choicelog via the `choose h lc` constructor
using the `newNF` constructor for `lc : LegalChoices`.
So far so good, all obvious.

But there still are a few things to deambiguate when trying to define
the predicate `IsNF`. In particular, with respect to *what* is an element
normal?
From low level to abstract we should distinguish the following definitions
of `IsNF`:
1. **Normality of a state:** 
    `IsNFState : Q → Set`.
    This is true if the lastmost chosen element is in normal form
    in the given choicelog,
    simply by pattern matching and checking if the
    `root` or `choose ... newNf` construct was used.
2. **Normality *in* a state:** 
    `IsNFInState : (q : Q) → (i : C) → (i<idxq : i <C q) → Set`.
    Element-index `i` is a normal form if its corresponding
    subchoicelog `q'` (`getSubLog`, which strips down a choicelog 
    to the point `q'` where `i` was the lastmost choice) 
    satisfies `IsNFState q'`.
3. **Normality in a *StreamGrid*:**
    `IsNFInSG : Decider → C → Set`
    The predicate `IsNFInSG D i` checks for normality in `iterTill D i`,
    i.e., the choicelog created by following the choices according to `D`.

### Remark
Definitions 1. and 2. above do *not* need to be defined with respect to a
decider. The input choicelogs could have been build by some noncomputable
alternation using an assemble of deciders, for example.
But states are, at type level, still sufficiently well-formed to speak of normal
forms, and they still encode a partial equivalence relation.
We just can't assume they are all constructed via the StreamGrids algorithm.

## Defining normal forms via NFLists
The output of `nfGlobalIdx` should, of course, be a normal form.
This function, on input `i`,
builds a choicelog inductively via the StreamGrids algorithm until the 
point where `i` becomes chosen.
How do we prove that this returns a normal form?
Well it always outputs an element from the normal form list.
But we just defined normality via *sublogs*, not via the normal forms lists!
Of course, they are tightly related (since a new element is added to a NFList
iff the `newNF` constructor is used), but not the same definition.

Checking normality via NFLists is easy: just check list membership.

```agda
IsListNF : Decider → C → Set
IsListNF D i = i ∈ (nflist (iterTill S D i))
-- #TODO: this is still a proposition.
-- It is using `Data.List.Membership.Setoid.Properties.unique⇒irrelevant`
-- if one can show `Unique (nflist q)` for all `q : Q`,
-- which ought to be easily provable.
```

**Maybe this definition of normal form is easier in the first place.**
It is what I've been doing in `StreamGrids/States` already anyway.
And easier to check, while still an hProp (see comment in snippet above,
still needs to be proven). 
Proving that `nfGlobalIdx` outputs a NF becomes now easy, since the output of
`lookup (nflist (iterTill i))` is obviously always an element
of `nflist (iterTill i)`, but this being-an-element-of-that is exactly how
we defined `IsListNF`!

## Coherence requirements
It can be proven that an element is in the NFList iff the corresponding
output of `getSubLog` uses the `root` xor `choose ... newNF ...` construct.
I have not formalised this in Agda (yet), since there was no need for it (yet).
