# To discuss 18 Feb 2026
## High priority

## Localisible properties
* I realised: FinitaryRelationProperty <-> LocalisibleRelationProperty
    truth-preserving mapping between them, for relations on ℕ×ℕ.
    **Should I prove in Agda?**
* Proof of preservation of localisible properties in one direction
    is trivial: it is exactly the definition of localisible!
    Is this OK or problematic?

## Other high-prio things
* Can't prove homotopy for `R : ℕ → ℕ → Bool` but `R : ℕ×ℕ → bool` works.
    But proved everything else for `R : ℕ → ℕ → Bool`,
    and used `uncurry` in main statement.
    Makes main statement less elegant, but otherwise have to change everything.
    Which option is best?
* Shulman's catlog is delightful book! 
    Interesting new angle/perspective on type theory and terms!
* I defined homotopy and <-> myself, stdlib provides *similar*
    (but confusing and just not exactly right) definitions.
* NFLeqLoc and NFFixLoc worth proving in Agda? Feels like big distractor,
    or at least low-prio.
* Just state theorems loose or really use 'NFFunsWithPropery ..."
* Lot of definitions that I left unused in the end, remove?

## Lower priority
* Ploc can be decidable in many cases. It is in all my examples. Checking
    whether a relation on finite set has a property is often easy and decidable,
    but on an infinite set not 
    (ℕ → ℕ → Bool is hard to define!
    (Fin n → Fin n → Bool) not!)
    This is an argument why locally extending a normal form function may be a
    useful tool: we can check (=compute) 
    for every potential extension whether it preserves the desired properties.
* Ploc : output a Bool or a Set?
    Really been in doubt for a long time!
* (This I want to discuss already for a long time): induction proof principle
    (every congruence contains the equality relation -- how is this useful?)
* Why do people do HoTT and cubical TT, when ≡ is just an inductive type
    with -- somewhat arbitrarily -- only the `refl` constructor.
    Why not allow types to supply their own equality relation?
    You still get induction principles etc...
