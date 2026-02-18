# To discuss 18 Feb 2026

## Progress
* Simplified the diagram.
    The formal definitions in Agda are slightly different from the handwritten
    ones.
    I managed to prove all the correspondences in the diagram in Agda.
    Main theorems:

in `Eser/Correspondences`:
```agda
FRFHomot : (F : NFFun) → (proj₁ ∘ RelToFun ∘ FunToRel) F ≈ proj₁ F

RFRHomot 
    : (R : DecEquiv) 
    → (uncurry ∘ proj₁ ∘ FunToRel ∘ RelToFun) R ≈ (uncurry ∘  proj₁) R

-- This one is trivial!:
RelToFunPresvProps
    : (P : LocalisibleProp)
    → (R : DecEquiv)
    → Prel P R ↔ AllRestr ((proj₁ ∘ RelToFun) R) (Ploc P)

FunToRelPresvProps
    : (P : LocalisibleProp)
    → (f : NFFun)
    → Prel P (FunToRel f) ↔ AllRestr (proj₁ f) (Ploc P)
```

## Localisible properties
* I realised: FinitaryRelationProperty <-> LocalisibleRelationProperty
    truth-preserving mapping between them, for relations on ℕ×ℕ.
    **Should I prove in Agda?**
* Proof of preservation of localisible properties in one direction
    is trivial: it is exactly the definition of localisible!
    Is this OK or problematic?

## Potential TODOs
**Let's set priorities for next meeting!**, options:
[ ] LaTex:Write section §2 (the correspondence theorem I just proved in Agda).
[ ] Agda : Cleanup Agda code.
[ ] Agda : Prove `f (f n) ≡ f n` and `f n ≤ n` are a localisible property.
[ ] Agda : Start implementing §3: tools for signatures.
[ ] Agda : Implement construction quotient type from NFFun.
[ ] Read: W-types.

## Other high-prio things
* Can't prove homotopy for `R : ℕ → ℕ → Bool` but `R : ℕ×ℕ → bool` works.
    But proved everything else for `R : ℕ → ℕ → Bool`,
    and used `uncurry` in main statement.
    Makes main statement less elegant, but otherwise have to change everything.
    Which option is best?
* Do we have a target conference/journal?
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
