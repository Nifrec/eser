--------------------------------------------------------------------------------
-- These things were removed from Eser.EqRel.Definitions.
--------------------------------------------------------------------------------
_⊢_~_ : {A : Set} → (A → A → Bool) → Rel A 0ℓ
R ⊢ n ~ m = R n m ≡ true


-- Type of predicates on a relation 
-- (Not necessarily proof irrelevant
-- since that's simply a bit inconvenient to implement in Agda --
-- the `Prop` sort is not vanilla and experimental,
-- and adding proofs of proof-irrelevance via Σ is overcomplicating things).
RelPred : Set₁
RelPred = EqRel → Set

-- Property of a function.
FunPred : Set₁
FunPred = (ℕ → ℕ) → Set

-- Equivalence relations that also have a given property.
EqRelWithProp : RelPred → Set
EqRelWithProp P = Σ[ R ∈ DecRel ] Σ[ Req ∈ IsEquivalence (R ⊢_~_) ] (P (R , Req))

-- #TODO: remove?
NFFunWithProp : FunPred → Set
NFFunWithProp P = Σ[ f ∈ (ℕ → ℕ) ] ( NFLeq f × NFFix f × P f)


--------------------------------------------------------------------------------
-- Normal-form functions and locally-defined predicates on them.
--------------------------------------------------------------------------------
-- Get the first n outputs of a function ℕ → ℕ as a vector.
-- Equivalently, restrict the domain to {0, 1, ..., n-1}.
restrict : (n : ℕ) → (ℕ → ℕ) → Vec ℕ n
restrict 0 f = []
restrict (suc n) f = (f n) ∷ (restrict n f)

-- Decidable locally defined predicate.
-- For each n, judge whether the restriction of a function ℕ → ℕ
-- to {0, ..., n-1} satisfies the predicate.
LocPred : Set₁
LocPred = (n : ℕ) → Vec ℕ n → Set

-- Predicate that all restrictions of a function satisfy a
-- locally defined property.
AllRestr : (ℕ → ℕ) → LocPred → Set
AllRestr f P = (n : ℕ) → P n (restrict n f)

-- #TODO: remove?
-- Local version of NFLeq: f m ≤ m for all m,
-- where f m is encoded as the value of a vector at index 0.
NFLeqLoc : LocPred
NFLeqLoc n v = (m : Fin n) → lookup v m ≤ toℕ m

NFFunWithLocPred : LocPred → Set
NFFunWithLocPred P = Σ[ f ∈ (ℕ → ℕ) ] (
      NFLeq f
    × NFFix f
    × AllRestr f P)
