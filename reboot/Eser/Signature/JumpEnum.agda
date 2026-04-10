-- Module      : Eser.Signature.JumpEnum
-- Description : Equivalence between sums-of-fin-sets to natural numbers.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- The type Σ[ x ∈ ℕ ] Fin (f x) is equivalent to ℕ if infinitely
-- many `Fin (f x)`s are inhabited.
-- Having a function that maps from an inhabited x ∈ ℕ
-- to the next inhabited x' ∈ ℕ (so f(x) ≥ 1, f(x') ≥ 1, x' > x)
-- (and skipping over all intermediate x'' with f(x'') = 0)
-- is sufficient to establish the equivalence.

{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)
open import Data.Vec 
open import Function
open import Relation.Binary.Reasoning.Syntax
open import Data.Fin.Properties using (fromℕ<-toℕ ; toℕ-fromℕ< ; toℕ-injective)

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Card
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Aux
open import Eser.Signature.Definitions
open import Eser.Signature.PiecewiseFin using (noWeightlessTerms)
open import Eser.Logic using (elimCaseLeft ; elimCaseRight)
open import Eser.Monotone

module Eser.Signature.JumpEnum where

-- `iter f n a` returns fⁿ(a), i.e., f applied n times starting from a.
iter : {A : Set} → (A → A) → ℕ → A → A
iter {A} f 0 a = a
iter {A} f (suc n) a = f (iter f n a)

--------------------------------------------------------------------------------
-- Linearly searching forward
--
-- Starting from some n₀ ∈ ℕ, one can search all  {n > n₀ : n ∈ ℕ}
-- untill the smallest number greater than n that satisfies a predicate P,
-- provided that there is a guarrantee that this search will not take forever.
-- I.e., provided with an upper bound on n.
-- Such an upper bound can simply be a n' > n with a proof that P (n');
-- then we only need to check if there is a smaller n in {n₀ + 1, ..., n' ∸ 1}
-- that also satisfies P.
-- If not, this gives a proof that n' is the smallest.
--------------------------------------------------------------------------------
-- There is no number strictly inbetween n and n + 1.
emptyIval : (n : ℕ) → (ℓ : ℕ) → ¬ Between n (n + 1) ℓ
emptyIval n ℓ (n<ℓ , ℓ<n+1) = 
    let ℓ<SucN : ℓ < ℕ.suc n
        ℓ<SucN = subst (λ x → ℓ < x) 
                       (trans (+-suc n 0) (cong ℕ.suc $ +-identityʳ n))
                       ℓ<n+1
    in
    let H : ℓ < n ⊎ ℓ ≡ n
        H = m<1+n⇒m<n∨m≡n ℓ<SucN
    in
    let ℓ≡n : ℓ ≡ n
        ℓ≡n = elimCaseLeft H (λ ℓ<n → n≮n n (Data.Nat.Properties.<-trans n<ℓ ℓ<n))
    in
    n≮n n (subst (λ x → n < x) ℓ≡n n<ℓ)

IsLeastNext : (P : ℕ → Set) → (n₀ : ℕ) → (h : ℕ) → Set
IsLeastNext P n₀ h = 
                (P $ n₀ + (1 + h))
                ×
                ((ℓ : ℕ) → Between n₀ (n₀ + (1 + h)) ℓ → ¬ (P ℓ))

LeastNext : (P : ℕ → Set) → (n₀ : ℕ) → Set
LeastNext P n₀ = Σ[ h ∈ ℕ ] IsLeastNext P n₀ h

-- If n₀+1 does not satisfy P and no 0 ≤ h < F 
-- satisfies `P (n₀ + 1 + 1 + h)`
-- then no 0 ≤ h < F satisfies `P (n₀ + 1 + h)`.
extensionLemma
    : {P : ℕ → Set}
    → (decP : Relation.Unary.Decidable P)
    → (n₀ F : ℕ)
    → ¬ P (n₀ + 1)
    → ((ℓ : ℕ) → Between (n₀ + 1) (n₀ + 1 + (1 + F)) ℓ → ¬ P ℓ)
    → ((ℓ : ℕ) → Between n₀ (n₀ + (1 + ℕ.suc F)) ℓ → ¬ P ℓ)
extensionLemma {P} decP n₀ F ¬Pn₀+1 ¬rest ℓ (n₀<ℓ , ℓ<n₀+1+1+F) 
    with ℓ Data.Nat.≟ n₀ + 1
... | yes ℓ≡n₀+1 = subst (λ y → ¬ P y) (sym ℓ≡n₀+1) ¬Pn₀+1
... | no  ℓ≢n₀+1 = 
    let n₀+1<ℓ : n₀ + 1 < ℓ
        n₀+1<ℓ = subst (λ y → y < ℓ) (sym $ +-suc n₀ 0) 
               $ subst (λ y → 2+ y ≤ ℓ) (sym $ +-identityʳ n₀)
               $ sucStillSmaller {n₀} {ℓ} n₀<ℓ 
               $ subst (λ y → y ≢ ℓ) 
                        (trans (+-suc n₀ 0) (+-identityʳ (ℕ.suc n₀)) ) 
                        (≢-sym ℓ≢n₀+1)
    in
    let ℓ<n₀+1+SucF : ℓ < n₀ + 1 + (1 + F)
        ℓ<n₀+1+SucF = subst (λ y → ℓ < y) (bracketRewr n₀ F) ℓ<n₀+1+1+F
    in
    ¬rest ℓ (n₀+1<ℓ , ℓ<n₀+1+SucF)

-- Forward search with limited fuel.
-- Search forward from a starting point n₀ until a positive instance is found, 
-- or until the endpoint n₀ + 1 + F has been reached. 
-- Positive instances at the startpoint P n₀ or endpoint P (n₀+1+F) 
-- are not considered, only instances strictly inbetween.
linearSearchForward 
    : {P : ℕ → Set}
    → (decP : Relation.Unary.Decidable P)
    → (n₀ F : ℕ)
    → (Σ[ h ∈ ℕ ](h < F × IsLeastNext P n₀ h))
        -- ^ A positive instance is found, all earlier instances are negative.
        ⊎
        ((ℓ : ℕ) → Between n₀ (n₀ + (1 + F)) ℓ → ¬ P ℓ)
        -- ^ None of the instances in the given range satisfy P.
linearSearchForward {P} decP n₀ ℕ.zero = inj₂ f
    where
        f : (ℓ : ℕ) → Between n₀ (n₀ + 1) ℓ → ¬ P ℓ
        f ℓ n₀<ℓ<n₀+1 = ⊥-elim $ emptyIval n₀ ℓ n₀<ℓ<n₀+1
-- There are two possible ways to prove the (ℕ.suc F) case:
-- 1. First decide if `P (n₀ + 1)`, if not use recursion
--      with fuel F to check the candidates {n₀ + 1 + 1 , ..., n₀ + 1 + F}.
-- 2. Use fuel F to check the candidates {n₀ + 1 , ..., n₀ + F},
--      and if they all fail decide `n₀ + 1 + F`.
-- Both ways seem more or less the same work to implement,
-- and seem to perform almost the same actual computation.
-- The implementation below uses option 1:
linearSearchForward {P} decP n₀ (ℕ.suc F) with (decP (n₀ + 1))
... | yes Pn₀+1 = inj₁ ( 0 , s≤s z≤n , Pn₀+1 , f)
    where
        f : (ℓ : ℕ) → Σ (ℕ.suc n₀ ≤ ℓ) (λ x → ℕ.suc ℓ ≤ n₀ + 1) → P ℓ → ⊥
        f ℓ n₀<ℓ<n₀+1 = ⊥-elim $ emptyIval n₀ ℓ n₀<ℓ<n₀+1
... | no ¬Pn₀+1 with linearSearchForward decP (n₀ + 1) F
...     | inj₁ (h , h<F , x) = 
    let h<SucF : h < ℕ.suc F
        h<SucF = Data.Nat.Properties.<-trans h<F (n<1+n F)
    in
    inj₁ (ℕ.suc h , s≤s h<F 
            , subst P (sym $ bracketRewr n₀ h) (proj₁ x)
            , extensionLemma decP n₀ h ¬Pn₀+1 (proj₂ x))
...     | inj₂ x = inj₂ $ extensionLemma decP n₀ F ¬Pn₀+1 x
            

boundedSearchForward
    : {P : ℕ → Set}
    → (decP : Relation.Unary.Decidable P)
    → (n₀ : ℕ)
    → Σ[ h ∈ ℕ ] P (n₀ + (1 + h))
    → LeastNext P n₀
boundedSearchForward {P} decP n₀ UB with linearSearchForward decP n₀ (proj₁ UB)
... | inj₁ x = (h , Pn₀+1+h , isLeastH)
    where
        h = proj₁ x
        Pn₀+1+h = proj₁ $ proj₂ $ proj₂ x
        isLeastH = proj₂ $ proj₂ $ proj₂ x
... | inj₂ x = (proj₁ UB , proj₂ UB , x )

-- #TODO: maybe move this definition to somewhere else
PiecewiseFin : (P : ℕ → Set) → Set
PiecewiseFin P = ((w : ℕ) → Σ[ z ∈ ℕ ]( P w ≃ Fin z ))

PiecewiseFinToDec
    : ( P : ℕ → Set)
    → PiecewiseFin P
    → Relation.Unary.Decidable P
PiecewiseFinToDec P PWFin w with (PWFin w)
... | (0 , Pw≃Fin0) = no (≃-⊥-to-¬ (≃-trans Pw≃Fin0 fin0))
... | (suc z , Pw≃FinSucz) = yes (Inverse.from Pw≃FinSucz Fin.zero)

--------------------------------------------------------------------------------
-- Skip-over-⊥s theorem
-- A sum over a family of types is equivalent to the sum
-- over the same types except with the empty ones left out.
--
-- One could prove a more general statement than presented here,
-- but this version is most convenient for our use case.
--------------------------------------------------------------------------------

-- A function that jumps from one to the next inhabited type
-- given an ℕ-indexed family of types.
InhabitJumper : (C : ℕ → Set)  → Set
InhabitJumper C 
    = {w : ℕ} 
    → C w
    → Σ[ h ∈ ℕ ] (
       --^ Jumping distance (minus one).
       (C $ w + (1 + h)) 
       --^ The destination is inhabited, ...
       × 
       ((x : ℕ) → (w < x × x < w + (1 + h)) → ¬ C x) 
       --^ ... but intermediate points are not.
    )
-- Note: the argument `C w` might seem redundant.
-- For my use case it could indeed be avoided,
-- but the implementation of an actual jumper simplifies a lot if we can
-- depart from the latest inhabited point.
-- The alternative is to take multiple jumps from the first inhabited points,
-- until one reaches the first point beyond w; this is more work to prove right
-- in Agda.

-- Iterate an InhabitJumper from an inhabited starting point n₀,
-- and give the point reached after n jumps.
-- (In out use case (see below), we'll have ¬ C 0 but C 1 is inhabited, 
-- so we start with n₀ ≔ 1).
J-iter : {C : ℕ → Set} → (n₀ : ℕ) → C n₀ → (J : InhabitJumper C) → ℕ → ℕ
J-iter {C} n₀ t₀ J i = proj₁ $ iter J' i (n₀ , t₀)
    module IterableJumper where
        J' : Σ[ w ∈ ℕ ] C w → Σ[ w ∈ ℕ ] C w
        J' (w , t) = 
            let (h , t' , _) = J {w} t
            in
            (w + (1 + h) , t')

-- Same as J-iter, but return the inhabitant at the endpoint instead
-- of the index of the endpoint.
J-iter-endpoint 
    : {C : ℕ → Set} 
    → (n₀ : ℕ) 
    → (t₀ : C n₀)
    → (J : InhabitJumper C) 
    → (i : ℕ)
    → C (J-iter n₀ t₀ J i)
J-iter-endpoint {C} n₀ t₀ J i = proj₂ $ iter J' i (n₀ , t₀)
    where open IterableJumper {C} n₀ t₀ J i

J-iter-ival-empty 
    : {C : ℕ → Set} 
    → (n₀ : ℕ) 
    → (t₀ : C n₀)
    → (J : InhabitJumper C) 
    → (i : ℕ) 
    → ((ℓ : ℕ) 
        → (Between (J-iter {C} n₀ t₀ J i) (J-iter {C} n₀ t₀ J (ℕ.suc i)) ℓ)
        → ¬ C ℓ
      )
J-iter-ival-empty {C} n₀ t₀ J 0 = proj₂ $ proj₂ $ J {n₀} t₀
J-iter-ival-empty {C} n₀ t₀ J i@(ℕ.suc i') = 
    proj₂ $ proj₂ $ J (proj₂ $ iter J' i (n₀ , t₀))
    where open IterableJumper {C} n₀ t₀ J i

jumpOver⊥s
    : (C : ℕ → Set)
    → (J : InhabitJumper C)
    → (¬ C 0)
    → (t₀ : C 1)
    → (Σ[ w ∈ ℕ ] C w) ≃ (Σ[ i ∈ ℕ ] (C $ J-iter 1 t₀ J i))
jumpOver⊥s C J ¬C0 t₀ = mk≃' f f⁻¹ invˡ invʳ
    where
    j : ℕ → ℕ
    j = J-iter 1 t₀ J

    piecewiseIncrLemma : (i : ℕ) → j i < j (ℕ.suc i) 
    -- The proof for i≡0 uses the following definitional equalities:
    -- j 0 ≗ 1
    -- j 1 ≗ proj₁ $ (1 + (1 + h))
    --  where
    --      (h , _ , _) ≗ J {1} t₀
    piecewiseIncrLemma 0 = m<m+1+n 1 h
        where
            h = proj₁ $ J {1} t₀
    piecewiseIncrLemma (i@(suc i')) = m<m+1+n (j i) h
        where
            -- We import J' from the def of J-iter;
            -- this is the iterable version of J.
            open IterableJumper 1 t₀ J i using (J')
            h  = proj₁ $ J (proj₂ $ iter J' i (1 , t₀))
            tₕ = proj₁ $ proj₂ $ J (proj₂ $ iter J' i (1 , t₀))
            
            -- The above use of m<m+1+n works because `j (suc i)` is equal to
            -- the following two exporessions, and the proj₁ of the RHS
            -- is of the desired form m+(1+n).
            -- Note that m  ≔ j i is the base weight of the (wᵢ , tᵢ)
            -- starting point of the last jump. j i outputs wᵢ,
            -- j (ℕ.suc i) outputs w₁ + (1 + h).
            H : iter J' (ℕ.suc i) (1 , t₀) 
                ≡ 
                (proj₁ (iter J' i (1 , t₀)) + (1 + h) , tₕ)
            H = refl


    monotoneLemma : ℕ<Monotone j
    monotoneLemma = piecewiseIncrImplMono {j} piecewiseIncrLemma

    -- For all w s.t. C w is inhabited, there exists an i ∈ ℕ s.t. w ≡ j i.
    existenceLemma
        : (w : ℕ)
        → C w
        → Σ[ i ∈ ℕ ] w ≡ j i
    existenceLemma w t = (i , w≡ji)
        where
            -- Note that j 0 ≡ 1, and that ¬C0 implies that 1 ≤ w.
            -- So in particular, j 0 ≤ w must always hold. 
            j0≤w : j 0 ≤ w
            j0≤w = 
                let H : j 0 ≤ w ⊎ w < j 0
                    H = Data.Nat.Properties.≤-<-connex (j 0) w
                in
                let K : ¬ w < j 0
                    K w<j0 = 
                        let w≡0 = n<1⇒n≡0 w<j0
                        in
                        ¬C0 (subst C w≡0 t)
                in
                elimCaseRight H K

            ivalLemmaOutp : Σ[ i ∈ ℕ ]( j i ≤ w × w < j (ℕ.suc i))
            ivalLemmaOutp = ℕ<MonoImplIval j monotoneLemma w j0≤w
            i : ℕ
            i = proj₁ ivalLemmaOutp
            ji≤w : j i ≤ w
            ji≤w = proj₁ $ proj₂ ivalLemmaOutp
            w<jSucI : w < j (ℕ.suc i)
            w<jSucI = proj₂ $ proj₂ ivalLemmaOutp

            ¬rest : (ℓ : ℕ) → Between (j i) (j (ℕ.suc i)) ℓ → ¬ C ℓ
            ¬rest = J-iter-ival-empty {C} 1 t₀ J i

            w≡ji : w ≡ j i
            w≡ji = firstOfIval {w} {j i} {j (ℕ.suc i)} ji≤w w<jSucI C ¬rest t

    -- This shows that j is injective, which stengthens the above
    -- existenceLemma to 'there exists a *unique* i s.t. w ≡ j i.
    injectivityLemma : ℕInjective j
    injectivityLemma = monotoneImplInjective {j} monotoneLemma

    -- If t : C (j i) then the existenceLemma outputs the same i again.
    -- This is because j is monotone and hence injective!
    existenceRetractsJ
        : (i : ℕ)
        → (t : C (j i))
        → (proj₁ $ existenceLemma (j i) t) ≡ i
    existenceRetractsJ i t = 
        let i' : ℕ
            i' = proj₁ $ existenceLemma (j i) t
        in
        injectivityLemma (sym $ proj₂ $ existenceLemma (j i) t)

    f : Σ[ w ∈ ℕ ] C w → Σ[ i ∈ ℕ ] (C $ j i)
    f (w , t) = 
        let (i , w≡ji) = existenceLemma w t
        in
        (i , subst C w≡ji t)
    f⁻¹ : Σ[ i ∈ ℕ ] (C $ j i) → Σ[ w ∈ ℕ ] C w
    f⁻¹ (i , t) = (j i , t)
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {(i , t)} {w , t} refl = 
        let (i' , ji≡ji') = existenceLemma (j i) t
        in
        ≡begin 
            f (j i , t)
        ≡⟨⟩
            (i' , subst C ji≡ji' t)
        ≡⟨ tuple-with-subst {ℕ} {ℕ} {C} j i i' t (existenceRetractsJ i t) ji≡ji' ⟩
            (i , t)
        ≡∎
    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {w , t} {i , t'} refl =
        let (i' , w≡ji') = existenceLemma w t
        in
        ≡begin 
            f⁻¹ (i' , subst C w≡ji' t)
        ≡⟨⟩
            (j i' ,  subst C w≡ji' t)
        ≡⟨ tuple-with-subst {ℕ} {ℕ} {C} id w (j i') t (sym w≡ji') w≡ji' ⟩
            (w , t)
        ≡∎

jumpTheoremInhabitJumper
    : {C : ℕ → Set}
    -- ^ Type of 'pitstops' the jumping function can visit.
    → (t₀ : C 1)
    -- ^ Proof the starting pitstop with index 1 is inhabited.
    → (J : InhabitJumper C)
    -- ^ Function to jump between pitstops.
    → ((w : ℕ) → Σ[ z ∈ ℕ ]( C w ≃ Fin z ))
    -- ^ Every point (incl. non-pitstops) is some finite set.
    → ((i : ℕ) → Σ[ z' ∈ ℕ ] (C (J-iter {C} 1 t₀ J i) ≃ Fin (ℕ.suc z')))
    -- ^ But when only looking at pitstops, they are inhabited finite sets.
jumpTheoremInhabitJumper {C} t₀ J pitstops i = (z' , Hz')
    where
        j = J-iter {C} 1 t₀ J
        j' = J-iter-endpoint {C} 1 t₀ J
        z  = proj₁ $ pitstops $ j i
        Cw≃FinZ = proj₂ $ pitstops $ j i
        
        w : ℕ
        w = j i

        z≡0⊎z≡Sz' : (z ≡ 0) ⊎ (Σ[ z' ∈ ℕ ] z ≡ ℕ.suc z')
        z≡0⊎z≡Sz' = nullOrSuc z

        -- The case z≡0 cannot happen, because all pitstops are inhabited,
        -- so we have a term tᵢ ≔ j' i : C w which
        -- contradicts C w ≃ Fin 0 ≃ ⊥.
        z≢0 : z ≢ 0
        z≢0 z≡0 = 
            let Cw≃Fin0 : C w ≃ Fin 0
                Cw≃Fin0 = subst (λ x → C w ≃ Fin x) z≡0 Cw≃FinZ
            in
            let Cw≃⊥ = C w ≃ ⊥
                Cw≃⊥ = ≃-trans Cw≃Fin0 fin0
            in
            Inverse.to Cw≃⊥ (j' i)

        z≡Sz' : Σ[ z' ∈ ℕ ] z ≡ ℕ.suc z'
        z≡Sz' = elimCaseLeft z≡0⊎z≡Sz' z≢0
        
        z' : ℕ
        z' = proj₁ z≡Sz'

        Hz' : C w ≃ Fin (ℕ.suc z')
        Hz' = subst (λ x → C w ≃ Fin x) (proj₂ z≡Sz') Cw≃FinZ

--------------------------------------------------------------------------------
-- Every signature with at least one nullary constructor and at least
-- one multiary constructor has infinitely many terms,
-- and there are infinitely many weights such that it has a term of that weight.
-- We can always build an InhabitJumper visiting exactly those weights
-- (actually, there are probably many ways to do so, but showing some
-- InhabitJumper exists is enough!)
--
-- Note: "at least one nullary and at least one multiary constructor"
-- is the same as "μ ≥ 1 and ζ ≥ 1".
-- Strictly speaking,
-- building an InhabitJumper does not require any nullary constructor,
-- But this is always required when applying it in the jumpOver⊥s
-- or in the jumpTheoremInhabitJumper (to create the argument t₀) anyway.
-- So we do require it, 
-- since having a nullary constructor makes the implementation easier.
--
-- Strategy: let c be the given multiary constructor and a₀ be the given nullary
-- constructor.
-- Then c(a₀, a₀, a₀, ... , a₀, -) : {w} → C w → C (w + (1 + h))
-- (c with a₀ applied one time fewer than its arity)
-- gives a family of terms that has a member greater than any inhabited weight.
-- (h is the index of c plus (arity(c) - 1)*(weight of a₀) = (arity(c) - 1)
-- since a₀ weights 1.
--------------------------------------------------------------------------------

module _ {μ ζ : ℕ∞} (S : Signature (suc∞ μ) (suc∞ ζ) ) where

    C = ClosedTerms {suc∞ μ} {suc∞ ζ} S
    OT = OpenTerms {suc∞ μ} {suc∞ ζ} S

    -- Given an OpenTerm with (suc n) open argument-holes and an argument a₀,
    -- apply a₀ n times to it, yielding an OpenTerm with 1 open hole.
    applyArgTillAlmostFull
        : {n : ℕ}
        → {wₜ wₐ : ℕ}
        → (t : OT wₜ (ℕ.suc n))
        → (a : C wₐ)
        → OT (n * wₐ + wₜ) 1
    applyArgTillAlmostFull {0} t a = t
    applyArgTillAlmostFull {ℕ.suc n} {wₜ} {wₐ} t a = 
        let H : n * wₐ + (wₐ + wₜ) ≡ (ℕ.suc n) * wₐ + wₜ
            H = n*a+[a+b]≡Sn*a+b n wₐ wₜ
        in
        subst (λ w → OT w 1) H (applyArgTillAlmostFull (giveArg t a) a)
    
    -- Default upper-bound for the length of the linear-search-forward
    -- from an inhabited C w till a C (w + 1 + h) that is inhabited again.
    -- Idea: fill the first multiary constructor with the first nullary
    -- until it has one argument-hole remaining, giving an (t : OpenTerm 1+h 1)
    -- with weight 1+h ≥ 1.
    -- Appling the proof (a : C w) as an argument to t
    -- results in a term `giveArg t a : C (w + (1 + h))`.
    module UpperBound where
            -- Term corresponding to the first nullary term, has weight 1.
            a₀ : C 1 
            a₀ = subst (λ w → C w) (sucZeroIsOneInℕ μ) (mk-nullary (cardToZero μ))

            -- Arity of the first multiary constructor.
            c₀-ar : ℕ
            c₀-ar = (arity {suc∞ μ} {suc∞ ζ} {S} (cardToZero ζ))
            c₀-ar∸1 : ℕ
            c₀-ar∸1 = S (cardToZero ζ)

            -- First multiary constructor without arguments applied.
            c₀ : OT 1 c₀-ar
            c₀ = subst (λ w → OT w c₀-ar ) (sucZeroIsOneInℕ ζ) (mk-multiary (cardToZero ζ))

            -- Apply a₀ as often as possible to c₀ until one open argument-hole
            -- remains. The weight is 1 + (c₀-ar  ∸ ) * 1 ≡ c₀-ar.
            c₀-onemore : OT c₀-ar 1
            c₀-onemore = subst (λ w → OT w 1) eq c₀'
                where
                    c₀' : OT (S (cardToZero ζ) * 1 + 1) 1
                    c₀' = applyArgTillAlmostFull {c₀-ar∸1} {1} c₀ a₀
                    eq : c₀-ar∸1 * 1 + 1 ≡ c₀-ar
                    eq = ≡begin 
                            c₀-ar∸1 * 1 + 1 
                        ≡⟨  cong (λ x → x + 1) (*-identityʳ $ c₀-ar∸1)⟩
                            c₀-ar∸1 + 1
                        ≡⟨ +-comm c₀-ar∸1 1 ⟩
                            1 + c₀-ar∸1
                        ≡⟨⟩
                            c₀-ar
                        ≡∎
                    
            
            hMax : ℕ
            hMax = c₀-ar∸1

            app-to-c₀ : {w : ℕ} → (a : C w) → C (w + (1 + hMax))
            app-to-c₀ {w} a = giveArg c₀-onemore a

            upperBoundTerm : {w : ℕ} → C w → C (w + (1 + hMax))
            upperBoundTerm t = app-to-c₀ t

            upperBoundWeight : {w : ℕ} → C w → ℕ
            upperBoundWeight {w} t = (w + (1 + hMax))

        

    mkInhabitJumper 
        : (PiecewiseFin C) 
        -- ^ For every weight w, we know C w ≃ Fin (z w) for some z : ℕ → ℕ.
        → InhabitJumper (ClosedTerms {suc∞ μ} {suc∞ ζ} S)
    mkInhabitJumper PWFin {w} t = (h , Cw+1+h , intermEmpty)
        where
            open UpperBound

            upperBound : Σ[ h' ∈ ℕ ](C (w + (1 + h')))
            upperBound = (hMax , upperBoundTerm t)

            decC : Relation.Unary.Decidable C
            decC = PiecewiseFinToDec C PWFin

            searchOutp : LeastNext C w
            searchOutp = boundedSearchForward {C} decC w upperBound

            h : ℕ
            h = proj₁ searchOutp

            Cw+1+h : C (w + (1 + h))
            Cw+1+h = proj₁ $ proj₂ searchOutp

            intermEmpty : ((x : ℕ) → (w < x × x < w + (1 + h)) → ¬ C x) 
            intermEmpty = proj₂ $ proj₂ searchOutp
