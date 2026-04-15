-- Module      : Eser.Equivalences.Properties
-- Description : General theorems about commonly used equivalences
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

open import Level
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties 
    renaming (setoid to mk-≡-setoid)
open import Relation.Nullary
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)
open import Data.Fin.Properties 

open import Function.Related.TypeIsomorphisms
open import Function
open import Function.Properties.Inverse hiding (refl ; trans ; sym)
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Data.Product.Function.NonDependent.Propositional using (_×-↔_)

open import Eser.Aux
open import Eser.Dec
open import Eser.Equivalences.Notation
open import Eser.Stdlib using (fin-≡-irrelevant)
open import Eser.Fin using (finMaxOrSmaller)

module Eser.Equivalences.Properties where

--------------------------------------------------------------------------------
-- Basic equivalence properties and convenient constructor.
--------------------------------------------------------------------------------

≃-refl : {A : Set} → (A ≃ A)
≃-refl = ↔-refl

≃-sym : {A B : Set} → (A ≃ B) → (B ≃ A)
≃-sym = ↔-sym

≃-trans : {A B C : Set} → (A ≃ B) → (B ≃ C) → (A ≃ C)
≃-trans = ↔-trans

mk≃ = mk↔

mk≃' 
    : {A B : Set}
    → (to : A → B)
    → (from : B → A)
    → (invl : Inverseˡ _≡_ _≡_ to from)
    → (invr : Inverseʳ _≡_ _≡_ to from)
    → A ≃ B
mk≃' {A} {B} to from invl invr = mk↔ (invl , invr)

module _ where
    open Inverse using (to ; from ; inverse)
    open import Eser.Definitions using (_≈_)
    open import Function.Consequences.Propositional
        
    FromToHomot
        : {A B : Set}
        → (H : A ≃ B)
        → ((from H) ∘ (to H)) ≈ (id {A = A})
    FromToHomot {A} {B} H = inverseʳ⇒strictlyInverseʳ $ proj₂ $ inverse H

    ToFromHomot
        : {A B : Set}
        → (H : A ≃ B)
        → ((to H) ∘ (from H)) ≈ (id {A = B})
    ToFromHomot {A} {B} H = inverseˡ⇒strictlyInverseˡ $ proj₁ $ inverse H
--------------------------------------------------------------------------------
-- Very basic ≃-rewriting theorems
--------------------------------------------------------------------------------

-- If a ≡ a' then B a ≃ B a'.
≃-subst
    : {A : Set}
    → {B : A → Set}
    → {a a' : A}
    → a ≡ a'
    → B a ≃ B a'
≃-subst {A} {B} {a} a≡a' = subst (λ x → B a ≃ B x) a≡a' (≃-refl {B a})

≡-to-≃ 
    : { A A' : Set}
    → A ≡ A'
    → A ≃ A'
≡-to-≃ refl = ≃-refl

≃-× : {A A' B B' : Set}
    → A ≃ A'
    → B ≃ B'
    → (A × B) ≃ (A' × B')
≃-× = _×-↔_

--------------------------------------------------------------------------------
-- Empty sets
--------------------------------------------------------------------------------

≃-⊥-to-¬
    : {A : Set}
    → A ≃ ⊥
    → ¬ A
≃-⊥-to-¬ {A} A≃⊥ = Inverse.to A≃⊥

--------------------------------------------------------------------------------
-- Rewriting dependent sums Σ
--------------------------------------------------------------------------------

module _ where
    open import Data.Product.Function.Dependent.Propositional using (Σ-↔)

    -- If Ba ≃ Ca for all a ∈ A then Σ[a∈A]Ba ≃ Σ[a∈A]Ca.
    rewr-≃-rightOf-Σ
        : {A : Set}
        → {B C : A → Set}
        → ((a : A) → (B a ≃ C a))
        → (Σ[ a ∈ A ] B a) ≃ (Σ[ a ∈ A ] C a)
    rewr-≃-rightOf-Σ {A} {B} {C} H = Σ-↔ (≃-refl) H' 
        where
            H' : {a : A} → (B a ≃ C a)
            H' {a} = H a

    -- If f : A ≃ A' then Σ[a∈A]Ba ≃ Σ[a'∈A']B(f(a)).
    -- Note that we have to precompose B with f to make it type-check.
    rewr-≃-indexOf-Σ-dep
        : {A A' : Set}
        → {B : A → Set}
        → (A≃A' : A ≃ A')
        → (Σ[ a ∈ A ] B a) ≃ (Σ[ a' ∈ A' ] B (Inverse.from A≃A' a'))
    rewr-≃-indexOf-Σ-dep {A} {A'} {B} A≃A' = Σ-↔ A≃A' H
        where
            f : A → A'
            f = Inverse.to A≃A'
            g : A' → A
            g = Inverse.from A≃A'
            H : {a : A} → B a ≃ (B $ g $ f a)
            H {a} = 
                let Ba≃Ba : B a ≃ B a
                    Ba≃Ba = ≃-refl
                in
                subst (λ x → B a ≃ B x) (sym $ FromToHomot A≃A' a) Ba≃Ba

    -- Special case of above:
    -- If A ≃ A' and B does NOT depend on A then Σ[a∈A]B ≃ Σ[a'∈A']B
    rewr-≃-indexOf-Σ-indep
        : {A A' B : Set}
        → A ≃ A'
        → (Σ[ a ∈ A ] B) ≃ (Σ[ a' ∈ A' ] B)
    rewr-≃-indexOf-Σ-indep {A} {A'} {B} = rewr-≃-indexOf-Σ-dep {A} {A'} {λ a → B}

--------------------------------------------------------------------------------
-- Rewriting binary sums _⊎_
--------------------------------------------------------------------------------

rewr-≃-under-⊎
    : {A A' B : Set}
    → A ≃ A'
    → (A ⊎ B) ≃ (A' ⊎ B)
rewr-≃-under-⊎ {A} {A'} {B} A≃A' = mk≃' f f⁻¹ invˡ invʳ
    where
        g : A → A'
        g = Inverse.to A≃A'
        g⁻¹ : A' → A
        g⁻¹ = Inverse.from A≃A'
        invˡg : Inverseˡ _≡_ _≡_ g g⁻¹
        invˡg = Inverse.inverseˡ A≃A'
        invʳg : Inverseʳ _≡_ _≡_ g g⁻¹
        invʳg = Inverse.inverseʳ A≃A'

        f : A ⊎ B → A' ⊎ B
        f = Data.Sum.map g id
        f⁻¹ : A' ⊎ B → A ⊎ B
        f⁻¹ = Data.Sum.map g⁻¹ id
        invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
        -- Use that map g h (map g⁻¹ h⁻¹ (inj₁ z)) = inj₁ (g (g⁻¹ (z)))
        -- and then use Inverse.invˡ A≃A'.
        invˡ {inj₁ a'} {y} refl = 
            ≡begin 
                (f $ f⁻¹ $ inj₁ a')
            ≡⟨⟩ -- Definition of Sum.map (functoriality of ⊎): take inj₁ out.
                (inj₁ $ g $ g⁻¹ a')
            ≡⟨ cong inj₁ (invˡg refl) ⟩
                inj₁ a'
            ≡∎
        -- Idem but now for h (which is id in our case)
        invˡ {inj₂ b} {y} refl = 
            ≡begin 
                (f $ f⁻¹ $ inj₂ b)
            ≡⟨⟩
                (inj₂ $ id $ id b)
            ≡⟨⟩
                inj₂ b
            ≡∎
            
        invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
        invʳ {inj₁ a} {y} refl = 
            ≡begin 
                (f⁻¹ $ f $ inj₁ a)
            ≡⟨⟩
                (inj₁ $ g⁻¹ $ g a)
            ≡⟨ cong inj₁ (invʳg refl) ⟩
                inj₁ a
            ≡∎
        invʳ {inj₂ b} {y} refl = 
            ≡begin 
                (f⁻¹ $ f $ inj₂ b)
            ≡⟨⟩
                (inj₂ $ id $ id b)
            ≡⟨⟩
                inj₂ b
            ≡∎

rewr-≃-under-⊎-right
    : {A B B' : Set}
    → B ≃ B'
    → (A ⊎ B) ≃ (A ⊎ B')
rewr-≃-under-⊎-right {A} {B} {B'} B≃B' =
    begin 
        (A ⊎ B)
    ≃⟨ ⊎-comm A B ⟩
        (B ⊎ A)
    ≃⟨ rewr-≃-under-⊎ {B} {B'} {A} B≃B' ⟩
        (B' ⊎ A)
    ≃⟨ ⊎-comm  B' A ⟩
        (A ⊎ B')
    ∎
    
rewr-≃-under-⊎-both
    : {A A' B B' : Set}
    → A ≃ A'
    → B ≃ B'
    → (A ⊎ B) ≃ (A' ⊎ B')
rewr-≃-under-⊎-both {A} {A'} {B} {B'} A≃A' B≃B' =
    begin 
        (A ⊎ B)
    ≃⟨ rewr-≃-under-⊎ A≃A' ⟩
        (A' ⊎ B)
    ≃⟨ rewr-≃-under-⊎-right B≃B' ⟩
        (A' ⊎ B')
    ∎
    
rewr-≃-under-⊎-3
    : {A A' B B' C C' : Set}
    → A ≃ A'
    → B ≃ B'
    → C ≃ C'
    → (A ⊎ B ⊎ C) ≃ (A' ⊎ B' ⊎ C')
rewr-≃-under-⊎-3 {A} {A'} {B} {B'} {C} {C'} A≃A' B≃B' C≃C' =
    let H : (B ⊎ C) ≃ (B' ⊎ C')
        H = rewr-≃-under-⊎-both B≃B' C≃C'
    in
        rewr-≃-under-⊎-both A≃A' H

--------------------------------------------------------------------------------
-- Rewriting expressions involving Fin
--------------------------------------------------------------------------------

fin0 : Fin 0 ≃ ⊥
fin0 = mk≃' f f⁻¹ invˡ invʳ
    where
    f : Fin 0 → ⊥
    f ()
    f⁻¹ : ⊥ → Fin 0
    f⁻¹ ()
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {()}
    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {()}

isContrFin1
    : isContr (Fin 1)
isContrFin1 = (Fin.zero , isCenter)
    where
        isCenter : (x : Fin 1) → (Fin.zero ≡ x)
        isCenter (Fin.zero) = refl

-- All contractible types are equivalent to Fin 1.
contr≃Fin1
    : {A : Set}
    → isContr A
    → A ≃ Fin 1
contr≃Fin1 {A} (a , isCenter) = mk≃' f f⁻¹ invˡ invʳ
    where
    f : A → Fin 1
    f a = Fin.zero
    f⁻¹ : Fin 1 → A
    f⁻¹ _ = a
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {Fin.zero} {a'} refl = (proj₂ isContrFin1) (f a')
    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {a'} {Fin.zero} refl = isCenter a'


Σfin0 : (B : Fin 0 → Set) → (Σ[ x ∈ Fin 0 ] B x) ≃ ⊥
Σfin0 B = mk≃' f f⁻¹ invˡ invʳ
    where
    f : Σ[ x ∈ Fin 0 ] B x → ⊥
    f ()
    f⁻¹ : ⊥ → Σ[ x ∈ Fin 0 ] B x
    f⁻¹ ()
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {()}
    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {()}

-- The stdlib's definition of surjectivity is a bit indirect
-- because it also allows other relations than _≡_.
-- The stdlib's definition of surjectivity says that:
--      (b : B) → surjectiveAt f b
surjectiveAt
    : {A B : Set}
    → (f : A → B)
    → (b : B)
    → Set
surjectiveAt {A} {B} f b = Σ[ a ∈ A ] ({a' : A} → a' ≡ a → f a' ≡ b)

-- If x is not the maximum element of a finite set,
-- then 1+x also exists in the same finite set.
finEndoSuc
    : {n : ℕ}
    → (x : Fin $ ℕ.suc n)
    → (x Data.Fin.< fromℕ n)
    → Σ[ x' ∈ (Fin $ ℕ.suc n) ](ℕ.suc (toℕ x) ≡ toℕ x')
finEndoSuc {n} x x<n = (x'' , p)
    where
        x' : ℕ
        x' = ℕ.suc $ toℕ x

        x'<Sn : x' Data.Nat.< ℕ.suc n
        x'<Sn = s≤s $ subst (λ z → toℕ x Data.Nat.< z) (toℕ-fromℕ n) x<n

        x'' : Fin $ ℕ.suc n
        x'' = fromℕ< x'<Sn

        p : ℕ.suc (toℕ x) ≡ toℕ x''
        p = ≡begin 
                ℕ.suc (toℕ x)
            ≡⟨⟩
                x'
            ≡⟨ sym $ toℕ-fromℕ< {x'} x'<Sn ⟩
                toℕ (fromℕ< x'<Sn)
            ≡⟨⟩
                toℕ x''
            ≡∎

-- A ℕ-indexed sum of nonempty finite sets is equivalent to ℕ.
Σfin-inf-inhabited
    : (g : ℕ → ℕ)
    → Σ[ i ∈ ℕ ](Fin $ ℕ.suc $ g i) ≃ ℕ
-- Proof: give a function and show it is injective and surjective.
Σfin-inf-inhabited g = ⤖⇒↔ $ mk⤖ (injF , surjF)
    where
        From = Σ[ i ∈ ℕ ](Fin $ ℕ.suc $ g i)
        open import Function.Properties.Bijection using (⤖⇒↔)
        open Σfin-inf-inhabited-arithmetic
        f' : Σ[ i ∈ ℕ ](Fin $ ℕ.suc $ g i) → ℕ
        -- Currying the input makes the termination checker see we make progress
        -- on the first argument. 
        -- When giving pairs (i , x) it would complain.
        f : (i : ℕ) → (Fin $ ℕ.suc $ g i) → ℕ
        f' (i , x) = f i x

        f 0 x = toℕ x
        f (suc i) x = (toℕ x) + 1 + f i  (fromℕ (g i))

        -- Every element in the ith finite set is ≤ than g i,
        -- which is the maximum element of that set.
        smallerThanGi
            : {i : ℕ}
            → (x : Fin $ ℕ.suc $ g i)
            → toℕ x Data.Nat.≤ g i
        smallerThanGi {i} x = s≤s⁻¹ $ toℕ<n x

        -- Any element of the (i+1)th set is mapped by f to a number
        -- greater than the last element of the 0th set.
        greaterThanG0
            : {i : ℕ}
            → (x : Fin $ ℕ.suc $ g $ ℕ.suc i)
            → (g 0) ℕ< (f (ℕ.suc i) x) 
        greaterThanG0 {0} x = m<n+1+TFm (g 0) (toℕ x)

        greaterThanG0 {suc i} x = 
            let H : g 0 ℕ< toℕ x + 1 + g 0 
                H = m<n+1+m (g 0) (toℕ x)
            in
            let H' : g 0 ℕ< f (ℕ.suc i) (fromℕ $ g $ ℕ.suc i)
                H' = greaterThanG0 {i} (fromℕ $ g $ ℕ.suc i)
            in
            ℕ<-trans H (n<k→m+n<m+k (toℕ x + 1) H')


        -- If i<i' then f assigns the last element of Fin (g (suc i))
        -- a greater number than g (suc i) + f' (i , fromℕ (g i)),
        incrLemma
            : {i i' : ℕ}
            → i ℕ< i'
            → g (ℕ.suc i) + f' (i , fromℕ (g i)) ℕ< f' (i' , fromℕ (g i'))
        -- Sublemma of incrLemma. Separating this allows to pattern match 
        -- i' as ℕ.suc j, and performing an inductive call on j
        -- without needing <-well-founded-recursion.
        -- incrLemma and this sublemma are mutually recursive.
        incrLemma-Si<i'-case
            : {i i' : ℕ}
            → i ℕ< i'
            → ℕ.suc i ℕ< i'
            → g (ℕ.suc i) + f' (i , fromℕ (g i)) ℕ< f' (i' , fromℕ (g i'))
        incrLemma {i} {i'} i<i' with (m≤n⇒m<n∨m≡n i<i')
        -- i<i' leaves two possible cases : suc i < i' or suc i ≡ i'.
        ... | inj₁ Si<i' = incrLemma-Si<i'-case i<i' Si<i'
        ... | inj₂ Si≡i' = 
            let H : (toℕ $ fromℕ $ g (ℕ.suc i)) + 1 + f' (i , fromℕ (g i)) 
                    ≡ 
                    f' (i' , fromℕ (g i'))
                H = cong (λ j → f' (j , fromℕ (g j))) Si≡i'
            in
            -- Remove the annoying toℕ-fromℕ =.
            let H' : g (ℕ.suc i) + 1 + f' (i , fromℕ (g i)) 
                    ≡ 
                    f' (i' , fromℕ (g i'))
                H' = subst (λ y → y + 1 + f' (i , fromℕ (g i)) 
                                  ≡ f' (i' , fromℕ (g i')))
                           (toℕ-fromℕ (g $ ℕ.suc i))
                           H
            in
            -- The .. + 1 + ... ensures the above is greater than
            let H'' : g (ℕ.suc i) + f' (i , fromℕ (g i))
                     ℕ<
                     g (ℕ.suc i) + 1 + f' (i , fromℕ (g i)) 
                H'' = n+m<n+1+m (f' (i , fromℕ (g i))) (g $ ℕ.suc i)
            in
            subst (λ y → g (ℕ.suc i) + f' (i , fromℕ (g i)) ℕ< y) H' H''

        incrLemma-Si<i'-case {i} {i'@(ℕ.suc j)} i<i' Si<i' = 
                ℕ<-trans H'''
                (subst (λ y → g (ℕ.suc j) + 1 + g (ℕ.suc i) + f' (i , fromℕ (g i))
                              ℕ<
                              y
                       ) H H')
                where
                    i<j : i ℕ< j
                    i<j = s≤s⁻¹ Si<i'

                    H : g (ℕ.suc j) + 1 + f' (j , fromℕ (g j)) 
                        ≡ 
                        f' (i' , fromℕ (g i'))
                    H = subst (λ y → y + 1 + f' (j , fromℕ (g j)) 
                              ≡ 
                              f'(i' , fromℕ (g i')))
                              (toℕ-fromℕ (g $ ℕ.suc j)) refl

                    H' : g (ℕ.suc j) + 1 + g (ℕ.suc i) + f' (i , fromℕ (g i))
                         ℕ<
                         g (ℕ.suc j) + 1 + f' (j , fromℕ (g j))
                    H' = subst 
                            (λ y → y ℕ< g (ℕ.suc j) + 1 + f' (j , fromℕ (g j)))
                            (sym $ +-assoc (g (ℕ.suc j) + 1) 
                                     (g (ℕ.suc i))
                                     (f' (i , fromℕ (g i)))
                            )
                        $ +-monoʳ-< (g (ℕ.suc j) + 1) $ incrLemma i<j

                    H''' : g (ℕ.suc i) + f' (i , fromℕ (g i))
                          ℕ<
                          g (ℕ.suc j) + 1 + g (ℕ.suc i) + f' (i , fromℕ (g i))
                    H''' = subst (λ y → g (ℕ.suc i) + f' (i , fromℕ (g i)) ℕ< y)
                                 (sym $ +-assoc (g ( ℕ.suc j) + 1) 
                                                (g $ ℕ.suc i) 
                                                (f' (i , fromℕ (g i)))
                                 )
                            $ m<n+1+m (g (ℕ.suc i) + f' (i , fromℕ (g i))) 
                                      (g (ℕ.suc j))

        -- For a fixed i, f is ≤-monotone in the elements of Fin $ ℕ.suc $ g i.
        -- We only need the special cases where we compare an element with the
        -- min or the max of the finite set.
        ≥minOfSet
            : {i : ℕ}
            → (x : Fin $ ℕ.suc $ g i)
            → f' (i , Fin.zero) ℕ≤ f' (i , x)
        ≥minOfSet = ?
        ≤maxOfSet
            : {i : ℕ}
            → (x : Fin $ ℕ.suc $ g i)
            → f' (i , x) ℕ≤ f' (i , fromℕ (g i))
        ≤maxOfSet = ?

        -- Injectivity proof for the case where both:
        -- * inputs are of the form (suc i , x) (suc i' , x')
        -- * i < i'
        injF-suci-ineq-case
            : {i i' : ℕ}
            → (x : Fin $ ℕ.suc $ g $ ℕ.suc i)
            → (x' : Fin $ ℕ.suc $ g $ ℕ.suc i')
            → i ℕ< i'
            → f' (ℕ.suc i , x) ≡ f' (ℕ.suc i' , x')
            → _≡_ {A = From} (ℕ.suc i , x) (ℕ.suc i' , x')
            --^ Agda got confused about the base type when giving just:
            --  (ℕ.suc i , x) ≡ (ℕ.suc i' , x')
        injF-suci-ineq-case {i} {i'} x x' i<i' outpEq = 
            let H : 1 + g (ℕ.suc i) + f' (i , fromℕ (g i)) 
                    ℕ< 
                    1 + 0 + f' (i' , fromℕ (g i'))
                H = s≤s $ incrLemma i<i'
            in
            -- Swap order of summands.
            let H' : g (ℕ.suc i) + 1 + f' (i , fromℕ (g i)) 
                    ℕ< 
                    0 + 1 + f' (i' , fromℕ (g i'))
                H' = ?
            in
            -- This is what H actually says, up to a toℕ∘fromℕ ≈ id conversion.
            -- This is the most extreme case where
            -- x ≗ g (ℕ.suc i) is maximal
            -- and 
            -- x' ≗ 0
            -- is minimal.
            let H'' : f' (ℕ.suc i , fromℕ (g $ ℕ.suc i)) 
                      ℕ< 
                      f' (ℕ.suc i' , Fin.zero)
                H'' = subst 
                    (λ y → (
                            y + 1 + f' (i , fromℕ (g i)) 
                            ℕ< 
                            0 + 1 + f' (i' , fromℕ (g i'))
                    )) 
                    (sym $ toℕ-fromℕ (g $ ℕ.suc i))
                    H'
            in
            let H''' : f' (ℕ.suc i , x)
                      ℕ< 
                      f' (ℕ.suc i' , x')
                H''' = ℕ≤-<-trans (s≤s $ ≤maxOfSet x) 
                                  (ℕ<-≤-trans H'' (≥minOfSet x'))
            in
            ⊥-elim $ n≮n (f' (ℕ.suc i , x))
                (subst (λ v → f' (ℕ.suc i , x) ℕ< v) (sym outpEq) H''')
        
        injF : Injective _≡_ _≡_ f'
        injF {0 , x}     {0 , x'}      H = 
            -- Use that f 0 x ≗ toℕ x, so H : toℕ x ≡ toℕ x'.
            let x≡x' : x ≡ x'
                x≡x' = toℕ-injective H
            in
            cong (λ x → (0 , x)) x≡x'
        injF {suc i , x} {0 , x'} eqOutp = ⊥-elim contra
            module MixCaseContradiction where 
                H : g 0 ℕ< f' (ℕ.suc i , x) 
                H = greaterThanG0 {i} x
                
                H' : toℕ x' ℕ≤ g 0 -- The LHS equals `f 0 x'`.
                H' = smallerThanGi x'
                
                H'' : f' (ℕ.suc i , x) ℕ≤ g 0
                H'' = subst (λ y → y ℕ≤ g 0) (sym eqOutp) H'
                
                H''' : g 0 ℕ< g 0
                H''' = ℕ<-≤-trans H H''
                contra : ⊥
                contra = n≮n (g 0) H'''
        injF {0 , x} {suc i' , x'} H = 
            -- Same as previous case after swapping the inputs.
            ⊥-elim $ MixCaseContradiction.contra i' x' x (sym H)
        injF {suc i , x} {suc i' , x'} H with Data.Nat.<-cmp i i'
            -- Three cases: i ≡ i' , i < i' or i' < i.
            -- The last two cases are symmetric, and both contradict H.
            -- The first case is easier, since +-injectivity using H
            -- gives toℕ x ≡ toℕ x'
        ... | tri≈ _ i≡i' _ = 
            let Si≡Si' = cong ℕ.suc i≡i'
            in
            let K = Tx+1+y≡Tx'+1+y→x≡x' 
                --{ℕ.suc $ g $ ℕ.suc i} 
                --{ℕ.suc $ g $ ℕ.suc i'} 
                    {i}
                    {i'}
                    (ℕ.suc ∘ g ∘ ℕ.suc)
                    x 
                    x' 
                    (f i (fromℕ $ g i))
                    (f i' (fromℕ $ g i'))
                    i≡i'
                    --(cong (ℕ.suc ∘ g ∘ ℕ.suc) i≡i')
                    (cong (λ i → f i (fromℕ $ g i)) i≡i')
                    H
            in
            cong (λ ((i , x)) → ℕ.suc i , x) K
        -- The next two cases are symmetric, so we prove them
        -- once as a lemma, and simply swap the inputs and apply sym to get the
        -- other case.
        ... | tri< i<i' _ _ = injF-suci-ineq-case x x' i<i' H
        ... | tri> _ _ i'<i = sym $ injF-suci-ineq-case x' x i'<i (sym H)

        surjF : Surjective _≡_ _≡_ f'
        surjF 0 = ((0 , Fin.zero) , lemma)
            where
                lemma : 
                    {y : Σ[ i ∈ ℕ ] (Fin $ ℕ.suc $ g i)}
                    → (y ≡ (0 , Fin.zero))
                    → f' y ≡ 0
                lemma {0 , Fin.zero} refl = refl
        surjF n@(suc n') =
            let ((i , x) , p) = surjF n' in
            let f'ix≡n' : f' (i , x) ≡ n'
                f'ix≡n' = p {i , x} refl
            in
            caseDistinction i x (finMaxOrSmaller {g i} x) f'ix≡n'
            where
                caseDistinction 
                    : (i : ℕ) 
                    → (x : Fin $ ℕ.suc $ g i)
                    → (x ≡ fromℕ (g i) ⊎ x Data.Fin.< fromℕ (g i))
                    → (f' (i , x) ≡ n')
                    → surjectiveAt f' n
                caseDistinction i x (inj₁ x≡max) f'ix≡n' 
                    = ((ℕ.suc i , Fin.zero) , q)
                    where
                        q   : {ix' : From} 
                            → ix' ≡ (ℕ.suc i , Fin.zero) 
                            → f' ix' ≡ n
                        q  refl = 
                            ≡begin 
                                f' (ℕ.suc i , Fin.zero)
                            ≡⟨⟩
                                1 + 0 + f i (fromℕ (g i))
                            ≡⟨⟩
                                1 + f i (fromℕ (g i))
                            ≡⟨ cong (λ y → 1 + f i y) (sym x≡max) ⟩ 
                                1 + f i x
                            ≡⟨⟩
                                ℕ.suc (f i x)
                            ≡⟨⟩
                                ℕ.suc (f' (i , x))
                            ≡⟨ cong ℕ.suc f'ix≡n' ⟩
                                ℕ.suc n'
                            ≡⟨⟩
                                n
                            ≡∎
                caseDistinction i x (inj₂ x<max) f'ix≡n' = ((i , 1+x) , q)
                    where
                        1+x : Fin $ ℕ.suc $ g i
                        1+x = proj₁ $ finEndoSuc x x<max

                        p : ℕ.suc (toℕ x ) ≡ toℕ 1+x
                        p = proj₂ $ finEndoSuc x x<max

                        q : { ix' : From} → ix' ≡ (i , 1+x) → f' ix' ≡ n
                        -- f is defined by a case distinction on i,
                        -- so we need to make the same case distinction in q.
                        q {(0 , x')} refl = 
                            ≡begin 
                                f' (0 , x')
                            ≡⟨⟩
                                toℕ x'
                            ≡⟨ proj₂-eq-fin-tuples x' 1+x refl ⟩
                                toℕ (1+x)
                            ≡⟨ sym p ⟩
                                ℕ.suc (toℕ x)  
                            ≡⟨ cong ℕ.suc f'ix≡n' ⟩
                                ℕ.suc n'
                            ≡⟨⟩
                                n    
                            ≡∎
                        q {suc i' , x'} refl = 
                            -- Note: i ≗ ℕ.suc i' in this context.
                            -- NOT i ≗ i'.
                            ≡begin 
                                f' (ℕ.suc i' , 1+x)
                            ≡⟨⟩ 
                                toℕ 1+x + 1 + (f i' (fromℕ (g i'))) 
                            ≡⟨ cong 
                                (λ y → y + 1 + (f i' (fromℕ (g i')))) 
                                (sym p) 
                            ⟩
                                ℕ.suc (toℕ x) + 1 + (f i' (fromℕ (g i'))) 
                            ≡⟨⟩
                                ℕ.suc ( f' (ℕ.suc i' , x))
                            ≡⟨ cong ℕ.suc f'ix≡n' ⟩
                                ℕ.suc n' 
                            ≡⟨⟩
                                n    
                            ≡∎

fin-+-assoc
    : (n m l : ℕ)
    → Fin (n + (m + l)) ≃ Fin (n + m + l)
fin-+-assoc n m l = 
    let H₁ : (n + (m + l)) ≡ n + m + l
        H₁ = sym (Data.Nat.Properties.+-assoc n m l)
    in
    let H₂ : Fin (n + (m + l)) ≡ Fin (n + m + l)
        H₂ = cong Fin H₁
    in
    ≡-to-≃ H₂

fin-⊎-+
    : (n m : ℕ)
    → ((Fin n) ⊎ (Fin m)) ≃ Fin (n + m)
fin-⊎-+ n m = ≃-sym (Data.Fin.Properties.+↔⊎ {n} {m})

fin-×-*
    : (n m : ℕ)
    → ((Fin n) × (Fin m)) ≃ Fin (n * m)
fin-×-* n m = ≃-sym (Data.Fin.Properties.*↔× {n} {m})

-- #TODO: Instead of fin-dec-irrel-witness use the tools of Eser.Dec 
-- in the proof of fin-Σ-takeout-first 
--      in the subproof of invˡ 
--          in the inj₁ case,
-- just as the inj₂ case does. That's simpler, doesn't depend on the
-- proof-irrelevance of `Dec (x ≡ y)`.

-- Given a witness x ≡ y, all decisions of x ≐ y must output true,
-- and by proof irrelevance, also with the same proof.
fin-dec-irrel-witness
    : {n : ℕ}
    → {x y : Fin n}
    → x ≡ y
    → Relation.Nullary.Irrelevant (Dec (x ≡ y))
fin-dec-irrel-witness {n} {x} {y} h (no p) (no q) = ⊥-elim (p h)
fin-dec-irrel-witness {n} {x} {y} h (no p) (yes q) = ⊥-elim (p q)
fin-dec-irrel-witness {n} {x} {y} h (yes p) (no q) = ⊥-elim (q p)
fin-dec-irrel-witness {n} {x} {y} h (yes p) (yes q) = cong yes (fin-≡-irrelevant p q)

-- The sum Σ[x ∈ Fin (a + 1)](Bx)
-- is the same as the ⊎-sum of the last element,
-- Ba, and the remaining sum Σ[x ∈ Fin a](Bx).
-- (Similarly how for sums numbers it holds that:
--  ∑_{i=1}^{n+1}f(i) ≡ f(n+1) + ∑_{i=1}^{n}f(i) )
fin-Σ-takeout-first
    : (a : ℕ)
    → (B : Fin (ℕ.suc a) → Set)
    → Σ[ x ∈ Fin (ℕ.suc a) ] B x ≃ B (fromℕ a) ⊎ Σ[ x ∈ Fin a ] B (inject₁ x)
fin-Σ-takeout-first a B = mk≃' f f⁻¹ invˡ invʳ
    where
    -- The left-to-right direction f needs to make a case distinction.
    -- Using a `with` clause is quite confusing when writing the inversity
    -- proof, so instead of a with clause I use an auxiliary function.
    f'  : Σ[ x ∈ Fin (ℕ.suc a) ] ((B x) × (Dec $ x ≡ fromℕ a))
        → (B (fromℕ a) ⊎ Σ[ x ∈ Fin a ](B $ inject₁ x))
    f' (x , b , no p) = 
        let p' : a ≢ toℕ x
            p' H = p $ sym $ toℕ-injective $ trans (toℕ-fromℕ a) H
        in
        inj₂ (lower₁ x p' , subst B (sym $ inject₁-lower₁ x p') b)
    f' (x , b , yes p) = inj₁ (subst B p b)

    f   : Σ[ x ∈ Fin (ℕ.suc a) ] B x 
        → (B (fromℕ a) ⊎ Σ[ x ∈ Fin a ](B $ inject₁ x))
    f (x , b) = f' (x , b , (x Data.Fin.≟ fromℕ a))

    f⁻¹ : (B (fromℕ a) ⊎ Σ[ x ∈ Fin a ](B $ inject₁ x)) → Σ[ x ∈ Fin (ℕ.suc a) ] B x
    f⁻¹ (inj₁ b) = (fromℕ a , b)
    f⁻¹ (inj₂ (x , b)) = (inject₁ x , b)

    invˡ-inj₁-aux : Σ[ p ∈(fromℕ a ≡ fromℕ a) ]((fromℕ a Data.Fin.≟ fromℕ a) ≡ (yes p))
    invˡ-inj₁-aux = (refl , fin-dec-irrel-witness refl (fromℕ a Data.Fin.≟ fromℕ a) (yes refl)) 

    invˡ-inj₁-case
        : (b : B (fromℕ a))
        → (p : fromℕ a ≡ fromℕ a)
        → ((fromℕ a Data.Fin.≟ fromℕ a) ≡ (yes p))
        → f (fromℕ a , b) ≡ inj₁ b
    invˡ-inj₁-case b p H =
            -- p is an equality between finite numbers; but Fin (suc a)
            -- is an hSet so equalities are proof-irrelevant
            -- and hence p can be contracted to refl.
            let pIsRefl : p ≡ refl
                pIsRefl = fin-≡-irrelevant p refl
            in
            ≡begin 
                (f $ (fromℕ a ,  b))
            ≡⟨⟩
                f' (fromℕ a , b , (fromℕ a Data.Fin.≟ fromℕ a))
            ≡⟨ cong (λ p → f' (fromℕ a , b , p)) H ⟩ 
                f' (fromℕ a , b , yes p)
            ≡⟨⟩ 
                inj₁ (subst B p b)
            ≡⟨ cong (λ p → inj₁ (subst B p b)) pIsRefl ⟩ 
                inj₁ (subst B refl b)
            ≡⟨⟩ 
                inj₁ b
            ≡∎

    invˡ-inj₂-case
        : (x : Fin a)
        → (b : B (inject₁ x))
        → (¬p : inject₁ x ≢ fromℕ a)
        → ((inject₁ x Data.Fin.≟ fromℕ a) ≡ (no ¬p))
        → f (inject₁ x , b) ≡ inj₂ (x , b)
    invˡ-inj₂-case x b ¬p H =
            let p' : a ≢ toℕ (inject₁ x)
                p' z = ¬p $ sym $ toℕ-injective $ trans (toℕ-fromℕ a) z
            in
            let k : lower₁ (inject₁ x) p' ≡ x
                k = lower₁-inject₁ x
            in
            let R : inject₁ x ≡ (inject₁ $ lower₁ (inject₁ x) p')
                -- We could have defined `R = cong inject₁ (sym k)`,
                -- but that would not be the same proof as f' uses!
                R = sym (inject₁-lower₁ (inject₁ x) p') 
            in
            ≡begin 
                (f $ (inject₁ x ,  b))
            ≡⟨⟩
                f' (inject₁ x , b , (inject₁ x Data.Fin.≟ fromℕ a))
            ≡⟨ cong (λ p → f' (inject₁ x , b , p)) H ⟩ 
                f' (inject₁ x , b , no ¬p)
            ≡⟨⟩ 
                inj₂ (lower₁ (inject₁ x) p' , subst B (sym $ inject₁-lower₁ (inject₁ x) p') b)
            ≡⟨ cong inj₂ $ 
                tuple-with-subst {Fin a} {Fin $ ℕ.suc a} {B = B} 
                                 inject₁ x (lower₁ (inject₁ x) p') b k R
             ⟩
                inj₂ (x , b)
            ≡∎

    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {inj₁ b} {a' , b} refl = 
        let (p , H) = invˡ-inj₁-aux 
        in invˡ-inj₁-case b p H

    invˡ {inj₂ (x , b)} {a' , b} refl =
        let ¬p' : (inject₁ x ≢ fromℕ a)
            ¬p' = ≢-sym (fromℕ≢inject₁ {n = a} {i = x})
        in
        let (¬p , H) = dec-no-case (inject₁ x) (λ y → (y Data.Fin.≟ fromℕ a)) ¬p'
        in
        invˡ-inj₂-case x b ¬p H


    invʳ-sub-inj₁-case
        : (x : Fin $ ℕ.suc a)
        → (b : B x)
        → (p : x ≡ fromℕ a)
        → (H : (x Data.Fin.≟ fromℕ a) ≡ yes p)
        → (f⁻¹ $ f (x , b)) ≡ (x , b)
    invʳ-sub-inj₁-case x b refl H =
            ≡begin 
                (f⁻¹ $ f (fromℕ a , b))
            -- Some good luck: we can recycle a sublemma of invˡ:
            ≡⟨ cong f⁻¹ (invˡ-inj₁-case b refl H) ⟩ 
                f⁻¹ (inj₁ b)
            ≡⟨⟩
                (fromℕ a , b)
            ≡∎

    invʳ-sub-inj₂-case-inject₁
        : (x : Fin a)
        → (b : B (inject₁ x))
        → (¬p : (inject₁ x) ≢ fromℕ a)
        → (H : ((inject₁ x) Data.Fin.≟ fromℕ a) ≡ no ¬p)
        → (f⁻¹ $ f ((inject₁ x) , b)) ≡ (inject₁ x , b)
    invʳ-sub-inj₂-case-inject₁ x b ¬p H =
            ≡begin 
                (f⁻¹ $ f (inject₁ x , b))
            ≡⟨ cong f⁻¹ $  invˡ-inj₂-case x b ¬p H ⟩
                f⁻¹ (inj₂ (x , b))
            ≡⟨⟩
                (inject₁ x , b)
            ≡∎

    invʳ-sub
        : (x : Fin $ ℕ.suc a)
        → (b : B x)
        → (Dec (x ≡ fromℕ a))
        → (f⁻¹ $ f (x , b)) ≡ (x , b)
    invʳ-sub x b (yes p') = 
        let (p , H) = dec-yes-case {Fin $ ℕ.suc a} {λ x → x ≡ fromℕ a} 
                                   x (λ x → x Data.Fin.≟ fromℕ a) p'
        in
        invʳ-sub-inj₁-case x b p H
    invʳ-sub x b (no  ¬p') = 
        -- Idea: recycle the invˡ-inj₂-case proof after showing
        -- that x must be of the form (inject₁ x').
        -- #TODO: I copied this proof from invˡ-inj₂-case which copied it from
        -- the def of f or f⁻¹. Better to refactor it perhaps?
        let p' : a ≢ toℕ x
            p' z = ¬p' $ sym $ toℕ-injective $ trans (toℕ-fromℕ a) z
        in
        let v : Σ[ x' ∈ Fin a ](x ≡ inject₁ x')
            v = (lower₁ x p' , sym (inject₁-lower₁ x p'))
        in
        let (x' , x≡inject₁x') = v in
        let b' : B (inject₁ x')
            b' = subst B x≡inject₁x' b
        in
        let ¬p'' : (inject₁ x') ≢ fromℕ a
            ¬p'' = subst (λ x → x ≢ fromℕ a) x≡inject₁x' ¬p'
        in
        let (¬p , H) = dec-no-case {Fin $ ℕ.suc a} {λ x → x ≡ fromℕ a} 
                                   (inject₁ x') (λ x → x Data.Fin.≟ fromℕ a) ¬p''
        in
        let k : (f⁻¹ $ f (inject₁ x' , b')) ≡ (inject₁ x' , b')
            k = invʳ-sub-inj₂-case-inject₁ x' b' ¬p H
        in
        let tuplesEq : (inject₁ x' , b') ≡ (x , b)
            tuplesEq = tuple-with-subst {B = B} 
                             id x (inject₁ x') b (sym x≡inject₁x') x≡inject₁x'
        in
        subst (λ t → (f⁻¹ $ f t) ≡ t) tuplesEq k

    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {x , b} {y} refl = invʳ-sub x b (x Data.Fin.≟ fromℕ a)

    

-- A finite sum of finite sets is equivalent to a single finite set.
--
-- #TODO: The size 'z' is given as a rather black box,
-- but on paper I have a proof it equals
-- `fold (Fin (suc a)) 0 λsum.λx.(f x + sum)`.
fin-Σ-fun
    : (a : ℕ)
    → (f : Fin a → ℕ)
    → Σ[ z ∈ ℕ ]((Σ[ x ∈ Fin a ] Fin (f x)) ≃ (Fin z))
fin-Σ-fun 0 f = 
    let z = 0 in
    let H : (Σ[ x ∈ Fin 0 ] Fin (f x)) ≃ (Fin z)
        H = begin 
                (Σ[ x ∈ Fin 0 ] Fin (f x))
            ≃⟨ Σfin0 (λ x → Fin (f x)) ⟩
                ⊥
            ≃⟨ ≃-sym fin0 ⟩
                Fin 0
            ∎
    in (z , H)
fin-Σ-fun (suc a) f = 
    let zₐ : ℕ
        zₐ = proj₁ $ fin-Σ-fun a (f ∘ inject₁)
    in
    let z : ℕ
        z = (f $ fromℕ a) + zₐ
    in
    let H : (Σ[ x ∈ Fin (ℕ.suc a) ] Fin (f x)) ≃ (Fin z)
        H = begin 
                (Σ[ x ∈ Fin (ℕ.suc a) ] Fin (f x))
            ≃⟨ fin-Σ-takeout-first a (Fin ∘ f) ⟩
                ((Fin $ f $ fromℕ a) ⊎ Σ[ x ∈ Fin a ] (Fin $ f $ inject₁ x))
            ≃⟨ rewr-≃-under-⊎-right (proj₂ $ fin-Σ-fun a (f ∘ inject₁)) ⟩
                ((Fin $ f $ fromℕ a) ⊎ (Fin zₐ))
            ≃⟨ fin-⊎-+ (f $ fromℕ a) zₐ ⟩
                Fin z
            ∎
    in
    (z , H)


