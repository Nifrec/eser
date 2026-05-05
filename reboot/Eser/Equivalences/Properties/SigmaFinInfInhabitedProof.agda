-- Module      : Eser.Equivalences.Properties.SigmaFinInfInhabitedProof
-- Description : Proof of Σfin-inf-inhabited from Eser.Equivalences.Properties.
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
open import Function.Properties.Bijection using (⤖⇒↔)

open import Eser.Aux
open import Eser.Fin
open import Eser.Dec
open import Eser.Equivalences.Notation
open import Eser.Stdlib using (fin-≡-irrelevant)
open import Eser.Fin using (finMaxOrSmaller)

module Eser.Equivalences.Properties.SigmaFinInfInhabitedProof where

-- #TODO: ≃-from-inj-surj and surjectiveAt are defined here instead
-- of in Eser.Equivalances.Properties to avoid circular imports.
≃-from-inj-surj
    : {A B : Set}
    → (f : A → B)
    → (Injective _≡_ _≡_ f)
    → (Surjective _≡_ _≡_ f)
    → A ≃ B
≃-from-inj-surj {A} {B} f injF surjF = ⤖⇒↔ $ mk⤖ (injF , surjF)

-- The stdlib's definition of surjectivity is a bit indirect
-- because it also allows other relations than _≡_.
-- For the _≡_ relations,
-- the stdlib's definition of surjectivity simplifies to:
--      `(b : B) → surjectiveAt f b`
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
Σfin-inf-inhabited-proof
    : (g : ℕ → ℕ)
    → Σ[ i ∈ ℕ ](Fin $ ℕ.suc $ g i) ≃ ℕ
-- Proof: give a function and show it is injective and surjective.
Σfin-inf-inhabited-proof g = ≃-from-inj-surj f' injF surjF
    module SigmaFinInfInhabitedProofImpl where
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
        ≥minOfSet {ℕ.zero} x = z≤n
        -- First get 0 < x, then use that `_+ 1` and `_+ f' (...)` are monotone.
        ≥minOfSet {ℕ.suc i} x = +-monoˡ-≤ (f' (i , fromℕ (g i)) ) 
                              $ +-monoˡ-≤ 1 z≤n
        ≤maxOfSet
            : {i : ℕ}
            → (x : Fin $ ℕ.suc $ g i)
            → f' (i , x) ℕ≤ f' (i , fromℕ (g i))
        ≤maxOfSet {ℕ.zero} x = fin≤TFMax {g 0} x
        ≤maxOfSet {ℕ.suc i} x =
            let H : toℕ x ℕ≤ (toℕ $ fromℕ $ g $ ℕ.suc i)
                H = fin≤TFMax {g $ ℕ.suc i} x
            in
            +-monoˡ-≤ (f' (i , fromℕ (g i))) $ +-monoˡ-≤ 1 H

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
                H' = +-comm-both-sides 1 (g $ ℕ.suc i) (f' (i , fromℕ (g i)))
                                       0 1             (f' (i' , fromℕ (g i')))
                                       H
            in
            -- This is what H actually says, up to a toℕ∘fromℕ ≈ id conversion.
            -- This is the most extreme case where
            --      x ≗ g (ℕ.suc i) is maximal
            -- and 
            --      x' ≗ 0
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

