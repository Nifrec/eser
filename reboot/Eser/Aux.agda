-- Module      : Eser.Signature.Aux
-- Description : Very general (and well-known) definitions and lemmas
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
open import Level
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.List
open import Data.Fin using (Fin)
open import Function hiding (_↔_)

open import Eser.Logic
module Eser.Aux where

--------------------------------------------------------------------------------
-- General mathematical definitions
--------------------------------------------------------------------------------
indices : {A : Set} → List A → Set
indices {A} L = Fin (Data.List.length L)

-- Biimplication: existance of functions both ways, 
-- they do not need to be inverses of each other.
_↔_ : (A B : Set) → Set
A ↔ B = (A → B) × (B → A)

-- Homotopy between functions, i.e., pointwise equality.
-- I.e., the functions are the same input-output map,
-- but may have different implementations.
-- A more general, but rather overcomplicated and confusing, definition
-- can be found in the stdlib in Function.Relation.Binary.Setoid.Equality.
_≈_ : {A : Set} → {B : A → Set} → Rel ((a : A) → B a) 0ℓ
_≈_ {A} {B} f g = (a : A) → f a ≡ g a

≈-sym : {A : Set} → {B : A → Set} → Symmetric (_≈_ {A} {B})
≈-sym {A} {B} {f} {g} f≈g a = sym (f≈g a)

isContr : (A : Set) → Set
isContr A = Σ[ a ∈ A ]((a' : A) → a ≡ a')

Between : (a b : ℕ) → ℕ → Set
Between a b ℓ = (a < ℓ) × (ℓ < b)
 
--------------------------------------------------------------------------------
-- Substitution of equalities
--------------------------------------------------------------------------------

doubleSubst
    : {A B : Set}
    → (X : A → B → Set)
    → {a a' : A}
    → {b b' : B} 
    → (ha : a ≡ a')
    → (hb : b ≡ b')
    → X a b
    → X a' b'
doubleSubst X refl refl x = x

proj₁₂ 
    : {A : Set}
    → {B : A → Set}
    → {C : (a : A) → B a → Set}
    → (x : Σ[ a ∈ A ](Σ[ b ∈ B a ] C a b))
    → B (proj₁ x)
proj₁₂ = proj₁ ∘ proj₂

proj₃ 
    : {A : Set}
    → {B : A → Set}
    → {C : (a : A) → B a → Set}
    → (x : Σ[ a ∈ A ](Σ[ b ∈ B a ] C a b))
    → C (proj₁ x) (proj₁ $ proj₂ x)
proj₃ = proj₂ ∘ proj₂

-- If first elements of pairs are equal, and the second elements
-- are proof-irrelevant, then the whole pairs are also equal.
restIsProofIrrel 
    : {A : Set} 
    → {B : A → Set} 
    → ((a : A) → Relation.Nullary.Irrelevant (B a))
    → {a a' : A}
    → (b : B a)
    → (b' : B a')
    → (a ≡ a')
    → (a , b) ≡ (a' , b')
restIsProofIrrel H {a} {a} b b' refl =
    cong (λ b → (a , b)) (H a b b')

--------------------------------------------------------------------------------
-- Natural number arithmetic
--------------------------------------------------------------------------------

m∸Sn≤m∸n
    : (n m : ℕ)
    → m ∸ ℕ.suc n ≤ m ∸ n
m∸Sn≤m∸n n m =
    let H : (m ∸ n) ∸ 1 ≡ m ∸ (ℕ.suc n)
        H = begin 
                (m ∸ n) ∸ 1
            ≡⟨ ∸-+-assoc m n 1 ⟩
                m ∸ (n + 1)
            ≡⟨ cong (λ x → m ∸ x) (+-comm n 1) ⟩
                m ∸ (1 + n)
            ≡⟨⟩
                m ∸ (ℕ.suc n)
            ∎
    in
    subst (λ x → x ≤ m ∸ n) H (m∸n≤m (m ∸ n) 1)
        
sumToSub
    : (m n ℓ : ℕ)
    → m + n ≡ ℓ
    → n ≡ ℓ ∸ m
sumToSub m n ℓ m+n≡ℓ = 
    let H : (m + n) ∸ m ≡ ℓ ∸ m
        H = cong (_∸ m) m+n≡ℓ
    in
    subst (λ x → x ≡ ℓ ∸ m) (Data.Nat.Properties.m+n∸m≡n m n) H

≤⊎< : (n m : ℕ) → n ≤ m ⊎ m < n
≤⊎< n m with n ≤? m
... | yes n≤m = inj₁ n≤m
... | no n≰m = inj₂ (≰⇒> n≰m)

-- If a + b = m and both a≥1 and b≥1 then a<m and b<m.
posSummandsThenSmaller
    : {a b m : ℕ}
    → (ℕ.suc a) + (ℕ.suc b) ≡ m
    → ℕ.suc a < m
posSummandsThenSmaller {a} {b} {m} Sa+Sb≡m =
    let a' = ℕ.suc a
    in
    let H : m ≤ a' ⊎ a' < m
        H = ≤⊎< m a'
    in
    let a+Sb≡Sa+b : a + ℕ.suc b ≡ ℕ.suc a + b
        a+Sb≡Sa+b = +-suc a b
    in
    let a'≤a'+b : a' ≤ a' + b
        a'≤a'+b = m≤n⇒m≤n+o b ≤-refl
    in
    let a'<a'+Sb : a' < a' + ℕ.suc b 
        a'<a'+Sb = s≤s (subst (λ x → a' ≤ x) (sym a+Sb≡Sa+b) a'≤a'+b )
    in
    let m≰a' : ¬ (m ≤ a')
        m≰a' m≤a' = <-irrefl refl 
            (subst (λ x → m < x) Sa+Sb≡m (≤-<-trans m≤a' a'<a'+Sb))
    in
    elimCaseLeft H m≰a'

+-injective
    : {n m l : ℕ}
    → n + m ≡ n + l
    → m ≡ l
+-injective {zero} {m} {l} H = H
+-injective {suc n} {m} {l} H = +-injective (suc-injective H)

+-injective-right
    : {n m l : ℕ}
    → m + n ≡ l + n
    → m ≡ l
+-injective-right {n} {m} {l} m+n≡l+n =
    let H : n + m ≡ n + l
        H = begin 
                n + m
            ≡⟨ +-comm n m ⟩
                m + n
            ≡⟨ m+n≡l+n ⟩
                l + n
            ≡⟨ +-comm l n ⟩
                n + l
            ∎
    in +-injective H

¬1+m+1+n≡1
    : {m n : ℕ}
    → (ℕ.suc m + ℕ.suc n ≡ 1)
    → ⊥
¬1+m+1+n≡1 {m} {n} p = 
    let H : ℕ.suc ( ℕ.suc (m + n)) ≡ 1
        H = trans (sym $ +-suc (ℕ.suc m) n) p
    in
    1+n≢0 {m + n} (suc-injective H)


bracketRewr : (n m : ℕ) → n + (ℕ.suc $ ℕ.suc m ) ≡ n + 1 + (1 + m)
bracketRewr n m =     
        begin 
            n + (ℕ.suc $ ℕ.suc m )       
        ≡⟨⟩
            n + (1 + ℕ.suc m)
        ≡⟨ sym $ +-assoc n 1 (ℕ.suc m) ⟩
            (n + 1) + ℕ.suc m
        ∎

m<m+1+n : (m n : ℕ) → m < m + (1 + n)
m<m+1+n m n = m<m+n m $ 0<1+n {n}

≡→≤ : {m n : ℕ} → m ≡ n → m ≤ n
≡→≤ {m} {n} refl = ≤-refl

-- Every number is either 0 or the successor of another number.
nullOrSuc
    : (n : ℕ)
    → n ≡ 0 ⊎ Σ[ n' ∈ ℕ ]( n ≡ ℕ.suc n')
nullOrSuc 0 = inj₁ refl
nullOrSuc (suc n') = inj₂ $ (n' , refl)

-- *-suc but with some reordering of the operands
-- (which is equivalent since * and + are commutative).
*-suc-rev
    : (n m : ℕ)
    → n * m + m ≡ (ℕ.suc n) * m
*-suc-rev n m =
    begin 
        n * m + m
    ≡⟨ cong (_+ m) (*-comm n m) ⟩
        m * n + m
    ≡⟨ +-comm (m * n) m ⟩
        m + m * n
    ≡⟨ sym $ *-suc m n ⟩
        m * (ℕ.suc n)
    ≡⟨ *-comm m (ℕ.suc n) ⟩
        (ℕ.suc n) * m
    ∎
    
n*a+[a+b]≡Sn*a+b
    : (n a b : ℕ)
    → n * a + (a + b) ≡ (ℕ.suc n) * a + b
n*a+[a+b]≡Sn*a+b n a b = 
    begin 
        n * a + (a + b)
    ≡⟨  sym $ +-assoc (n * a) a b ⟩
        (n * a + a) + b
    ≡⟨ cong (_+ b) (*-suc-rev n a) ⟩
        (ℕ.suc n) * a + b
    ∎
    
m<n→Sm>n⊎Sm≡n
    : {m n : ℕ}
    → m < n
    → ℕ.suc m < n ⊎ ℕ.suc m ≡ n
m<n→Sm>n⊎Sm≡n {m} {n} m<n = 
    let Sm≤n : ℕ.suc m ≤ n
        Sm≤n = m<n
    in
    m≤n⇒m<n∨m≡n Sm≤n

-- Sublemma of injF-suci-ineq-case in Eser.Equivalence.Properties.
+-comm-both-sides
    : (a b c n m k : ℕ)
    → a + b + c < n + m + k
    → b + a + c < m + n + k
+-comm-both-sides a b c n m k H = 
    subst (λ y → y + c < m + n + k) (+-comm a b)
    $ subst (λ y → a + b + c < y + k) (+-comm n m) H


--------------------------------------------------------------------------------
-- Properties of ≡ᵇ used in Eser.EqRel.Conversions
--------------------------------------------------------------------------------
open import Data.Bool using (true)

numIsItself : (n : ℕ) → (n ≡ᵇ n) ≡ true
numIsItself zero = refl
numIsItself (ℕ.suc n) = numIsItself n

numEqualSym : (n m : ℕ) → (n ≡ᵇ m) ≡ true → (m ≡ᵇ n) ≡ true
numEqualSym ℕ.zero ℕ.zero n≡m = refl
numEqualSym (ℕ.suc n) (ℕ.suc m) Sn≡Sm = numEqualSym n m Sn≡Sm

numEqualTrans : 
    (n m ℓ : ℕ) 
    → (n ≡ᵇ m) ≡ true 
    → (m ≡ᵇ ℓ) ≡ true
    → (n ≡ᵇ ℓ) ≡ true
numEqualTrans ℕ.zero ℕ.zero ℕ.zero n≡m m≡ℓ = refl
numEqualTrans (ℕ.suc n) (ℕ.suc m) (ℕ.suc ℓ) Sn≡Sm Sm≡Sℓ = 
    numEqualTrans n m ℓ Sn≡Sm Sm≡Sℓ



--------------------------------------------------------------------------------
-- ℕ-Arithmetic used in the injectivity proof of Σfin-inf-inhabited
--------------------------------------------------------------------------------
module Σfin-inf-inhabited-arithmetic where
    infix 4 _ℕ<_ _ℕ≤_
    _ℕ<_ = Data.Nat._<_
    _ℕ≤_ = Data.Nat._≤_
    ℕ<-trans = Data.Nat.Properties.<-trans
    ℕ<-≤-trans = Data.Nat.Properties.<-≤-trans
    ℕ≤-<-trans = Data.Nat.Properties.<-≤-trans
    open import Data.Fin hiding (_+_)
    open import Data.Fin.Properties

    m<n+1+m
        : (m n : ℕ)
        → m ℕ< n + 1 + m
    m<n+1+m m n = m<n+m m {n + 1} 0<n+1
        where
            0<n+1 : 0 ℕ< n + 1
            0<n+1 = subst (λ y → 0 ℕ< y) (+-comm 1 n) (s≤s z≤n)

    n+m<n+1+m
        : (m n : ℕ)
        → n + m ℕ< n + 1 + m
    n+m<n+1+m m n = subst (λ y → n + m ℕ< y) (sym $ +-assoc n 1 m)
        $ +-monoʳ-< n (n<1+n m)

    m<n+1+TFm
        : (m n : ℕ)
        → m ℕ< n + 1 + (toℕ $ fromℕ m)
    m<n+1+TFm m n = 
        subst (λ y → m ℕ< n + 1 + y) (sym $ toℕ-fromℕ m) (m<n+1+m m n)

    n<k→m+n<m+k
        : {n k : ℕ}
        → (m : ℕ)
        → n ℕ< k
        → m + n ℕ< m + k
    n<k→m+n<m+k {n} {k} m n<k = +-monoʳ-< m n<k

    Tx+1+y≡Tx'+1+y→x≡x'
        : {n n' : ℕ}
        → (h : ℕ → ℕ)
        → (x : Fin (h n))
        → (x' : Fin (h n'))
        → (y y' : ℕ)
        → (n ≡ n')
        → (y ≡ y')
        → toℕ x + 1 + y ≡ toℕ x' + 1 + y'
        → (n , x) ≡ (n' , x')
    Tx+1+y≡Tx'+1+y→x≡x' {n} h x x' y y refl refl H = cong (λ x → (n , x)) H'
        where
            H'' : toℕ x ≡ toℕ x'
            H'' = +-injective-right $ +-injective-right H
            H' : x ≡ x'
            H' = toℕ-injective H''
            


--------------------------------------------------------------------------------
-- Rewriting equalities
--------------------------------------------------------------------------------
open import Relation.Binary.PropositionalEquality
open import Data.Product

tuple-with-subst
    : {A A' : Set}
    → {B : A' → Set}
    → (f : A → A')
    → (x x' : A)
    → (b : B (f x))
    → x' ≡ x
    → (R : f x ≡ f x')
    → (x' , subst B R b) ≡ (x , b)
tuple-with-subst {A} {A'} {B} f x x b refl refl = refl

--------------------------------------------------------------------------------
-- Finite sets
--------------------------------------------------------------------------------
-- The imports for Fin are down here to avoid name clashes with Data.Nat.
open import Data.Fin hiding (_≤_ ; _+_ ; _<_)
open import Data.Fin.Properties hiding (_≤?_)
open import Data.Product

finOpposite
    : (w : ℕ)
    → (x : Fin (ℕ.suc w))
    → Σ[ y ∈ Fin (ℕ.suc w) ](toℕ x + toℕ y ≡ w)
finOpposite w x = (opposite x , p)
    where
        y = opposite x
        p =
            begin 
                toℕ x + toℕ y
            ≡⟨ +-comm (toℕ x) (toℕ y) ⟩
                toℕ y + toℕ x
            ≡⟨ cong (λ z → z + toℕ x) (opposite-prop x) ⟩
                ((ℕ.suc w) ∸ (ℕ.suc (toℕ x))) + (toℕ x)
            ≡⟨⟩
                (w ∸ (toℕ x)) + (toℕ x)
            ≡⟨ m∸n+n≡m {w} {toℕ x} (s≤s⁻¹ $ toℕ<n x) ⟩
                w
            ∎
            
sucStillSmaller
    : {n m : ℕ}
    → n < m
    → ℕ.suc n ≢ m
    → ℕ.suc n < m
sucStillSmaller {n} {m} n<m 1+n≢m = 
    let 1+n≡m⊎1+n<m : ℕ.suc n < m ⊎ ℕ.suc n ≡ m
        1+n≡m⊎1+n<m = m≤n⇒m<n∨m≡n n<m
    in
    elimCaseRight 1+n≡m⊎1+n<m 1+n≢m

-- Given x ∈ Fin (w-1), there exists a y ∈ Fin (w-1)
-- such that 1+x + 1+y ≡ w.
-- Or equivalently, x ∈ Fin w and y ∈ Fin w and 1+x + 1+y ≡ 1+w.
finOppositeSuc
    : (w : ℕ)
    → (x : Fin w)
    → Σ[ y ∈ Fin w ]( ℕ.suc (toℕ x) + ℕ.suc (toℕ y) ≡ ℕ.suc w)
finOppositeSuc 0 ()
finOppositeSuc w@(suc w') x = 
    let (y , x+y≡w') = finOpposite w' x in
    let x' = toℕ x in
    let y' = toℕ y in
    let SS[x+y]≡Sw : ℕ.suc (ℕ.suc (x' + y')) ≡ ℕ.suc w
        SS[x+y]≡Sw = cong (ℕ.suc ∘ ℕ.suc) x+y≡w'
    in
    let p : ℕ.suc (toℕ x) + ℕ.suc (toℕ y) ≡ ℕ.suc w
        p = begin 
                ℕ.suc x' + ℕ.suc y' 
            ≡⟨  +-suc (ℕ.suc x') y'   ⟩
                ℕ.suc (ℕ.suc x') + y'
            ≡⟨⟩ -- Definition of _+_:
                ℕ.suc ( ℕ.suc (x' + y'))
            ≡⟨  SS[x+y]≡Sw ⟩
                ℕ.suc w 
            ∎
    in 
    (y , p)
    

-- Given two pairs (i , x), (i' , x') ∈ Σ[ n ∈ ℕ ] Fin n
-- such that (i , x) ≡ (i' , x')
-- then it follows that both i ≡ i' and toℕ x ≡ toℕ x'.
-- (Note: we can't say x ≡ x'; that'd be ill-typed, unless we add a subst with i
-- ≡ i').
proj₁-eq-fin-tuples 
    : {i i' : ℕ}
    → {x : Fin i}
    → {x' : Fin i'}
    → (i , x) ≡ (i' , x')
    → i ≡ i'
proj₁-eq-fin-tuples {i} {i} refl = refl
proj₂-eq-fin-tuples 
    : {i i' : ℕ}
    → (x : Fin i)
    → (x' : Fin i')
    → (i , x) ≡ (i' , x')
    → toℕ x ≡ toℕ x'
proj₂-eq-fin-tuples {i} {i} x x refl = refl

