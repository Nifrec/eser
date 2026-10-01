-- Module      : Eser.Vec
-- Description : Additional properties of Vec.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
open import Level hiding (suc)
--open import Data.Bool using (Bool ; true) renaming (T to IsTrue)
open import Data.Nat
open import Data.Nat.Properties
--open import Data.Sum hiding (reduce ; map)
--open import Data.Product hiding (map)
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
--open ≡-Reasoning -- renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Relation.Unary using (_⊆_)
open import Data.Vec
open import Data.Vec.Membership.Propositional as Mem
--open import Data.Vec.Relation.Unary.All as All hiding (_∷_ ; head ; tail ;
--map)
open import Data.Vec.Relation.Unary.Any as Any hiding (head ; tail ; map)
open import Function hiding (_↔_)

open import Eser.NewSigStream.EnumVectors using (weight)

module Eser.Vec where

-- Replace all occurrences of one element in a vector by another element.
replace-all 
    : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → {n : ℕ}
    → (v : Vec A n)
    → A -- Element to replace all occurrences of.
    → A -- Replacement.
    → Vec A n
replace-all {A} _≡?_ v a b = map replace-if-matches v
    module ReplaceAllImpl where
        replace-if-matches : A → A
        replace-if-matches x = cases (x ≡? a)
            module Cases where
                cases : (Dec (x ≡ a)) → A
                cases (yes _) = b
                cases (no _) = x

-- When replacing x' by x' if x' ≡ x, and not replacing it if x' ≢ x, 
-- the output is always x', regardless of whether x and x' are equal.
replace-all-cases-doesn't-matter
    : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → {n : ℕ}
    → (v : Vec A n)
    → (x x' : A)
    → (d : Dec (x' ≡ x))
    → ReplaceAllImpl.Cases.cases _≡?_ v x x' x' d ≡ x'
replace-all-cases-doesn't-matter _≡?_ v x x' (yes x'≡x) = refl
replace-all-cases-doesn't-matter _≡?_ v x x' (no x'≢x) = refl

replace-all-not-member
    : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → {n : ℕ}
    → (v : Vec A n)
    → (x x' : A)
    → x ∉ v
    → replace-all _≡?_ v x x' ≡ v
replace-all-not-member _≡?_ [] x x' x∉v = refl
replace-all-not-member _≡?_ (y ∷ ys) x x' x∉v = 
    begin 
        replace-all _≡?_ (y ∷ ys) x x'
    ≡⟨⟩
        replace-if-matches y ∷ map replace-if-matches ys
    ≡⟨⟩
        cases (y ≡? x) ∷ map replace-if-matches ys
    ≡⟨⟩
        cases (y ≡? x) ∷ replace-all _≡?_ ys x x'
    ≡⟨ cong (cases (y ≡? x) ∷_) $ replace-all-not-member _≡?_ ys x x' x∉ys ⟩
        cases (y ≡? x) ∷ ys
    ≡⟨ cong (λ d → cases d ∷ ys) $ dec-no (y ≡? x) y≢x  ⟩
        cases (no y≢x) ∷ ys
    ≡⟨⟩
        y ∷ ys
    ∎ 
    where
        open ≡-Reasoning
        open ReplaceAllImpl _≡?_ (y ∷ ys) x x'
        open ReplaceAllImpl.Cases _≡?_ (y ∷ ys) x x' y
        y≢x : y ≢ x
        y≢x y≡x = x∉v (Any.here $ sym y≡x)
        x∉ys : x ∉ ys
        x∉ys = x∉v ∘ Any.there

-- Replacing an other element of v than z ∈ v, keeps z in the output.
replace-all-keep
    : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → {n : ℕ}
    → (v : Vec A n)
    → (x x' z : A)
    → z ∈ v
    → x ≢ z
    → z ∈ replace-all _≡?_ v x x'
replace-all-keep _≡?_ v@(z ∷ ys) x x' z (Any.here refl) x≢z = Any.here (sym eq)
    where
        open ≡-Reasoning
        open ReplaceAllImpl _≡?_ v x x'
        open ReplaceAllImpl.Cases _≡?_ v x x' z
        eq : replace-if-matches z ≡ z
        eq =
            begin 
                replace-if-matches z
            ≡⟨⟩
                cases (z ≡? x)
            ≡⟨ cong cases $ dec-no (z ≡? x) $ ≢-sym x≢z ⟩
                cases (no $ ≢-sym x≢z)
            ≡⟨⟩
                z
            ∎
replace-all-keep _≡?_ (y ∷ ys) x x' z (Any.there z∈ys) x≢z = 
    Any.there $ replace-all-keep _≡?_ ys x x' z z∈ys x≢z

-- Replacing an element of v by x' does not introduce any other element than x'.
replace-all-nospawn
    : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → {n : ℕ}
    → (v : Vec A n)
    → (x x' z : A)
    → z ∉ v
    → x' ≢ z
    → z ∉ replace-all _≡?_ v x x'
replace-all-nospawn _≡?_ v@(y ∷ ys) x x' z z∉v x'≢z (Any.here eq) = 
    cases (y ≡? x) refl
    where
        open ≡-Reasoning
        open ReplaceAllImpl _≡?_ v x x'
        open ReplaceAllImpl.Cases _≡?_ v x x' y renaming (cases to repl-cases)

        cases : (d : Dec (y ≡ x)) → (d ≡ (y ≡? x)) → ⊥
        cases (yes y≡x) eq-d = x'≢z $
            begin 
                x'
            ≡⟨⟩
                repl-cases (yes y≡x)
            ≡⟨ cong repl-cases eq-d ⟩
                repl-cases (y ≡? x)
            ≡⟨⟩
                replace-if-matches y
            ≡⟨ sym eq ⟩
                z
            ∎
        cases (no y≢x) eq-d = z∉v $ Any.here z≡y
            where
                z≡y : z ≡ y
                z≡y = 
                    begin 
                        z
                    ≡⟨ eq ⟩
                        replace-if-matches y
                    ≡⟨⟩
                        repl-cases (y ≡? x)
                    ≡⟨ cong repl-cases $ sym eq-d ⟩
                        repl-cases (no y≢x)
                    ≡⟨⟩
                        y
                    ∎
replace-all-nospawn _≡?_ {suc n'} v@(y ∷ ys) x x' z z∉v x'≢z (Any.there z∈v' ) = 
    z∉v' z∈v'
    where
        z∉ys : z ∉ ys
        z∉ys = z∉v ∘ Any.there

        z∉v' : z ∉ replace-all _≡?_ ys x x'
        z∉v' = replace-all-nospawn _≡?_ {n'} ys x x' z z∉ys x'≢z 

replace-all-comm
    : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → {n : ℕ}
    → (v : Vec A n)
    → {x x' z z' : A}
    → (x ≢ z)
    → (x ≢ z')
    → (z ≢ x')
    → replace-all _≡?_ (replace-all _≡?_ v z z') x x'
      ≡
      replace-all _≡?_ (replace-all _≡?_ v x x') z z'
replace-all-comm _≡?_ [] {x} {x'} {z} {z'} x≢z x≢z' z≢x' = refl
replace-all-comm {A} _≡?_ {suc n} v@(y ∷ ys) {x} {x'} {z} {z'} x≢z x≢z' z≢x' =
    begin 
        replace-all _≡?_ (replace-all _≡?_ (y ∷ ys) z z') x x'
    ≡⟨⟩
        replace-all _≡?_ (fzz' (y ≡? z) ∷ ys[z'/z] ) x x'
    ≡⟨⟩
        LHS-firstel ∷ ys[z'/z][x'/x]
    ≡⟨ cong (_∷ ys[z'/z][x'/x]) firstel-eq ⟩
        RHS-firstel ∷ ys[z'/z][x'/x]
    ≡⟨ cong (RHS-firstel ∷_) IH ⟩
        RHS-firstel ∷ ys[x'/x][z'/z]
    ≡⟨⟩
      replace-all _≡?_ (replace-all _≡?_ v x x') z z'
    ∎
    where
        -- A is hSet-truncated, i.e., a ≡ b is Irrelevant for all a, b : A,
        -- because A has decidable equality. 
        -- Irrelevance could also have been proven
        -- with the UIP, since we are not using Cubical compatibility.
        import Axiom.UniquenessOfIdentityProofs
        open Axiom.UniquenessOfIdentityProofs.Decidable⇒UIP _≡?_
            renaming (≡-irrelevant to ≡-irr)

        open ≡-Reasoning
        open ReplaceAllImpl.Cases _≡?_ v z z' y renaming (cases to fzz')
        open ReplaceAllImpl.Cases _≡?_ v x x' y renaming (cases to fxx')

        v[z'/z] : Vec A (suc n)
        v[z'/z] = replace-all _≡?_ (y ∷ ys) z z'

        -- We can't hardcode `a` to be `fzz' (y ≡? z)`,
        -- because then rewriting the latter's argument to `yes y≡z` or `no y≢z`
        -- results in ill-typed input,
        -- since `yes y≡z` is not judgementally equal to `fzz' (y ≡? z)`.
        fzz'xx' : {a : A} → (Dec (a ≡ x)) → A
        fzz'xx' {a} = cases
            where
                open ReplaceAllImpl.Cases _≡?_ v[z'/z] x x' a

        v[x'/x] : Vec A (suc n)
        v[x'/x] = replace-all _≡?_ (y ∷ ys) x x'

        -- Same subtlety as with fzz'xx'.
        fxx'zz' : {a : A} → (Dec (a ≡ z)) → A
        fxx'zz' {a} = cases
            where
                open ReplaceAllImpl.Cases _≡?_ v[x'/x] z z' a

        ys[z'/z] : Vec A n
        ys[z'/z] = replace-all _≡?_ ys z z'

        ys[z'/z][x'/x] : Vec A n
        ys[z'/z][x'/x] = replace-all _≡?_ ys[z'/z] x x'

        ys[x'/x] : Vec A n
        ys[x'/x] = replace-all _≡?_ ys x x'
    
        ys[x'/x][z'/z] : Vec A n
        ys[x'/x][z'/z] = replace-all _≡?_ ys[x'/x] z z'

        IH : ys[z'/z][x'/x] ≡ ys[x'/x][z'/z]
        IH = replace-all-comm _≡?_ ys x≢z x≢z' z≢x'

        LHS-firstel : A
        LHS-firstel = fzz'xx' ((fzz' (y ≡? z)) ≡? x)

        RHS-firstel : A
        RHS-firstel = fxx'zz' ((fxx' (y ≡? x)) ≡? z)

        cases : (Dec (y ≡ z)) → (Dec (y ≡ x)) → LHS-firstel ≡ RHS-firstel
        cases (yes y≡z) (yes y≡x) = ⊥-elim $ x≢z $ trans (sym y≡x) y≡z
        cases (yes y≡z) (no y≢x) =
            begin 
                LHS-firstel
            ≡⟨⟩
                fzz'xx' ((fzz' (y ≡? z)) ≡? x)
            ≡⟨ cong (λ d → fzz'xx' ((fzz' d) ≡? x)) 
               $ dec-yes-irr (y ≡? z) ≡-irr y≡z
             ⟩
                fzz'xx' ((fzz' (yes y≡z)) ≡? x)
            ≡⟨⟩
                fzz'xx' (z' ≡? x)
            ≡⟨ cong fzz'xx' $ dec-no (z' ≡? x) $ ≢-sym x≢z' ⟩
                fzz'xx' (no $ ≢-sym x≢z')
            ≡⟨⟩
                z'
            ≡⟨⟩
                fxx'zz' (yes y≡z)
            ≡⟨ cong fxx'zz' $ sym $ dec-yes-irr (y ≡? z) ≡-irr y≡z ⟩
                fxx'zz' (y ≡? z)
            ≡⟨⟩
                fxx'zz' ((fxx' (no y≢x)) ≡? z)
            ≡⟨ cong (λ d → fxx'zz' (fxx' d ≡? z)) $ sym $ dec-no (y ≡? x) y≢x ⟩
                fxx'zz' ((fxx' (y ≡? x)) ≡? z)
            ≡⟨⟩
                RHS-firstel
            ∎
        cases (no y≢z) (yes y≡x) =
            begin 
                LHS-firstel
            ≡⟨⟩
                fzz'xx' ((fzz' (y ≡? z)) ≡? x)
            ≡⟨ cong (λ d → fzz'xx' ((fzz' d) ≡? x)) $ dec-no (y ≡? z) y≢z ⟩
                fzz'xx' ((fzz' (no y≢z)) ≡? x)
            ≡⟨⟩
                fzz'xx' (y ≡? x)
            ≡⟨ cong fzz'xx' $ dec-yes-irr (y ≡? x) ≡-irr y≡x ⟩
                fzz'xx' (yes y≡x)
            ≡⟨⟩
                x'
            ≡⟨⟩
                fxx'zz' (no $ ≢-sym z≢x')
            ≡⟨ cong fxx'zz' $ sym $ dec-no (x' ≡? z) $ ≢-sym z≢x' ⟩
                fxx'zz' (x' ≡? z)
            ≡⟨⟩
                fxx'zz' ((fxx' (yes y≡x)) ≡? z)
            ≡⟨ cong (λ d → fxx'zz' (fxx' d ≡? z)) 
                $ sym $ dec-yes-irr (y ≡? x) ≡-irr y≡x 
             ⟩
                fxx'zz' ((fxx' (y ≡? x)) ≡? z)
            ≡⟨⟩
                RHS-firstel
            ∎
        cases (no y≢z) (no y≢x) =
            begin 
                LHS-firstel
            ≡⟨⟩
                fzz'xx' ((fzz' (y ≡? z)) ≡? x)
            ≡⟨ cong (λ d → fzz'xx' ((fzz' d) ≡? x)) $ dec-no (y ≡? z) y≢z ⟩
                fzz'xx' ((fzz' (no y≢z)) ≡? x)
            ≡⟨⟩
                fzz'xx' (y ≡? x)
            ≡⟨ cong fzz'xx' $ dec-no (y ≡? x) y≢x ⟩
                fzz'xx' (no y≢x)
            ≡⟨⟩
                y
            ≡⟨⟩
                fxx'zz' (no y≢z)
            ≡⟨ cong fxx'zz' $ sym $ dec-no (y ≡? z) y≢z ⟩
                fxx'zz' (y ≡? z)
            ≡⟨⟩
                fxx'zz' ((fxx' (no y≢x)) ≡? z)
            ≡⟨ cong (λ d → fxx'zz' (fxx' d ≡? z)) $ sym $ dec-no (y ≡? x) y≢x ⟩
                fxx'zz' ((fxx' (y ≡? x)) ≡? z)
            ≡⟨⟩
                RHS-firstel
            ∎

        firstel-eq : LHS-firstel ≡ RHS-firstel
        firstel-eq = cases (y ≡? z) (y ≡? x)

-- When replacing x by x' in a vector v, and x ∈ v, then the resulting
-- vector contains x'.
replace-all-effect
    : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → {n : ℕ}
    → {v : Vec A n}
    → {x : A}
    → (x' : A)
    → x ∈ v
    → x' ∈ replace-all _≡?_ v x x'
replace-all-effect _≡?_ {v = y ∷ ys} {x = x} x' (Any.here x≡y) = Any.here eq
    where
        import Axiom.UniquenessOfIdentityProofs
        open Axiom.UniquenessOfIdentityProofs.Decidable⇒UIP _≡?_
            renaming (≡-irrelevant to ≡-irr)
        open ReplaceAllImpl.Cases _≡?_ (y ∷ ys) x x' y
        eq : x' ≡ cases (y ≡? x)
        eq = sym $ cong cases $ dec-yes-irr (y ≡? x) ≡-irr (sym x≡y)
replace-all-effect _≡?_ {v = y ∷ ys} {x = x} x' (Any.there x∈ys) =
    Any.there $ replace-all-effect _≡?_ x' x∈ys

replace-all-halfcut
    : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → {n : ℕ}
    → (v : Vec A n)
    → (x z a : A)
    → replace-all _≡?_ (replace-all _≡?_ v x a) a z
      ≡
      replace-all _≡?_ (replace-all _≡?_ v x z) a z
replace-all-halfcut _≡?_ [] x z a = refl
replace-all-halfcut {A} _≡?_ {suc n} v@(y ∷ ys) x z a = 
    begin 
        replace-all _≡?_ (replace-all _≡?_ (y ∷ ys) x a) a z
    ≡⟨⟩
        replace-all _≡?_ (fxa (y ≡? x) ∷ ys[a/x] ) a z
    ≡⟨⟩
        LHS-firstel ∷ ys[a/x][z/a]
    ≡⟨ cong (_∷ ys[a/x][z/a]) firstel-eq ⟩
        RHS-firstel ∷ ys[a/x][z/a]
    ≡⟨ cong (RHS-firstel ∷_) IH ⟩
        RHS-firstel ∷ ys[z/x][z/a]
    ≡⟨⟩
      replace-all _≡?_ (replace-all _≡?_ v x z) a z
    ∎
    -- Proof is similar to replace-all-comm.
    where
        import Axiom.UniquenessOfIdentityProofs
        open Axiom.UniquenessOfIdentityProofs.Decidable⇒UIP _≡?_
            renaming (≡-irrelevant to ≡-irr)

        open ≡-Reasoning
        open ReplaceAllImpl.Cases _≡?_ v x a y renaming (cases to fxa)
        open ReplaceAllImpl.Cases _≡?_ v x z y renaming (cases to fxz)

        v[a/x] : Vec A (suc n)
        v[a/x] = replace-all _≡?_ (y ∷ ys) x a

        fxaaz : {b : A} → (Dec (b ≡ a)) → A
        fxaaz {b} = cases
            where
                open ReplaceAllImpl.Cases _≡?_ v[a/x] a z b

        v[z/x] : Vec A (suc n)
        v[z/x] = replace-all _≡?_ (y ∷ ys) x z

        fxzaz : {b : A} → (Dec (b ≡ a)) → A
        fxzaz {b} = cases
            where
                open ReplaceAllImpl.Cases _≡?_ v[z/x] a z b

        ys[a/x] : Vec A n
        ys[a/x] = replace-all _≡?_ ys x a

        ys[a/x][z/a] : Vec A n
        ys[a/x][z/a] = replace-all _≡?_ ys[a/x] a z

        ys[z/x] : Vec A n
        ys[z/x] = replace-all _≡?_ ys x z
    
        ys[z/x][z/a] : Vec A n
        ys[z/x][z/a] = replace-all _≡?_ ys[z/x] a z

        IH : ys[a/x][z/a] ≡ ys[z/x][z/a]
        IH = replace-all-halfcut _≡?_ ys x z a

        LHS-firstel : A
        LHS-firstel = fxaaz ((fxa (y ≡? x)) ≡? a)

        RHS-firstel : A
        RHS-firstel = fxzaz ((fxz (y ≡? x)) ≡? a)

        doesn't-matter
            : {n : ℕ}
            → (v : Vec A n)
            → (x x' : A)
            → ReplaceAllImpl.Cases.cases _≡?_ v x x' x' (x' ≡? x) ≡ x'
        doesn't-matter v x x' = 
            replace-all-cases-doesn't-matter _≡?_ v x x' (x' ≡? x)

        cases 
            : Dec (y ≡ x) 
            → Dec (y ≡ a) 
            → LHS-firstel ≡ RHS-firstel
        cases (yes y≡x) _ =
            begin 
                fxaaz ((fxa (y ≡? x)) ≡? a)
            ≡⟨ cong (λ d → fxaaz (fxa d ≡? a)) 
                $ dec-yes-irr (y ≡? x) ≡-irr y≡x 
             ⟩
                fxaaz ((fxa (yes y≡x)) ≡? a)
            ≡⟨⟩
                fxaaz (a ≡? a)
            ≡⟨ cong fxaaz $ dec-yes-irr (a ≡? a) ≡-irr refl ⟩
                fxaaz (yes refl)
            ≡⟨⟩
                z
            -- This equality holds both when z ≡ a and when z ≢ a!
            ≡⟨ sym $ doesn't-matter v[z/x] a z ⟩ 
                fxzaz (z ≡? a)
            ≡⟨⟩
                fxzaz ((fxz (yes y≡x)) ≡? a)
            ≡⟨  sym 
                $ cong (λ d → fxzaz (fxz d ≡? a)) 
                $ dec-yes-irr (y ≡? x) ≡-irr y≡x 
             ⟩
                fxzaz ((fxz (y ≡? x)) ≡? a)
            ∎
        cases (no  y≢x) (yes y≡a) =
            begin 
                fxaaz ((fxa (y ≡? x)) ≡? a)
            ≡⟨ cong (λ d → fxaaz (fxa d ≡? a)) 
                $ dec-no (y ≡? x) y≢x 
             ⟩
                fxaaz ((fxa (no y≢x)) ≡? a)
            ≡⟨⟩
                fxaaz (y ≡? a)
            ≡⟨ cong fxaaz $ dec-yes-irr (y ≡? a) ≡-irr y≡a ⟩
                fxaaz (yes y≡a)
            ≡⟨⟩
                z
            ≡⟨⟩
                fxzaz (yes y≡a)
            ≡⟨ sym $ cong fxzaz $ dec-yes-irr (y ≡? a) ≡-irr y≡a ⟩
                fxzaz (y ≡? a)
            ≡⟨⟩
                fxzaz ((fxz (no y≢x)) ≡? a)
            ≡⟨  sym
                $ cong (λ d → fxzaz (fxz d ≡? a)) 
                $ dec-no (y ≡? x) y≢x 
             ⟩
                fxzaz ((fxz (y ≡? x)) ≡? a)
            ∎
        cases (no  y≢x) (no  y≢a) =
            begin 
                fxaaz ((fxa (y ≡? x)) ≡? a)
            ≡⟨ cong (λ d → fxaaz (fxa d ≡? a)) 
                $ dec-no (y ≡? x) y≢x 
             ⟩
                fxaaz ((fxa (no y≢x)) ≡? a)
            ≡⟨⟩
                fxaaz (y ≡? a)
            ≡⟨ cong fxaaz $ dec-no (y ≡? a) y≢a ⟩
                fxaaz (no y≢a)
            ≡⟨⟩
                y
            ≡⟨⟩
                fxzaz (no y≢a)
            ≡⟨ sym $ cong fxzaz $ dec-no (y ≡? a) y≢a ⟩
                fxzaz (y ≡? a)
            ≡⟨⟩
                fxzaz ((fxz (no y≢x)) ≡? a)
            ≡⟨  sym
                $ cong (λ d → fxzaz (fxz d ≡? a)) 
                $ dec-no (y ≡? x) y≢x 
             ⟩
                fxzaz ((fxz (y ≡? x)) ≡? a)
            ∎
            
        firstel-eq : LHS-firstel ≡ RHS-firstel
        firstel-eq = cases (y ≡? x) (y ≡? a)
        
-- Replacing an element by itself has no effect.
replace-all-id
    : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → {n : ℕ}
    → (v : Vec A n)
    → (x : A)
    → replace-all _≡?_ v x x ≡ v
replace-all-id _ [] _ = refl
replace-all-id _≡?_ v@(y ∷ ys) x = cases (y ≡? x) refl
    where
        open ReplaceAllImpl.Cases _≡?_ v x x y renaming (cases to repl-cases)
        open ≡-Reasoning
        cases 
            : (d : Dec (y ≡ x)) 
            → ((y ≡? x) ≡ d) 
            → replace-all _≡?_ v x x ≡ v
        cases (yes y≡x) eq-d = 
            begin 
                replace-all _≡?_ v x x
            ≡⟨⟩
                repl-cases (y ≡? x) ∷ replace-all _≡?_ ys x x
            ≡⟨ cong (repl-cases (y ≡? x) ∷_) $ replace-all-id _≡?_ ys x ⟩
                repl-cases (y ≡? x) ∷ ys
            ≡⟨ cong (λ d → repl-cases d ∷ ys) eq-d  ⟩
                repl-cases (yes y≡x) ∷ ys
            ≡⟨⟩
                x ∷ ys
            ≡⟨ cong (_∷ ys) $ sym y≡x ⟩
                y ∷ ys
            ∎
        cases (no y≢x) eq-d = 
            begin 
                replace-all _≡?_ v x x
            ≡⟨⟩
                repl-cases (y ≡? x) ∷ replace-all _≡?_ ys x x
            ≡⟨ cong (repl-cases (y ≡? x) ∷_) $ replace-all-id _≡?_ ys x ⟩
                repl-cases (y ≡? x) ∷ ys
            ≡⟨ cong (λ d → repl-cases d ∷ ys) eq-d  ⟩
                repl-cases (no y≢x) ∷ ys
            ≡⟨⟩
                y ∷ ys
            ∎
    
    
replace-all-weight-<
    : {n : ℕ}
    → {v : Vec ℕ n}
    → {x' x : ℕ}
    → x ∈ v
    → x' < x
    → weight (replace-all _≟_ v x x') < weight v
replace-all-weight-< {suc n'} {x ∷ ys} {x'} {x} (here refl) x'<x = 
    begin-strict
        weight (replace-all _≟_ (x ∷ ys) x x')  
    ≡⟨⟩
        replace-if-matches x + weight (replace-all _≟_ ys x x')  
    ≡⟨⟩
        repl-cases (x ≟ x) + weight (replace-all _≟_ ys x x')  
    ≡⟨ cong (λ d → repl-cases d + weight (replace-all _≟_ ys x x'))
        (dec-yes-irr (x ≟ x) ≡-irrelevant refl)
     ⟩
        repl-cases (yes refl) + weight (replace-all _≟_ ys x x')  
    ≡⟨⟩
        x' + weight (replace-all _≟_ ys x x')  
    ≤⟨ +-monoʳ-≤ x' (rec (x ∈? ys)) ⟩
        x' + weight ys
    <⟨ +-monoˡ-< (weight ys) x'<x ⟩
        x + weight ys
    ≡⟨⟩
        weight (x ∷ ys)
    ∎
    where
        open ≤-Reasoning
        open ReplaceAllImpl _≟_ (x ∷ ys) x x'
        open ReplaceAllImpl.Cases _≟_ (x ∷ ys) x x' x 
            renaming (cases to repl-cases)
        open import Data.Vec.Membership.DecPropositional {A = ℕ} (_≟_) 
            hiding (_∈_)
        rec : (Dec (x ∈ ys)) → weight (replace-all _≟_ ys x x') ≤ weight ys
        rec (yes x∈ys) = (<⇒≤ $ replace-all-weight-< x∈ys x'<x)
        rec (no x∈ys) =
            begin 
                weight (replace-all _≟_ ys x x')
            ≡⟨ cong weight $ replace-all-not-member _≟_ ys x x' x∈ys ⟩
                 weight ys
            ≤⟨ ≤-refl ⟩
                 weight ys
            ∎
replace-all-weight-< {suc n'} {y ∷ ys} {x'} {x} (there x∈ys) x'<x =
    begin-strict
        weight (replace-all _≟_ (y ∷ ys) x x')  
    ≡⟨⟩
        replace-if-matches y + weight (replace-all _≟_ ys x x')  
    ≡⟨⟩
        u + weight (replace-all _≟_ ys x x')  
    <⟨ +-monoʳ-< u $ replace-all-weight-< {n'} {ys} {x'} {x} x∈ys x'<x ⟩
        u + weight ys
    ≤⟨ +-monoˡ-≤ (weight ys) (u≤y (y ≟ x) refl) ⟩
        y + weight ys
    ≡⟨⟩
        weight (y ∷ ys)
    ∎
    where
        open ≤-Reasoning
        open ReplaceAllImpl _≟_ (x ∷ ys) x x'
        open ReplaceAllImpl.Cases _≟_ (x ∷ ys) x x' y
        u : ℕ
        u = replace-if-matches y
        u≤y : (d : Dec (y ≡ x)) → (d ≡ (y ≟ x)) → u ≤ y
        u≤y (yes y≡x) eq = 
            begin 
                replace-if-matches y
            ≡⟨⟩
                cases (y ≟ x)
            ≡⟨ cong cases (sym eq) ⟩
                cases (yes y≡x)
            ≡⟨⟩
                x'
            ≤⟨ <⇒≤ x'<x ⟩
                x
            ≡⟨ sym y≡x ⟩
                y
            ∎
        u≤y (no y≢x) eq =
            begin 
                replace-if-matches y
            ≡⟨⟩
                cases (y ≟ x)
            ≡⟨ cong cases (sym eq) ⟩
                cases (no y≢x)
            ≡⟨⟩
                y
            ∎
    
