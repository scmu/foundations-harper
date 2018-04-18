module Membership where

open import Data.Sum
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.List.Any as Any
open import Data.List.Any.Membership.Propositional

-- _∈_

∈-++-pos : ∀ {A : Set} {x : A} xs ys → x ∈ xs ++ ys
           → (x ∈ xs) ⊎ (x ∈ ys)
∈-++-pos [] ys x∈ = inj₂ x∈
∈-++-pos (x ∷ xs) ys (here refl) = inj₁ (here refl)
∈-++-pos (x ∷ xs) ys (there x∈) with ∈-++-pos xs ys x∈
... | inj₁ x∈xs = inj₁ (there x∈xs)
... | inj₂ x∈ys = inj₂ x∈ys

∈-++-r : ∀ {A : Set} {x : A} xs {ys}
           → x ∈ ys → x ∈ (xs ++ ys)
∈-++-r [] x∈ = x∈
∈-++-r (y ∷ xs) x∈ = there (∈-++-r xs x∈)

∈-++-l : ∀ {A : Set} {x : A} {xs} ys
           → x ∈ xs → x ∈ (xs ++ ys)
∈-++-l ys (here refl) = here refl
∈-++-l ys (there x∈) = there (∈-++-l ys x∈)

∈-++-weaken : ∀ {A : Set} {x : A} xs ys zs
              → x ∈ (xs ++ zs) → x ∈ (xs ++ ys ++ zs)
∈-++-weaken [] ys zs x∈ = ∈-++-r ys x∈
∈-++-weaken (x ∷ xs) ys zs (here refl) = here refl
∈-++-weaken (_ ∷ xs) ys zs (there x∈) = there (∈-++-weaken xs ys zs x∈)


-- _∉_

∉-++-l : ∀ {A : Set} {x : A} xs ys → x ∉ xs ++ ys → x ∉ xs
∉-++-l ._ ys x∉xs++ys (here eq) = x∉xs++ys (here eq)
∉-++-l .(x' ∷ xs) ys x∉xs++ys (there {x'} {xs} pxs) = 
  ∉-++-l xs ys (λ p → x∉xs++ys (there p)) pxs

∉-++-r : ∀ {A : Set} {x : A} xs ys → x ∉ xs ++ ys → x ∉ ys
∉-++-r [] ys x∉xs++ys x∈ys = x∉xs++ys x∈ys
∉-++-r (x' ∷ xs) ys x∉xs++ys x∈ys = ∉-++-r xs ys (λ p → x∉xs++ys (there p)) x∈ys

postulate
  ∉-[] : ∀ {A : Set} {y : A} → y ∉ []
  ∉-∷ : ∀ {A : Set} {y x : A} {xs}
        → ¬ (y ≡ x) → y ∉ xs → y ∉ (x ∷ xs)

∉-++-join : ∀ {A : Set} {x : A} 
            → ∀ xs ys → x ∉ xs → x ∉ ys → x ∉ xs ++ ys
∉-++-join [] ys x∉xs x∉ys x∈ys = x∉ys x∈ys
∉-++-join (_ ∷ xs) ys x∉xs x∉ys (here refl) = x∉xs (here refl)
∉-++-join (_ ∷ xs) ys x∉xxs x∉ys (there pxs) = ∉-++-join xs ys (λ x∉xs → x∉xxs (there x∉xs)) x∉ys pxs

∉-++-weaken : ∀ {A : Set} {x : A} xs ys zs
              → x ∉ (xs ++ ys ++ zs) → x ∉ (xs ++ zs)
∉-++-weaken xs ys zs x∉xyz x∈xz = x∉xyz (∈-++-weaken xs ys zs x∈xz)

∉-∷-hd : ∀ {A : Set} {x y : A} xs → x ∉ (y ∷ xs) → ¬ (x ≡ y)
∉-∷-hd {x} {._} xs x∉ refl = x∉ (here refl)

∉-∷-tl : ∀ {A : Set} {x y : A} xs → x ∉ (y ∷ xs) → x ∉ xs
∉-∷-tl {x} {y} xs x∉ x∈ = x∉ (there x∈)

≠-sym : ∀ {A : Set} {x y : A} → ¬ (x ≡ y) → ¬ (y ≡ x)
≠-sym x≠y refl = x≠y refl
