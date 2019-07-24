module FVars where

open import Data.Product 
open import Data.Nat
open import Data.List

open import Exp

open import Membership public

open import Data.List.Membership.Propositional

{-
∉-·-l : ∀ {x} e₁ e₂ → x ∉ fvars (e₁ · e₂) → x ∉ fvars e₁
∉-·-l e₁ e₂ = ∉-++-l (fvars e₁) (fvars e₂)

∉-·-r : ∀ {x} e₁ e₂ → x ∉ fvars (e₁ · e₂) → x ∉ fvars e₂
∉-·-r e₁ e₂ = ∉-++-r (fvars e₁) (fvars e₂)
-}

postulate fresh-gen : FNames → FName
postulate fresh-gen-spec : ∀ L → fresh-gen L ∉ L

freshgen-1 : (L : FNames) → ∃ (λ x → x ∉ L)
freshgen-1 L = fresh-gen L , fresh-gen-spec L

freshgen-2 : (L₁ L₂ : FNames) 
             → ∃ (λ x → x ∉ L₁ × x ∉ L₂)
freshgen-2 L₁ L₂ = x , x∉L₁ , x∉L₂
 where L = L₁ ++ L₂
       x = fresh-gen L
       x∉ : x ∉ L
       x∉ = fresh-gen-spec L
       x∉L₁ : x ∉ L₁
       x∉L₁ = (∉-++-l L₁ x∉)
       x∉L₂ : x ∉ L₂
       x∉L₂ = (∉-++-r L₁ x∉)

freshgen-3 : (L₁ L₂ L₃ : FNames) 
             → ∃ (λ x → x ∉ L₁ × x ∉ L₂ × x ∉ L₃)
freshgen-3 L₁ L₂ L₃ = x , x∉L₁ , x∉L₂ , x∉L₃
 where L = L₁ ++ L₂ ++ L₃
       x = fresh-gen L
       x∉ : x ∉ L
       x∉ = fresh-gen-spec L
       x∉L₁ : x ∉ L₁
       x∉L₁ = (∉-++-l L₁ x∉)
       x∉L₂ : x ∉ L₂
       x∉L₂ = (∉-++-l L₂ (∉-++-r L₁ x∉))
       x∉L₃ : x ∉ L₃
       x∉L₃ = (∉-++-r L₂ (∉-++-r L₁ x∉))

freshgen-4 : (L₁ L₂ L₃ L₄ : FNames) 
             → ∃ (λ x → x ∉ L₁ × x ∉ L₂ × x ∉ L₃ × x ∉ L₄)
freshgen-4 L₁ L₂ L₃ L₄ = x , x∉L₁ , x∉L₂ , x∉L₃ , x∉L₄
 where L = L₁ ++ L₂ ++ L₃ ++ L₄
       x = fresh-gen L
       x∉ : x ∉ L
       x∉ = fresh-gen-spec L
       x∉L₁ : x ∉ L₁
       x∉L₁ = (∉-++-l L₁ x∉)
       x∉L₂ : x ∉ L₂
       x∉L₂ = (∉-++-l L₂ (∉-++-r L₁ x∉))
       x∉L₃ : x ∉ L₃
       x∉L₃ = (∉-++-l L₃ (∉-++-r L₂ (∉-++-r L₁ x∉)))
       x∉L₄ : x ∉ L₄
       x∉L₄ = (∉-++-r L₃ (∉-++-r L₂ (∉-++-r L₁ x∉)))

postulate
 freshgen-5 : (L₁ L₂ L₃ L₄ L₅ : FNames) 
             → ∃ (λ x → x ∉ L₁ × x ∉ L₂ × x ∉ L₃ × x ∉ L₄ × x ∉ L₅)
