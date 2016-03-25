module Reduction where

open import Data.Nat
open import Data.Sum
open import Relation.Nullary using (¬_)

open import Exp

data Val : Expr → Set where
  ƛ : ∀ τ e → Val (ƛ τ e)
  Λ : ∀ e →  Val (Λ e)

val? : (e : Expr) → (Val e ⊎ ¬(Val e))
val? (bv i) = inj₂ (λ ())
val? (fv x) = inj₂ (λ ())
val? (ƛ σ e) = inj₁ (ƛ σ e)
val? (e · e₁) = inj₂ (λ ())
val? (Λ e) = inj₁ (Λ e)
val? (e ⋆ τ) = inj₂ (λ ())

infixr 2 _⟼_

data _⟼_ : Expr → Expr → Set where
  appL : ∀ {e₁ e₁' e₂}
          → e₁ ⟼ e₁'
          → e₁ · e₂ ⟼ e₁' · e₂
  app : ∀ {τ e₁ e₂}
        → (ƛ τ e₁) · e₂ ⟼ inst e₂ e₁
  appLτ : ∀ {e e' τ}
          → e ⟼ e'
          → e ⋆ τ ⟼ e' ⋆ τ
  appτ : ∀ {e τ} 
         → (Λ e) ⋆ τ ⟼ instτ τ e
