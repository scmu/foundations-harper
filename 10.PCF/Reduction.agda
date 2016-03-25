module Reduction where

open import Data.Nat
open import Data.Sum
open import Relation.Nullary using (¬_)

open import Exp

data Val : Expr → Set where
  zero : Val zero
  suc : ∀ e → Val (suc e)  -- lazy
  ƛ   : ∀ τ e → Val (ƛ τ e)

val? : (e : Expr) → (Val e ⊎ ¬(Val e))
val? (bv i) = inj₂ (λ ())
val? (fv x) = inj₂ (λ ())
val? zero = inj₁ zero
val? (suc e) = inj₁ (suc e)
val? (ifz e e₀ e₁) = inj₂ (λ ())
val? (ƛ σ e) = inj₁ (ƛ σ e)
val? (e · e₁) = inj₂ (λ ())
val? (μ σ e) = inj₂ (λ ())

infixr 2 _⟼_

data _⟼_ : Expr → Expr → Set where
  appL : ∀ {e₁ e₁' e₂}
          → e₁ ⟼ e₁'
          → e₁ · e₂ ⟼ e₁' · e₂
  app : ∀ {τ e₁ e₂}
        → (ƛ τ e₁) · e₂ ⟼ inst e₂ e₁
  ifz : ∀ {e e' e₀ e₁}
        → e ⟼ e'
        → ifz e e₀ e₁ ⟼ ifz e' e₀ e₁
  ifz₀ : ∀ {e₀ e₁}
        → ifz zero e₀ e₁ ⟼ e₀
  ifz₁ : ∀ {e e₀ e₁}
        → ifz (suc e) e₀ e₁ ⟼ inst e e₁
  μ : ∀ {τ e}
      → μ τ e ⟼ inst (μ τ e) e