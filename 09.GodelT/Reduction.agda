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
val? (elimℕ e₁ e₂ e) = inj₂ (λ ())
val? (ƛ σ e) = inj₁ (ƛ σ e)
val? (e · e₁) = inj₂ (λ ())

infixr 2 _⟼_

data _⟼_ : Expr → Expr → Set where
  appL : ∀ {e₁ e₁' e₂}
          → e₁ ⟼ e₁'
          → e₁ · e₂ ⟼ e₁' · e₂
  app : ∀ {τ e₁ e₂}
        → (ƛ τ e₁) · e₂ ⟼ inst e₂ e₁
  elimℕ : ∀ {e₀ e₁ e e'}
          → e ⟼ e'
          → elimℕ e₀ e₁ e ⟼ elimℕ e₀ e₁ e'
  elimℕ₀ : ∀ {e₀ e₁}
           → elimℕ e₀ e₁ zero ⟼ e₀
  elimℕ₁ : ∀ {e₀ e₁ e}
           → elimℕ e₀ e₁ (suc e) ⟼ 
              inst e ([ 1 ↦ inject (elimℕ e₀ e₁ e)] e₁)