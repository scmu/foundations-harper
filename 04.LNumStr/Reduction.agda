module Reduction where

open import Data.Nat
open import Data.Sum
open import Relation.Nullary using (¬_)

open import Exp

data Val : Expr → Set where
  num : ∀ n → Val (num n)
  str : ∀ s → Val (str s)

val? : (e : Expr) → (Val e ⊎ ¬(Val e))
val? (bv i) = inj₂ (λ ())
val? (fv x) = inj₂ (λ ())
val? (num m) = inj₁ (num m)
val? (str s) = inj₁ (str s)
val? (e ∔ e₁) = inj₂ (λ ())
val? (e ^ e₁) = inj₂ (λ ())
val? (len e) = inj₂ (λ ())
val? (lett e e₁) = inj₂ (λ ())

infixr 2 _⟼_

data _⟼_ : Expr → Expr → Set where
  plusN : ∀ {m n} 
          → num m ∔ num n ⟼ num (m + n)
  plusL : ∀ {e₁ e₁' e₂}
          → e₁ ⟼ e₁'
          → e₁ ∔ e₂ ⟼ e₁' ∔ e₂
  plusR : ∀ {e₁ e₂ e₂'}
          → Val e₁
          → e₂ ⟼ e₂'
          → e₁ ∔ e₂ ⟼ e₁ ∔ e₂'
  lett : ∀ {e₁ e₂}
         → lett e₁ e₂ ⟼ inst e₁ e₂