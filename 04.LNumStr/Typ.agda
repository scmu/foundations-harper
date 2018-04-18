module Typ where

open import Data.Nat
open import Data.String using (String) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any hiding (map)
open import Data.List.Any.Membership.Propositional

open import Assoc
open import Exp

data Typ : Set where
  num : Typ
  str : Typ

Cxt : Set
Cxt = Assoc FName Typ

data _⊢_∶_ : Cxt → Expr → Typ → Set where
  var : ∀ {Γ x τ}
        → DomDist Γ
        → (x , τ) ∈ Γ → Γ ⊢ fv x ∶ τ
  num : ∀ {Γ} m
        → Γ ⊢ num m ∶ num
--  str : ∀ {Γ} s →
--        Γ ⊢ str s ∶ str
  plus : ∀ {Γ e₁ e₂}
         → Γ ⊢ e₁ ∶ num → Γ ⊢ e₂ ∶ num
         → Γ ⊢ e₁ ∔ e₂ ∶ num
--  cat : ∀ {Γ e₁ e₂} →
--         Γ ⊢ e₁ ∶ str → Γ ⊢ e₂ ∶ str →
--         Γ ⊢ e₁ ^ e₂ ∶ str
--  len : ∀ {n} {Γ : Cxt n} {e} →
--         Γ ⊢ e ∶ str →
--         Γ ⊢ len e ∶ num
  lett : ∀ {Γ e₁ e₂ τ₁ τ₂}
         → Γ ⊢ e₁ ∶ τ₁ 
         → (L : FNames)
         → (∀ x → x ∉ L → ((x , τ₁) ∷ Γ) ⊢ instVar x e₂ ∶ τ₂)
         → Γ ⊢ lett e₁ e₂ ∶ τ₂
