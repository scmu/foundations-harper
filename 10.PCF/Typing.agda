module Typing where

open import Data.Nat
open import Data.String using (String) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any hiding (map)
open Data.List.Any.Membership-≡
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (¬_)

open import Assoc
open import Exp

Cxt : Set
Cxt = Assoc FName Typ

data _⊢_∶_ : Cxt → Expr → Typ → Set where
  var : ∀ {Γ x τ}
        → DomDist Γ
        → (x , τ) ∈ Γ → Γ ⊢ fv x ∶ τ
  zero : ∀ {Γ} 
        → Γ ⊢ zero ∶ nat
  suc : ∀ {Γ e}
         → Γ ⊢ e ∶ nat 
         → Γ ⊢ suc e ∶ nat
  ifz : ∀ {Γ τ e e₁ e₂}
           → Γ ⊢ e ∶ nat
           → Γ ⊢ e₁ ∶ τ
           → (L : FNames)
           → (∀ x → x ∉ L
              → ((x , nat) ∷ Γ) ⊢ instVar x e₂ ∶ τ)
           → Γ ⊢ ifz e e₁ e₂ ∶ τ
  ⇒-intro : ∀ {Γ e σ τ}
            → (L : FNames)
            → (∀ x → x ∉ L → ((x , σ) ∷ Γ) ⊢ instVar x e ∶ τ)
            → Γ ⊢ (ƛ σ e) ∶ (σ ⇒ τ)
  ⇒-elim : ∀ {Γ e₁ e₂ σ τ}
           → Γ ⊢ e₁ ∶ (σ ⇒ τ)
           → Γ ⊢ e₂ ∶ σ
           → Γ ⊢ (e₁ · e₂) ∶ τ
  μ : ∀ {Γ e τ}
      → (L : FNames)
      → (∀ x → x ∉ L → ((x , τ) ∷ Γ) ⊢ instVar x e ∶ τ)
      → Γ ⊢ μ τ e ∶ τ