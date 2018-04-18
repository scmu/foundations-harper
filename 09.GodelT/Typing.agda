module Typing where

open import Data.Nat
open import Data.String using (String) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any hiding (map)
open import Data.List.Any.Membership.Propositional
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
  ℕ-elim : ∀ {Γ τ e₁ e₂ e}
           → Γ ⊢ e₁ ∶ τ
           → (L : FNames)
           → (∀ x y → ¬ (x ≡ y) →  x ∉ L → y ∉ L 
              → ((x , nat) ∷ (y , τ) ∷ Γ) ⊢ instVar x ([ 1 ↦ fv y ] e₂) ∶ τ)
           → Γ ⊢ e ∶ nat
           → Γ ⊢ elimℕ e₁ e₂ e ∶ τ
  ⇒-intro : ∀ {Γ e σ τ}
            → (L : FNames)
            → (∀ x → x ∉ L → ((x , σ) ∷ Γ) ⊢ instVar x e ∶ τ)
            → Γ ⊢ (ƛ σ e) ∶ (σ ⇒ τ)
  ⇒-elim : ∀ {Γ e₁ e₂ σ τ}
           → Γ ⊢ e₁ ∶ (σ ⇒ τ)
           → Γ ⊢ e₂ ∶ σ
           → Γ ⊢ (e₁ · e₂) ∶ τ
