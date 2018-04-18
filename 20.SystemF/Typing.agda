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
Cxt = Assoc FName (Typ 0)

Cxt₁ : Set
Cxt₁ = List FName

data _⊢₁_ : Cxt₁ → Typ 0 → Set where
  var : ∀ {Δ x}
        → Distct Δ
        → x ∈ Δ → Δ ⊢₁ fv x
  _⇒_ : ∀ {Δ σ τ}
        → Δ ⊢₁ σ → Δ ⊢₁ τ
        → Δ ⊢₁ (σ ⇒ τ)
  Ȧ : ∀ {Δ τ}
      → (L : FNames)
      → (∀ x → x ∉ L → (x ∷ Δ) ⊢₁ instVar₁ x τ)
      → Δ ⊢₁ Ȧ τ 

data _,_⊢_∶_ : Cxt₁ → Cxt → Expr → Typ 0 → Set where
  var : ∀ {Θ Γ x τ}
        → DomDist Γ
        → (x , τ) ∈ Γ → Θ , Γ ⊢ fv x ∶ τ
  ⇒-intro : ∀ {Θ Γ e σ τ}
            → Θ ⊢₁ σ
            → (L : FNames)
            → (∀ x → x ∉ L → Θ , ((x , σ) ∷ Γ) ⊢ instVar x e ∶ τ)
            → Θ , Γ ⊢ (ƛ σ e) ∶ (σ ⇒ τ)
  ⇒-elim : ∀ {Θ Γ e₁ e₂ σ τ}
           → Θ , Γ ⊢ e₁ ∶ (σ ⇒ τ)
           → Θ , Γ ⊢ e₂ ∶ σ
           → Θ , Γ ⊢ (e₁ · e₂) ∶ τ
  Ȧ-intro : ∀ {Θ Γ e τ} 
            → (L : FNames)
            → (∀ x → x ∉ L → (x ∷ Θ) , Γ ⊢ instVarτ x e ∶ instVar₁ x τ)  
            → Θ , Γ ⊢ Λ e ∶ Ȧ τ 
  Ȧ-elim : ∀ {Θ Γ e σ τ}
           → Θ , Γ ⊢ e ∶ Ȧ σ
           → Θ ⊢₁ τ
           → Θ , Γ ⊢ e ⋆ τ ∶ inst₁ τ σ 

substCxt₁ : FName → Typ 0 → Cxt → Cxt 
substCxt₁ x τ = map (λ yσ → (proj₁ yσ , [ x ↝ τ ]₁ (proj₂ yσ)))

postulate 
 substCxt₁Distct : ∀ {Γ} x τ
                  → DomDist Γ
                  → DomDist (substCxt₁ x τ Γ)

postulate
 substCxt₁-∈ : ∀ {Γ} x σ y τ
               → (x , σ) ∈ Γ
               → (x , [ y ↝ τ ]₁ σ) ∈ substCxt₁ y τ Γ 
