module Assoc where 

open import Data.Product hiding (map)
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Membership

open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership.Propositional

Assoc : Set → Set → Set
Assoc A B = List (A × B)

dom : ∀ {A B} → Assoc A B → List A
dom = Data.List.map proj₁

data DomDist {A B : Set} : Assoc A B → Set where
  [] : DomDist []
  _∷_ : ∀ {Γ x τ} 
        → (x∉ : x ∉ dom Γ) → DomDist Γ
        → DomDist ((x , τ) ∷ Γ)

open import Data.List.Properties 
  using (map-++-commute)

assoc-rm : ∀ {A B} (Γ : Assoc A B) x Δ {τ} 
         → DomDist (Γ ++ [ x , τ ] ++ Δ) → DomDist (Γ ++ Δ)
assoc-rm [] x Δ (x∉ ∷ Δok) = Δok
assoc-rm ((y , _) ∷ Γ) x Δ {τ} (y∉ ∷ ok) 
  rewrite map-++-commute proj₁ Γ ((x , τ) ∷ Δ) 
  = safe ∷ assoc-rm Γ x Δ ok 
    where safe : y ∉ map proj₁ (Γ ++ Δ)
          safe rewrite map-++-commute proj₁ Γ Δ = 
            ∉-++-join (map proj₁ Γ) (map proj₁ Δ) 
              (∉-++-l (map proj₁ Γ) _ y∉) 
              (∉-∷-tl _ (∉-++-r (map proj₁ Γ) _ y∉))

postulate
 assoc-≠ : ∀ {A B} (Γ : Assoc A B) x Δ y {σ τ} 
           → DomDist (Γ ++ [ x , τ ] ++ Δ) → ¬ (x ≡ y)
           → (y , σ) ∈ (Γ ++ [ x , τ ] ++ Δ) 
           → (y , σ) ∈ (Γ ++ Δ)
 assoc-≡ : ∀ {A B} (Γ : Assoc A B) x Δ {σ τ} 
           → DomDist (Γ ++ [ x , τ ] ++ Δ)
           → (x , σ) ∈ (Γ ++ [ x , τ ] ++ Δ) 
           → σ ≡ τ
 DomDist-ins : ∀ {A B} (Γ : Assoc A B) x Δ {τ}
               → DomDist (Γ ++ Δ)
               → x ∉ dom (Γ ++ Δ)
               → DomDist (Γ ++ [ x , τ ] ++ Δ)
