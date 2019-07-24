module Assoc where 

open import Data.Product hiding (map)
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Membership

open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any

private
  variable
    A : Set
    x  y  : A
    xs ys : List A 
    
data Distct {A : Set} : List A → Set where
  [] : Distct []
  _∷_ : ∀ {x xs} → x ∉ xs → Distct xs → Distct (x ∷ xs)

Distct-rm : ∀ (xs : List A) z ys
           → Distct (xs ++ [ z ] ++ ys) → Distct (xs ++ ys)
Distct-rm [] z _ (_ ∷ ys) = ys
Distct-rm (x ∷ xs) z ys (x∉ ∷ xszys) = 
  ∉-++-weaken xs [ z ] ys x∉ ∷ Distct-rm xs z ys xszys

Distct-ins : ∀ (xs : List A) z ys
             → Distct (xs ++ ys)
             → z ∉ (xs ++ ys)
             → Distct (xs ++ [ z ] ++ ys)
Distct-ins [] z ys Dys z∉ = z∉ ∷ Dys
Distct-ins (x ∷ xs) z ys (x∉ ∷ Dxsys) z∉ = 
  ∉-++-ins xs z ys x∉ (≠-sym (∉-∷-hd z∉)) ∷
    Distct-ins xs z ys Dxsys (∉-∷-tl z∉)

Assoc : Set → Set → Set
Assoc A B = List (A × B)

dom : ∀ {A B} → Assoc A B → List A
dom = Data.List.map proj₁

DomDist : ∀ {A B} → Assoc A B → Set
DomDist xs = Distct (Data.List.map proj₁ xs)

{-
data DomDist {A B : Set} : Assoc A B → Set where
  [] : DomDist []
  _∷_ : ∀ {Γ x τ} 
        → (x∉ : x ∉ dom Γ) → DomDist Γ
        → DomDist ((x , τ) ∷ Γ)
-}

open import Data.List.Properties 
  using (map-++-commute)

postulate
 assoc-rm : ∀ {A B} (Γ : Assoc A B) x Δ {τ} 
            → DomDist (Γ ++ [ x , τ ] ++ Δ) → DomDist (Γ ++ Δ)

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
