module TypeSafety where

open import Data.Empty using (⊥-elim)
open import Data.String using (String) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List
open import Membership
open import Data.List.Any hiding (map)
open Data.List.Any.Membership-≡
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (¬_; yes; no)

open import Exp
open import Typ
open import Assoc
open import Infrastructure

⊢-weaken : ∀ Γ x τ Δ {e σ} 
           → x ∉ dom (Γ ++ Δ)
           → (Γ ++ Δ) ⊢ e ∶ σ
           → (Γ ++ [(x , τ)] ++ Δ) ⊢ e ∶ σ
⊢-weaken Γ x τ Δ x∉ (var D y) = 
  var (DomDist-ins Γ x Δ D x∉) (∈-++-weaken Γ [ x , τ ] Δ y)
⊢-weaken Γ x τ Δ x∉ (num m) = num m
⊢-weaken Γ x τ Δ x∉ (plus t₁ t₂) =
  plus (⊢-weaken Γ x τ Δ  x∉ t₁) (⊢-weaken Γ x τ Δ x∉ t₂)
⊢-weaken Γ x τ Δ {σ = σ} x∉ (lett {e₂ = e₂} {τ₁ = τ₁} t₁ L t₂) =
    lett (⊢-weaken Γ x τ Δ x∉ t₁) (x ∷ L) fn
  where fn : ∀ y → y ∉ x ∷ L
              → ((y , τ₁) ∷ Γ ++ [ x , τ ] ++ Δ) ⊢ instVar y e₂ ∶ σ
        fn y y∉ = ⊢-weaken ((y , τ₁) ∷ Γ) x τ Δ x∉' 
                           (t₂ y (∉-∷-tl L y∉))
           where x∉' : x ∉ dom ((y , τ₁) ∷ Γ ++ Δ)
                 x∉' = ∉-∷ (≠-sym (∉-∷-hd L y∉)) x∉
                   where ≠-sym : ∀ {A : Set} {x y : A} → ¬ (x ≡ y) → ¬ (y ≡ x)
                         ≠-sym x≠y refl = x≠y refl

⊢-subst : ∀ Γ x τ Δ {e t σ} 
          → (Γ ++ [(x , τ)] ++ Δ) ⊢ e ∶ σ
          → (Γ ++ Δ) ⊢ t ∶ τ
          → (Γ ++ Δ) ⊢ [ x ↝ t ] e ∶ σ
⊢-subst Γ x τ Δ (var {x = y} D y∈) t₂ with x ≟S y 
... | yes x≡y rewrite x≡y
              | assoc-≡ Γ y Δ D y∈ = t₂
... | no  x≠y = var (assoc-rm Γ x Δ D) (assoc-≠ Γ x Δ y D x≠y y∈)
⊢-subst Γ x τ Δ (num m) t₂ = num m
⊢-subst Γ x τ Δ (plus t₁ t₂) t₃ = 
  plus (⊢-subst Γ x τ Δ t₁ t₃) (⊢-subst Γ x τ Δ t₂ t₃)
⊢-subst Γ x τ Δ  {._} {t} {σ}
        (lett {._} {e₁} {e₂} {τ₁} {.σ} t₁ L f) t₂ = 
  lett (⊢-subst Γ x τ Δ t₁ t₂) (x ∷ dom (Γ ++ Δ) ++ L) fn
 where fn : ∀ y → y ∉ (x  ∷ dom (Γ ++ Δ) ++ L)
            → ((y , τ₁) ∷ Γ ++ Δ) ⊢ instVar y ([ x ↝ inject t ] e₂) ∶ σ
       fn y y∉ with let y∉L = ∉-++-r (dom (Γ ++ Δ)) L (∉-∷-tl _ y∉)
                        y∉ΓΔ = ∉-++-l (dom (Γ ++ Δ)) L (∉-∷-tl _ y∉)
                    in ⊢-subst ((y , τ₁) ∷ Γ) x τ Δ
                         {instVar y e₂} {t} {σ}
                         (f y y∉L) 
                         (⊢-weaken [] y τ₁ (Γ ++ Δ) y∉ΓΔ t₂)
       ...     | ⊢e rewrite subst-openVar x t y e₂ (∉-∷-hd _ y∉) = ⊢e
         
open import Data.Nat using (_+_)
open import FVars
open import Reduction

preservation : ∀ {e e' : Expr} {τ}
               → [] ⊢ e ∶ τ 
               → e ⟼ e'
               → [] ⊢ e' ∶ τ
preservation (plus _ _) plusN = num _
preservation (plus ⊢e₁ ⊢e₂) (plusL e₁⟼e₁') =
   plus (preservation ⊢e₁ e₁⟼e₁') ⊢e₂
preservation (plus ⊢e₁ ⊢e₂) (plusR x e₂⟼e₂') = 
   plus ⊢e₁ (preservation ⊢e₂ e₂⟼e₂')
preservation (lett {._} {e₁} {e₂} {τ₁} {τ₂} ⊢e₁ L fn) lett with freshgen-1 (fvars e₂ ++ L)
... | (y , y∉) = body
 where y⊢e₂ : ((y , τ₁) ∷ []) ⊢ instVar y e₂ ∶ τ₂
       y⊢e₂ = fn y (∉-++-r (fvars e₂) _ y∉)
                     
       ⊢e₂ : [] ⊢ [ y ↝ e₁ ] (instVar y e₂) ∶ τ₂
       ⊢e₂ = ⊢-subst [] y τ₁ [] y⊢e₂ ⊢e₁

       body : [] ⊢ inst e₁ e₂ ∶ τ₂
       body with subst-intro y e₁ e₂ (∉-++-l (fvars e₂) _ y∉)
       ...  | eq = subst (λ u → [] ⊢ u ∶ τ₂) (sym eq) ⊢e₂

progress : ∀ {e : Expr} {τ}
           → [] ⊢ e ∶ τ 
           → ¬ (Val e)
           → ∃ (λ e' → e ⟼ e')
progress {fv x} (var x₁ ()) _
progress (num m) ¬Val = ⊥-elim (¬Val (num m))
progress {e₁ ∔ e₂} (plus ⊢e₁ ⊢e₂) _ with val? e₁ 
progress {._ ∔ e₂} (plus ⊢e₁ ⊢e₂) _ | inj₁ (num m) with val? e₂ 
progress {._ ∔ ._} (plus ⊢e₁ ⊢e₂) _ | inj₁ (num m) | inj₁ (num n) = num (m + n) , plusN 
progress {._ ∔ ._} (plus ⊢e₁ ()) _ | inj₁ (num m) | inj₁ (str s) 
progress {._ ∔ e₂} (plus ⊢e₁ ⊢e₂) _ | inj₁ (num m) | inj₂ ¬Val 
     with progress ⊢e₂ ¬Val
...     | (e₂' , e₂⟼e₂') = num m ∔ e₂' , plusR (num m) e₂⟼e₂' 
progress {._ ∔ e₂} (plus () ⊢e₂) _ | inj₁ (str s)
progress {e₁ ∔ e₂} (plus ⊢e₁ ⊢e₂) _ | inj₂ ¬Val with progress ⊢e₁ ¬Val 
...           | (e₁' , e₁⟼e₁') = e₁' ∔ e₂ , plusL e₁⟼e₁'
progress {lett e₁ e₂} (lett ⊢e₁ L f) ¬Val = inst e₁ e₂ , lett