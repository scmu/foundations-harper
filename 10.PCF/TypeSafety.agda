module TypeSafety where

open import Data.Empty using (⊥-elim)
open import Data.String using (String) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List
open import Membership
-- open import Data.List.Any hiding (map)
open import Data.List.Any.Membership.Propositional
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (¬_; yes; no)

open import Exp
open import Typing
open import Assoc
open import Infrastructure

mutual
 ⊢-weaken : ∀ Γ x τ Δ {e σ} 
            → x ∉ dom (Γ ++ Δ)
            → (Γ ++ Δ) ⊢ e ∶ σ
            → (Γ ++ [(x , τ)] ++ Δ) ⊢ e ∶ σ
 ⊢-weaken Γ x τ Δ x∉ (var D y) = 
   var (DomDist-ins Γ x Δ D x∉) (∈-++-weaken Γ [ x , τ ] Δ y)
 ⊢-weaken Γ x τ Δ x∉ zero = zero
 ⊢-weaken Γ x τ Δ x∉ (suc t) =
   suc (⊢-weaken Γ x τ Δ x∉ t)
 ⊢-weaken Γ x τ Δ {σ = σ} x∉ (ifz {e = e}{e₀}{e₁} t t₀ L t₁) = 
   ifz (⊢-weaken Γ x τ Δ x∉ t) 
       (⊢-weaken Γ x τ Δ x∉ t₀) 
       (x ∷ L) 
       (⊢-weaken→ nat Γ x τ Δ x∉ e₁ t₁)
 ⊢-weaken Γ x τ Δ x∉ (⇒-intro {._} {e} {σ} {υ} L fn) =
   ⇒-intro (x ∷ L) (⊢-weaken→ σ Γ x τ Δ x∉ e fn)
 ⊢-weaken Γ x τ Δ x∉ (⇒-elim t₁ t₂) = 
   ⇒-elim (⊢-weaken Γ x τ Δ x∉ t₁) (⊢-weaken Γ x τ Δ x∉ t₂)
 ⊢-weaken Γ x τ Δ x∉ (μ {._}{e}{σ} L f) =
   μ (x ∷ L) (⊢-weaken→ σ Γ x τ Δ x∉ e f)

 private
  ⊢-weaken→ : ∀ σ Γ x τ Δ 
              → x ∉ dom (Γ ++ Δ) → 
              ∀ e {L ρ}
              → (∀ y → y ∉ L → ((y , σ) ∷ Γ ++ Δ) ⊢ instVar y e ∶ ρ)
              → ∀ y → y ∉ x ∷ L →  ((y , σ) ∷ Γ ++ [ x , τ ] ++ Δ) ⊢ instVar y e ∶ ρ
  ⊢-weaken→ σ Γ x τ Δ x∉ e {L} {ρ} ⊢e→ y y∉ =
    ⊢-weaken ((y , σ) ∷ Γ) x τ Δ x∉' (⊢e→ y (∉-∷-tl L y∉))
   where x∉' : x ∉ dom ((y , σ) ∷ Γ ++ Δ)
         x∉' = ∉-∷ (≠-sym (∉-∷-hd L y∉)) x∉

mutual 

 ⊢-subst : ∀ Γ x τ Δ {e t σ} 
          → (Γ ++ [(x , τ)] ++ Δ) ⊢ e ∶ σ
          → (Γ ++ Δ) ⊢ t ∶ τ
          → (Γ ++ Δ) ⊢ [ x ↝ t ] e ∶ σ
 ⊢-subst Γ x τ Δ (var {x = y} D y∈) t₂ with x ≟S y 
 ... | yes x≡y rewrite x≡y
              | assoc-≡ Γ y Δ D y∈ = t₂
 ... | no  x≠y = var (assoc-rm Γ x Δ D) (assoc-≠ Γ x Δ y D x≠y y∈)
 ⊢-subst Γ x τ Δ zero t₂ = zero
 ⊢-subst Γ x τ Δ (suc t₁) t₂ = 
   suc (⊢-subst Γ x τ Δ t₁ t₂)
 ⊢-subst Γ x τ Δ  {._} {u} {σ}
        (ifz {e = e}{e₀}{e₁} t t₀ L t₁) t₂ = 
  ifz (⊢-subst Γ x τ Δ t t₂) 
      (⊢-subst Γ x τ Δ t₀ t₂)
      (x ∷ dom (Γ ++ Δ) ++ L) 
      (⊢-subst→ nat Γ x τ Δ e₁ t₁ t₂)
 ⊢-subst Γ x τ Δ {._} {t} (⇒-intro {._} {e} {σ} {υ} L fn) t₃ = 
  ⇒-intro (x ∷ dom (Γ ++ Δ) ++ L)
          (⊢-subst→ σ Γ x τ Δ e fn t₃)
 ⊢-subst Γ x τ Δ (⇒-elim t₁ t₂) t₃ = 
  ⇒-elim (⊢-subst Γ x τ Δ t₁ t₃) (⊢-subst Γ x τ Δ t₂ t₃)
 ⊢-subst Γ x τ Δ {._} {t} (μ {._} {e} {σ} L f) t₃ = 
   μ (x ∷ dom (Γ ++ Δ) ++ L)
     (⊢-subst→ σ Γ x τ Δ e f t₃)

 private
  ⊢-subst→ : ∀ ρ Γ x τ Δ e {u σ L}
             → (∀ y → y ∉ L → ((y , ρ) ∷ Γ ++ (x , τ) ∷ Δ) ⊢ instVar y e ∶ σ)
             → (Γ ++ Δ) ⊢ u ∶ τ
             → ∀ y → y ∉ x ∷ dom (Γ ++ Δ) ++ L →
                 ((y , ρ) ∷ Γ ++ Δ) ⊢ instVar y ([ x ↝ inject u ] e) ∶ σ
  ⊢-subst→ ρ Γ x τ Δ e {u}{_}{L} ⊢e→ ⊢u y y∉ 
   with let y∉L : y ∉ L
            y∉L = ∉-++-r (dom (Γ ++ Δ)) L (∉-∷-tl _ y∉)
               
            y∉ΓΔ : y ∉ dom (Γ ++ Δ)
            y∉ΓΔ = ∉-++-l (dom (Γ ++ Δ)) L (∉-∷-tl _ y∉)
        in ⊢-subst ((y , ρ) ∷ Γ) x τ Δ (⊢e→ y y∉L)
                   (⊢-weaken [] y ρ (Γ ++ Δ) y∉ΓΔ ⊢u)
  ... | y⊢xye rewrite subst-openVar x u y e (∉-∷-hd _ y∉) = y⊢xye

open import FVars

⊢-substλ : ∀ Γ e₁ {τ} e₂ {σ} {L}
           → (∀ x → x ∉ L → ((x , σ) ∷ Γ) ⊢ instVar x e₁ ∶ τ)
           → Γ ⊢ e₂ ∶ σ
           → Γ ⊢ inst e₂ e₁ ∶ τ
⊢-substλ Γ e₁ {τ} e₂ {σ} {L} →⊢e₁ ⊢e₂ with freshgen-2 (fvars e₁) L
... | (x , x∉e₁ , x∉L) = body 
  where x⊢e₁ : ((x , σ) ∷ Γ) ⊢ instVar x e₁ ∶ τ
        x⊢e₁ = →⊢e₁ x x∉L

        ⊢xe₂e₁ : Γ ⊢ [ x ↝ e₂ ] (instVar x e₁) ∶ τ
        ⊢xe₂e₁ = ⊢-subst [] x σ Γ x⊢e₁ ⊢e₂

        body : Γ ⊢ inst e₂ e₁ ∶ τ
        body with subst-intro x e₂ e₁ x∉e₁
        ...  | eq = subst (λ u → Γ ⊢ u ∶ τ) (sym eq) ⊢xe₂e₁

-----------

open import Data.Nat using (_+_)
open import Reduction

preservation : ∀ {e e' : Expr} {τ}
               → [] ⊢ e ∶ τ 
               → e ⟼ e'
               → [] ⊢ e' ∶ τ
preservation t (appL e₁⟼e₁') with t
... | (⇒-elim ⊢e₁ ⊢e₂) =
  ⇒-elim (preservation ⊢e₁ e₁⟼e₁') ⊢e₂
preservation {(ƛ .σ .e₁) · .e₂} 
   (⇒-elim {τ = τ} (⇒-intro L →⊢e₁) ⊢e₂) (app {σ} {e₁} {e₂}) 
  = ⊢-substλ [] e₁ e₂ →⊢e₁ ⊢e₂
preservation {ifz .e .e₀ .e₁} (ifz ⊢e ⊢e₀ L ⊢e₁) (ifz {e}{e'}{e₀}{e₁} e⟼e') = 
  ifz (preservation ⊢e e⟼e') ⊢e₀ L ⊢e₁
preservation {ifz zero .e₀ .e₁} (ifz ⊢e ⊢e₀ L _) (ifz₀ {e₀}{e₁}) = ⊢e₀
preservation {ifz (suc .e) .e₀ .e₁} 
   (ifz {._}{τ} (suc ⊢e) ⊢e₀ L →⊢e₁) (ifz₁ {e}{e₀}{e₁})
  = ⊢-substλ [] e₁ e →⊢e₁ ⊢e 
preservation {μ .τ .e} (μ L →⊢e) (μ {τ}{e}) =
    ⊢-substλ [] e (μ τ e) →⊢e (μ L →⊢e)

progress : ∀ {e : Expr} {τ}
           → [] ⊢ e ∶ τ 
           → ¬ (Val e)
           → ∃ (λ e' → e ⟼ e')
progress (var _ ()) _
progress zero ¬Val = ⊥-elim (¬Val zero)
progress (suc _) ¬Val = ⊥-elim (¬Val (suc _))
progress {ifz e e₀ e₁}(ifz ⊢e ⊢e₀ L ⊢e₁) _ with val? e
progress {ifz .zero e₀ e₁}(ifz ⊢e ⊢e₀ L ⊢e₁) _ | inj₁ zero = e₀ , ifz₀
progress {ifz (suc e) e₀ e₁}(ifz ⊢e ⊢e₀ L ⊢e₁) _ | inj₁ (suc ._) = 
  inst e e₁ , ifz₁
progress {ifz ._ e₀ e₁}(ifz () ⊢e₀ L ⊢e₁) _ | inj₁ (ƛ _ _) 
progress {ifz e e₀ e₁}(ifz ⊢e ⊢e₀ L ⊢e₁) _ | inj₂ ¬V 
  with progress ⊢e ¬V
... | (e' , e⟼e') = ifz e' e₀ e₁ , ifz e⟼e'
progress {ƛ σ e} (⇒-intro L x) ¬Val = ⊥-elim (¬Val (ƛ σ e))
progress {e₁ · e₂} (⇒-elim ⊢e₁ ⊢e₂) _ with val? e₁
progress {._ · e₂} (⇒-elim () ⊢e₂) _ | inj₁ zero 
progress {._ · e₂} (⇒-elim () ⊢e₂) _ | inj₁ (suc _)
progress {._ · e₂} (⇒-elim ⊢e₁ ⊢e₂) _ | inj₁ (ƛ τ e) = inst e₂ e , app
progress {e₁ · e₂} (⇒-elim ⊢e₁ ⊢e₂) _ | inj₂ ¬Val 
    with progress ⊢e₁ ¬Val 
... | (e₁' , e₁⟼e₁') = e₁' · e₂ , appL e₁⟼e₁' 
progress {μ .τ .e} (μ {._} {e} {τ} L ⊢e) _ = inst (μ τ e) e , μ
