module TypeSafety where

open import Data.Empty using (⊥-elim)
open import Data.String using (String) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List
open import Membership
open import Data.List.Any hiding (map)
open import Data.List.Any.Membership.Propositional
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (¬_; yes; no)

open import Exp
open import Typing
open import Assoc
open import Infrastructure

⊢₁-weaken : ∀ Θ x Φ {σ} 
            → x ∉ (Θ ++ Φ)
            → (Θ ++ Φ) ⊢₁ σ
            → (Θ ++ [ x ] ++ Φ) ⊢₁ σ
⊢₁-weaken Θ x Φ x∉ (var D y∈) = 
   var (Distct-ins Θ x Φ D x∉) (∈-++-weaken Θ [ x ] Φ y∈)
⊢₁-weaken Θ x Φ x∉ (⊢₁σ ⇒ ⊢₁τ) = 
  ⊢₁-weaken Θ x Φ x∉ ⊢₁σ ⇒ ⊢₁-weaken Θ x Φ x∉ ⊢₁τ
⊢₁-weaken Θ x Φ x∉ (Ȧ {._}{σ} L ⊢₁σ→) =
   Ȧ (x ∷ L) ⊢₁-weaken→
 where
  ⊢₁-weaken→ : ∀ y → y ∉ x ∷ L →  (y ∷ Θ ++ [ x ] ++ Φ) ⊢₁ instVar₁ y σ
  ⊢₁-weaken→  y y∉ = 
    ⊢₁-weaken (y ∷ Θ) x Φ x∉' (⊢₁σ→ y (∉-∷-tl y∉))
   where x∉' : x ∉ (y ∷ Θ ++ Φ)
         x∉' = ∉-∷ (≠-sym (∉-∷-hd y∉)) x∉

⊢-weakenτ : ∀ Θ x Φ Γ {e σ} 
             → x ∉ (Θ ++ Φ)
             → (Θ ++ Φ) , Γ ⊢ e ∶ σ
             → (Θ ++ [ x ] ++ Φ) , Γ ⊢ e ∶ σ
⊢-weakenτ Θ x Φ Γ x∉ (var D y∈) = var D y∈
⊢-weakenτ Θ x Φ Γ x∉ (⇒-intro {e = e}{σ}{τ} ⊢₁σ L y⊢ey→) = 
  ⇒-intro (⊢₁-weaken Θ x Φ x∉ ⊢₁σ) L xy⊢ey→
 where xy⊢ey→ : ∀ y → y ∉ L 
                → (Θ ++ x ∷ Φ) , (y , σ) ∷ Γ ⊢ instVar y e ∶ τ
       xy⊢ey→ y y∉ = ⊢-weakenτ Θ x Φ ((y , σ) ∷ Γ) x∉ (y⊢ey→ y y∉)
⊢-weakenτ Θ x Φ Γ x∉ (⇒-elim ⊢e₁ ⊢e₂) = 
  ⇒-elim (⊢-weakenτ Θ x Φ Γ x∉ ⊢e₁)
         (⊢-weakenτ Θ x Φ Γ x∉ ⊢e₂)
⊢-weakenτ Θ x Φ Γ x∉ (Ȧ-intro {e = e}{τ} L y⊢ey→) = 
  Ȧ-intro (x ∷ L) yx⊢ey→
 where yx⊢ey→ : ∀ y → y ∉ x ∷ L 
                → (y ∷ Θ ++ [ x ] ++ Φ) , Γ ⊢ instVarτ y e ∶ instVar₁ y τ
       yx⊢ey→ y y∉ with ∉-uncons x L y∉ 
       ... | (y≠x , y∉L) = ⊢-weakenτ (y ∷ Θ) x Φ Γ 
                             (∉-∷ (≠-sym y≠x) x∉) (y⊢ey→ y y∉L)
⊢-weakenτ Θ x Φ Γ x∉ (Ȧ-elim ⊢e ⊢τ) = 
 Ȧ-elim (⊢-weakenτ Θ x Φ Γ x∉ ⊢e) 
        (⊢₁-weaken Θ x Φ x∉ ⊢τ)

⊢-weaken : ∀ Θ Γ x τ Δ {e σ} 
           → x ∉ dom (Γ ++ Δ)
           → Θ , (Γ ++ Δ) ⊢ e ∶ σ
           → Θ , (Γ ++ [(x , τ)] ++ Δ) ⊢ e ∶ σ
⊢-weaken Θ Γ x τ Δ x∉ (var D y∈) = 
  var (DomDist-ins Γ x Δ D x∉) 
       (∈-++-weaken Γ [(x , _)] Δ y∈)
⊢-weaken Θ Γ x τ Δ x∉ (⇒-intro {e = e}{σ}{γ} ⊢σ L y⊢ey→) = 
  ⇒-intro ⊢σ (x ∷ L) xy⊢ey→
 where xy⊢ey→ : ∀ y → y ∉ x ∷ L
                → Θ , (y , σ) ∷ Γ ++ [ x , τ ] ++ Δ ⊢ instVar y e ∶ γ
       xy⊢ey→ y y∉ with ∉-uncons x L y∉
       ... | (y≠x , y∉L) = ⊢-weaken Θ ((y , σ) ∷ Γ) x τ Δ 
                             (∉-∷ (≠-sym y≠x) x∉) 
                             (y⊢ey→ y y∉L)
⊢-weaken Θ Γ x τ Δ x∉ (⇒-elim ⊢e₁ ⊢e₂) = 
  ⇒-elim (⊢-weaken Θ Γ x τ Δ x∉ ⊢e₁)
         (⊢-weaken Θ Γ x τ Δ x∉ ⊢e₂)
⊢-weaken Θ Γ x τ Δ x∉ (Ȧ-intro {e = e}{σ} L y⊢ey→) = 
  Ȧ-intro (x ∷ L) yx⊢ey→
 where yx⊢ey→ : ∀ y → y ∉ x ∷ L
                → (y ∷ Θ) , Γ ++ (x , τ) ∷ Δ ⊢ instVarτ y e ∶ instVar₁ y σ
       yx⊢ey→ y y∉ with ∉-uncons x L y∉
       ... | (y≠x , y∉L) = ⊢-weaken (y ∷ Θ) Γ x τ Δ x∉ (y⊢ey→ y y∉L)
⊢-weaken Θ Γ x τ Δ x∉ (Ȧ-elim ⊢e ⊢₁τ) = 
  Ȧ-elim (⊢-weaken Θ Γ x τ Δ x∉ ⊢e) ⊢₁τ


⊢₁-subst : ∀ Θ x Φ {σ τ} 
           → (Θ ++ [ x ] ++ Φ) ⊢₁ σ
           → (Θ ++ Φ) ⊢₁ τ
           → (Θ ++ Φ) ⊢₁ [ x ↝ τ ]₁ σ
⊢₁-subst Θ x Φ (var {._}{y} D y∈) ⊢₁τ with x ≟S y
... | yes x≡y rewrite x≡y = ⊢₁τ
... | no  x≠y = var (Distct-rm Θ x Φ D) (∈-rm Θ x Φ y x≠y y∈)
⊢₁-subst Θ x Φ (x⊢₁σ ⇒ x⊢₁γ) ⊢₁τ = 
  ⊢₁-subst Θ x Φ x⊢₁σ ⊢₁τ ⇒ 
  ⊢₁-subst Θ x Φ x⊢₁γ ⊢₁τ
⊢₁-subst Θ x Φ {._} {τ} (Ȧ {._} {σ} L x⊢τ→) ⊢₁τ = 
  Ȧ (x ∷ (Θ ++ Φ) ++ L) ⊢τ→
 where ⊢τ→ : ∀ y → y ∉ x ∷ (Θ ++ Φ) ++ L 
             → (y ∷ Θ ++ Φ) ⊢₁ instVar₁ y ([ x ↝ inject₁ τ ]₁ σ)
       ⊢τ→ y y∉ with 
         let y∉L : y ∉ L 
             y∉L = ∉-++-r (Θ ++ Φ) (∉-∷-tl y∉)
             y∉ΘΦ : y ∉ (Θ ++ Φ)
             y∉ΘΦ = ∉-++-l (Θ ++ Φ) (∉-∷-tl y∉)
         in ⊢₁-subst (y ∷ Θ) x Φ (x⊢τ→ y y∉L)
               (⊢₁-weaken [] y (Θ ++ Φ) y∉ΘΦ ⊢₁τ)
       ... | y⊢σ rewrite subst₁-instVar₁ x τ y σ (∉-∷-hd y∉) = y⊢σ

⊢-substτ : ∀ Θ x Φ Γ {e σ τ}
           → (Θ ++ [ x ] ++ Φ) , Γ ⊢ e ∶ σ
           → (Θ ++ Φ) ⊢₁ τ 
           → (Θ ++ Φ) , substCxt₁ x τ Γ ⊢ ([ x ↝ τ ]τ e) ∶ ([ x ↝ τ ]₁ σ)
⊢-substτ Θ x Φ Γ (var {x = y} D y∈) ⊢₁τ = 
 var (substCxt₁Distct x _ D) 
     (substCxt₁-∈ y _ x _ y∈)
⊢-substτ Θ x Φ Γ {τ = τ} (⇒-intro {e = e}{γ}{σ} x⊢₁σ L y⊢ey→) ⊢₁τ = 
  ⇒-intro (⊢₁-subst Θ x Φ x⊢₁σ ⊢₁τ) 
          (x ∷ L) y⊢ey'
 where y⊢ey' : ∀ y → y ∉ (x ∷ L)
                → (Θ ++ Φ) , substCxt₁ x τ ((y , γ) ∷ Γ) ⊢
                     instVar y ([ x ↝ τ ]τ e) ∶ [ x ↝ τ ]₁ σ
       y⊢ey' y y∉ with let xy⊢ey : (Θ ++ x ∷ Φ) , (y , γ) ∷ Γ ⊢ 
                                      [ 0 ↦ fv y ] e ∶ σ
                           xy⊢ey = y⊢ey→ y (∉-∷-tl y∉)
                       in ⊢-substτ Θ x Φ ((y , γ) ∷ Γ) xy⊢ey ⊢₁τ
       ...   | y⊢exy rewrite substτ-instVar x τ y e (∉-∷-hd y∉) = y⊢exy
⊢-substτ Θ x Φ Γ (⇒-elim x⊢e₀ x⊢e₁) ⊢₁τ = 
  ⇒-elim (⊢-substτ Θ x Φ Γ x⊢e₀ ⊢₁τ) 
         (⊢-substτ Θ x Φ Γ x⊢e₁ ⊢₁τ)
⊢-substτ Θ x Φ Γ  {τ = σ} (Ȧ-intro {e = e}{τ} L yx⊢ey→) ⊢₁τ = 
  Ȧ-intro (x ∷ (Θ ++ Φ) ++ L) y⊢ey→
 where y⊢ey→ : ∀ y → y ∉ x ∷ (Θ ++ Φ) ++ L
               → (y ∷ Θ ++ Φ) , substCxt₁ x σ Γ ⊢
                    instVarτ y ([ x ↝ inject₁ σ ]τ e) ∶
                    instVar₁ y ([ x ↝ inject₁ σ ]₁ τ)
       y⊢ey→ y y∉ with ∉-split-3 x (Θ ++ Φ) L y∉
       ... | (y≠x , y∉ΘΦ , y∉L)with 
          let yx⊢ey : (y ∷ Θ ++ x ∷ Φ) , Γ ⊢ 
                   instVarτ y e ∶ instVar₁ y τ
              yx⊢ey = yx⊢ey→ y y∉L
          in ⊢-substτ (y ∷ Θ) x Φ Γ yx⊢ey 
               (⊢₁-weaken [] y (Θ ++ Φ) y∉ΘΦ ⊢₁τ)
       ... | y⊢ey rewrite substτ-instVarτ x σ y e y≠x
                        | subst₁-instVar₁ x σ y τ y≠x
            = y⊢ey
⊢-substτ Θ x Φ Γ {τ = τ} (Ȧ-elim {e = e}{σ}{γ} x⊢e x⊢₁γ) ⊢₁τ 
  rewrite subst₁-inst₁ x τ γ σ = 
   Ȧ-elim {Θ ++ Φ} {substCxt₁ x τ Γ}
          {[ x ↝ τ ]τ e} {[ x ↝ inject₁ τ ]₁ σ} {[ x ↝ τ ]₁ γ} 
       (⊢-substτ Θ x Φ Γ {e} {Ȧ σ} {τ} x⊢e ⊢₁τ)
       (⊢₁-subst Θ x Φ x⊢₁γ ⊢₁τ)

⊢-subst : ∀ Θ Γ x τ Δ {e t σ} 
          → Θ , (Γ ++ [(x , τ)] ++ Δ) ⊢ e ∶ σ
          → Θ , (Γ ++ Δ) ⊢ t ∶ τ
          → Θ , (Γ ++ Δ) ⊢ [ x ↝ t ] e ∶ σ
⊢-subst Θ Γ x τ Δ (var {x = y} D y∈) ⊢t with x ≟S y 
... | yes x≡y rewrite x≡y
              | assoc-≡ Γ y Δ D y∈ = ⊢t
... | no  x≠y = var (assoc-rm Γ x Δ D) (assoc-≠ Γ x Δ y D x≠y y∈)
⊢-subst Θ Γ x τ Δ {t = t} (⇒-intro {e = e}{σ = γ}{σ} ⊢γ L yx⊢ey→) ⊢t = 
   ⇒-intro ⊢γ (x ∷ dom (Γ ++ Δ) ++ L) y⊢ey→
 where y⊢ey→ : ∀ y → y ∉ x ∷ dom (Γ ++ Δ) ++ L
                → Θ , (y , γ) ∷ Γ ++ Δ ⊢ instVar y ([ x ↝ inject t ] e) ∶ σ
       y⊢ey→ y y∉ with ∉-split-3 x (dom (Γ ++ Δ)) L y∉
       ... | (y≠x , y∉ΓΔ , y∉L) with
          let yx⊢ey : Θ , (y , γ) ∷ Γ ++ (x , τ) ∷ Δ ⊢ [ 0 ↦ fv y ] e ∶ σ
              yx⊢ey = yx⊢ey→ y y∉L 
          in ⊢-subst Θ ((y , γ) ∷ Γ) x τ Δ 
                yx⊢ey (⊢-weaken Θ [] y γ (Γ ++ Δ) y∉ΓΔ ⊢t)
       ... | y⊢ey rewrite subst-instVar x t y e y≠x = y⊢ey
⊢-subst Θ Γ x τ Δ (⇒-elim ⊢e₁ ⊢e₂) ⊢t = 
   ⇒-elim (⊢-subst Θ Γ x τ Δ ⊢e₁ ⊢t) 
          (⊢-subst Θ Γ x τ Δ ⊢e₂ ⊢t)
⊢-subst Θ Γ x τ Δ {t = t} (Ȧ-intro {e = e}{σ} L yx⊢ey→) ⊢t = 
  Ȧ-intro (x ∷ Θ ++ L) y⊢ey→
 where y⊢ey→ : ∀ y → y ∉ x ∷ Θ ++ L
               → (y ∷ Θ) , Γ ++ Δ ⊢ 
                    instVarτ y ([ x ↝ injectτ t ] e) ∶ instVar₁ y σ
       y⊢ey→ y y∉ with ∉-split-3 x Θ L y∉
       ... | (y≠x , y∉Θ , y∉L) with
          let yx⊢ey : (y ∷ Θ) , Γ ++ (x , τ) ∷ Δ ⊢ instVarτ y e ∶ instVar₁ y σ
              yx⊢ey = yx⊢ey→ y y∉L
          in ⊢-subst (y ∷ Θ) Γ x τ Δ yx⊢ey 
             (⊢-weakenτ [] y Θ _ y∉Θ ⊢t)
       ... | y⊢ey rewrite 
                subst-instVarτ x t y e y≠x = y⊢ey
⊢-subst Θ Γ x τ Δ (Ȧ-elim x⊢e ⊢₁τ) ⊢t = 
  Ȧ-elim (⊢-subst Θ Γ x τ Δ x⊢e ⊢t) ⊢₁τ

open import FVars

{-

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
-}

open import Data.Nat using (_+_)
open import Reduction

postulate
 preservation : ∀ {e e' : Expr} {τ}
                → [] , [] ⊢ e ∶ τ 
                → e ⟼ e'
                → [] , [] ⊢ e' ∶ τ

{-
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

-}
