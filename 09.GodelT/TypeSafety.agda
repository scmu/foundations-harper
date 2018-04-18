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

⊢-weaken : ∀ Γ x τ Δ {e σ} 
           → x ∉ dom (Γ ++ Δ)
           → (Γ ++ Δ) ⊢ e ∶ σ
           → (Γ ++ [(x , τ)] ++ Δ) ⊢ e ∶ σ
⊢-weaken Γ x τ Δ x∉ (var D y) = 
  var (DomDist-ins Γ x Δ D x∉) (∈-++-weaken Γ [ x , τ ] Δ y)
⊢-weaken Γ x τ Δ x∉ zero = zero
⊢-weaken Γ x τ Δ x∉ (suc t) =
  suc (⊢-weaken Γ x τ Δ x∉ t)
⊢-weaken Γ x τ Δ {σ = σ} x∉ (ℕ-elim {e₁ = e₁}{e₂}{e} t₁ L t₂ t) = 
  ℕ-elim (⊢-weaken Γ x τ Δ x∉ t₁) 
         (x ∷ L) fn 
         (⊢-weaken Γ x τ Δ x∉ t)
  where fn : ∀ y z → ¬ (y ≡ z) → y ∉ x ∷ L → z ∉ x ∷ L
              → ((y , nat) ∷ (z , σ) ∷ Γ ++ [ x , τ ] ++ Δ) 
                    ⊢ instVar y ([ 1 ↦ fv z ] e₂) ∶ σ
        fn y z y≠z y∉ z∉ = ⊢-weaken ((y , nat) ∷ (z , σ) ∷ Γ) x τ Δ x∉'
                           (t₂ y z y≠z (∉-∷-tl L y∉) (∉-∷-tl L z∉))
           where x∉' : x ∉ dom ((y , nat) ∷ (z , σ) ∷ Γ ++ Δ)
                 x∉' = ∉-∷ (≠-sym (∉-∷-hd L y∉))
                        (∉-∷ (≠-sym (∉-∷-hd L z∉)) x∉)
⊢-weaken Γ x τ Δ x∉ (⇒-intro {._} {e} {σ} {υ} L fn) = ⇒-intro (x ∷ L) fn'
  where fn' : ∀ y → y ∉ (x ∷ L) 
              → ((y , σ) ∷ Γ ++ [ x , τ ] ++ Δ) ⊢ instVar y e ∶ υ
        fn' y y∉ = ⊢-weaken ((y , σ) ∷ Γ) x τ Δ x∉' (fn y (∉-∷-tl L y∉))
           where x∉' : x ∉ dom ((y , σ) ∷ Γ ++ Δ)
                 x∉' = ∉-∷ (≠-sym (∉-∷-hd L y∉)) x∉
⊢-weaken Γ x τ Δ x∉ (⇒-elim t₁ t₂) = ⇒-elim (⊢-weaken Γ x τ Δ x∉ t₁) (⊢-weaken Γ x τ Δ x∉ t₂)

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
⊢-subst Γ x τ Δ  {._} {t} {σ}
        (ℕ-elim {e₁ = e₁} {e₂} {e} t₁ L f t₂) t₃ = 
  ℕ-elim (⊢-subst Γ x τ Δ t₁ t₃) 
         (x ∷ dom (Γ ++ Δ) ++ L) fn
         (⊢-subst Γ x τ Δ t₂ t₃) 
 where fn : ∀ y z → ¬ (y ≡ z)
            → y ∉ (x  ∷ dom (Γ ++ Δ) ++ L) → z ∉ (x  ∷ dom (Γ ++ Δ) ++ L)
            → ((y , nat) ∷ (z , σ) ∷ Γ ++ Δ) ⊢
                  instVar y ([ 1 ↦ fv z ] ([ x ↝ inject (inject t) ] e₂)) ∶ σ
       fn y z y≠z y∉ z∉ with 
            let y∉L = ∉-++-r (dom (Γ ++ Δ)) L (∉-∷-tl _ y∉)
                y∉ΓΔ = ∉-++-l (dom (Γ ++ Δ)) L (∉-∷-tl _ y∉)
                z∉L = ∉-++-r (dom (Γ ++ Δ)) L (∉-∷-tl _ z∉)
                z∉ΓΔ = ∉-++-l (dom (Γ ++ Δ)) L (∉-∷-tl _ z∉)
            in ⊢-subst ((y , nat) ∷ (z , σ) ∷ Γ) x τ Δ
                        {instVar y ([ 1 ↦ fv z ] e₂)} {t} {σ}
                        (f y z y≠z y∉L z∉L) 
                        (⊢-weaken [] y nat ((z , σ) ∷ Γ ++ Δ) 
                                            (∉-∷ y≠z y∉ΓΔ) 
                          (⊢-weaken [] z σ (Γ ++ Δ) z∉ΓΔ t₃))
       ... | ⊢e₂ rewrite subst-openVar x t y ([ 1 ↦ fv z ] e₂) (∉-∷-hd _ y∉)
                       | subst-openVar x (inject t) z e₂ (∉-∷-hd _ z∉)
                         = ⊢e₂
⊢-subst Γ x τ Δ {._} {t} (⇒-intro {._} {e} {σ} {υ} L fn) t₃ = 
  ⇒-intro (x ∷ dom (Γ ++ Δ) ++ L) fn'
  where fn' : ∀ y → y ∉ (x ∷ dom (Γ ++ Δ) ++ L)
              → ((y , σ) ∷ Γ ++ Δ) ⊢ instVar y ([ x ↝ inject t ] e) ∶ υ
        fn' y y∉ with let y∉L : y ∉ L
                          y∉L = ∉-++-r (dom (Γ ++ Δ)) L (∉-∷-tl _ y∉)
               
                          y∉ΓΔ : y ∉ dom (Γ ++ Δ)
                          y∉ΓΔ = ∉-++-l (dom (Γ ++ Δ)) L (∉-∷-tl _ y∉)
                      in ⊢-subst ((y , σ) ∷ Γ) x τ Δ (fn y y∉L)
                                 (⊢-weaken [] y σ (Γ ++ Δ) y∉ΓΔ t₃)
        ...     | ⊢xye rewrite subst-openVar x t y e (∉-∷-hd _ y∉) = ⊢xye 
{-   
  -- The definition below results in a stack overflow. --

  where fn' : ∀ y → y ∉ (x ∷ dom (Γ ++ Δ) ++ L)
              → ((y , σ) ∷ Γ ++ Δ) ⊢ instVar y ([ x ↝ inject t ] e) ∶ υ
        fn' y y∉ = body ⊢xye  

           where y∉L : y ∉ L
                 y∉L = ∉-++-r (dom (Γ ++ Δ)) L (∉-∷-tl _ y∉)
               
                 y∉ΓΔ : y ∉ dom (Γ ++ Δ)
                 y∉ΓΔ = ∉-++-l (dom (Γ ++ Δ)) L (∉-∷-tl _ y∉)

                 ⊢ye : ((y , σ) ∷ Γ ++ (x , τ) ∷ Δ) ⊢ instVar y e ∶ υ
                 ⊢ye = fn y y∉L

                 ⊢t : ((y , σ) ∷ Γ ++ Δ) ⊢ t ∶ τ
                 ⊢t = ⊢-weaken [] y σ (Γ ++ Δ) y∉ΓΔ t₃

                 ⊢xye : ((y , σ) ∷ Γ ++ Δ) ⊢ [ x ↝ t ] (instVar y e) ∶ υ
                 ⊢xye = ⊢-subst ((y , σ) ∷ Γ) x τ Δ ⊢ye ⊢t 

                 body : ((y , σ) ∷ Γ ++ Δ) ⊢ [ x ↝ t ] (instVar y e) ∶ υ
                        → ((y , σ) ∷ Γ ++ Δ) ⊢ instVar y ([ x ↝ inject t ] e) ∶ υ
                 body ⊢xye rewrite subst-openVar x t y e (∉-∷-hd _ y∉)
                   = ⊢xye -}
⊢-subst Γ x τ Δ (⇒-elim t₁ t₂) t₃ = 
  ⇒-elim (⊢-subst Γ x τ Δ t₁ t₃) (⊢-subst Γ x τ Δ t₂ t₃)


open import Data.Nat using (_+_)
open import FVars
open import Reduction


preservation : ∀ {e e' : Expr} {τ}
               → [] ⊢ e ∶ τ 
               → e ⟼ e'
               → [] ⊢ e' ∶ τ
preservation t (appL e₁⟼e₁') with t
... | (⇒-elim ⊢e₁ ⊢e₂) =
  ⇒-elim (preservation ⊢e₁ e₁⟼e₁') ⊢e₂
preservation {(ƛ .σ .e₁) · .e₂} (⇒-elim {τ = τ} (⇒-intro L fn) ⊢e₂) (app {σ} {e₁} {e₂}) 
  with freshgen-2 (fvars e₁) L
... | (y , y∉e₁ , y∉L) = body
  where y⊢e₁ : ((y , σ) ∷ []) ⊢ instVar y e₁ ∶ τ
        y⊢e₁ = fn y y∉L

        ⊢ye₁e₂ : [] ⊢ [ y ↝ e₂ ] (instVar y e₁) ∶ τ
        ⊢ye₁e₂ = ⊢-subst [] y σ [] y⊢e₁ ⊢e₂

        body : [] ⊢ inst e₂ e₁ ∶ τ
        body with subst-intro y e₂ e₁ y∉e₁
        ...  | eq = subst (λ u → [] ⊢ u ∶ τ) (sym eq) ⊢ye₁e₂
preservation {elimℕ .e₀ .e₁ .e} (ℕ-elim ⊢e₀ L ⊢e₁ ⊢e) (elimℕ {e₀} {e₁} {e} {e'} e⟼e') = 
   ℕ-elim ⊢e₀ L ⊢e₁ (preservation ⊢e e⟼e')
preservation {elimℕ .e₀ .e₁ .zero} (ℕ-elim ⊢e₀ L ⊢e₁ ⊢e) (elimℕ₀ {e₀} {e₁}) = ⊢e₀
preservation {elimℕ .e₀ .e₁ (suc .e)} (ℕ-elim {._}{τ} ⊢e₀ L ⊢e₁ (suc ⊢e)) (elimℕ₁ {e₀} {e₁} {e}) 
  with freshgen-4 (fvars e₀) (fvars e₁) (fvars e) L 
...     | (y , y∉e₀ , y∉e₁ , y∉e , y∉L) with freshgen-5 [ y ] (fvars e₀) (fvars e₁) (fvars e) L 
...     | (z , z∉[y] , z∉e₀ , z∉e₁ , z∉e , z∉L) = body ⊢e₁yz
  where y≠z : ¬ (y ≡ z)
        y≠z = ≠-sym (∉-∷-hd [] z∉[y])

        yz⊢e₁ : ((y , nat) ∷ (z , τ) ∷ []) ⊢ [ 0 ↦ fv y ] ([ 1 ↦ fv z ] e₁) ∶ τ
        yz⊢e₁ = ⊢e₁ y z y≠z y∉L z∉L 

        z⊢e₁y : ((z , τ) ∷ []) ⊢ [ y ↝ e ] ([ 0 ↦ fv y ] ([ 1 ↦ fv z ] e₁)) ∶ τ
        z⊢e₁y = ⊢-subst [] y nat ((z , τ) ∷ [])
                        yz⊢e₁ (⊢-weaken [] z τ [] ∉-[] ⊢e)

        ⊢elim : [] ⊢ elimℕ e₀ e₁ e ∶ τ
        ⊢elim = ℕ-elim ⊢e₀ L ⊢e₁ ⊢e

        ⊢e₁yz : [] ⊢ [ z ↝ elimℕ e₀ e₁ e ] ([ y ↝ e ] ([ 0 ↦ fv y ] ([ 1 ↦ fv z ] e₁))) ∶ τ
        ⊢e₁yz = ⊢-subst [] z τ [] z⊢e₁y ⊢elim 

        postulate 
           y∉ze₁ : y ∉ fvars ([ 1 ↦ fv z ] e₁)

        body : [] ⊢ [ z ↝ elimℕ e₀ e₁ e ] ([ y ↝ e ] ([ 0 ↦ fv y ] ([ 1 ↦ fv z ] e₁))) ∶ τ
               →  [] ⊢ [ 0 ↦ e ] ([ 1 ↦ elimℕ (inject e₀) (inject e₁) (inject e) ] e₁) ∶ τ
        body t rewrite sym (subst-intro y e ([ 1 ↦ fv z ] e₁) y∉ze₁)
                     | subst-open z (elimℕ e₀ e₁ e) e ([ 1 ↦ fv z ] e₁)
                     | sym (subst-intro z (elimℕ (inject e₀) (inject e₁) (inject e)) e₁ z∉e₁)
                     | subst-fresh z (elimℕ e₀ e₁ e) e z∉e
                = t

progress : ∀ {e : Expr} {τ}
           → [] ⊢ e ∶ τ 
           → ¬ (Val e)
           → ∃ (λ e' → e ⟼ e')

progress (var _ ()) _
progress zero ¬Val = ⊥-elim (¬Val zero)
progress (suc _) ¬Val = ⊥-elim (¬Val (suc _))
progress {elimℕ e₀ e₁ e} (ℕ-elim t₀ L t₁ t) ¬Val with val? e
progress {elimℕ e₀ e₁ .zero} (ℕ-elim t₀ L t₁ t) ¬Val | inj₁ zero = e₀ , elimℕ₀
progress {elimℕ e₀ e₁ .(suc e)} (ℕ-elim t₀ L t₁ t) ¬Val | inj₁ (suc e) = 
  inst e ([ 1 ↦ inject (elimℕ e₀ e₁ e) ] e₁) , elimℕ₁
progress {elimℕ e₀ e₁ .(ƛ τ e)} (ℕ-elim t₀ L t₁ ()) ¬Val | inj₁ (ƛ τ e)
progress {elimℕ e₀ e₁ e} (ℕ-elim t₀ L t₁ t) _    | inj₂ ¬V  
  with progress {e} t ¬V
...  | (e' , e⟼e') = elimℕ e₀ e₁ e' , elimℕ e⟼e'
progress {ƛ σ e} (⇒-intro L x) ¬Val = ⊥-elim (¬Val (ƛ σ e))
progress {e₁ · e₂} (⇒-elim ⊢e₁ ⊢e₂) _ with val? e₁
progress {._ · e₂} (⇒-elim () ⊢e₂) _ | inj₁ zero 
progress {._ · e₂} (⇒-elim () ⊢e₂) _ | inj₁ (suc _)
progress {._ · e₂} (⇒-elim ⊢e₁ ⊢e₂) _ | inj₁ (ƛ τ e) = inst e₂ e , app
progress {e₁ · e₂} (⇒-elim ⊢e₁ ⊢e₂) _ | inj₂ ¬Val 
    with progress ⊢e₁ ¬Val 
... | (e₁' , e₁⟼e₁') = e₁' · e₂ , appL e₁⟼e₁' 

