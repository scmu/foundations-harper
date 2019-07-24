module Infrastructure where

open import Data.Empty using (⊥-elim)
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_; inject) renaming (inject₁ to injectF)
open import Data.Fin.Properties
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (¬_; yes; no)

open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any

open import Membership
open import Exp

inject₁-subst₁ : ∀ {m} x (τ σ : Typ m) 
                → inject₁ ([ x ↝ τ ]₁ σ ) ≡ [ x ↝ inject₁ τ ]₁ (inject₁ σ)
inject₁-subst₁ x τ (bv i) = refl
inject₁-subst₁ x τ (fv y) with x ≟S y
... | yes _ = refl
... | no  _ = refl 
inject₁-subst₁ x τ (σ ⇒ γ)
  rewrite inject₁-subst₁ x τ σ 
        | inject₁-subst₁ x τ γ = refl
inject₁-subst₁ x τ (Ȧ σ) 
  rewrite inject₁-subst₁ x (inject₁ τ) σ = refl


private 
 suc-inj : ∀ {x y : ℕ} → _≡_ {A = ℕ} (suc x) (suc y) → x ≡ y
 suc-inj refl = refl

 n∉Finn : ∀ {n} (i : Fin n) → ¬ (n ≡ toℕ (injectF i))
 n∉Finn zero ()
 n∉Finn (suc i) eq = n∉Finn i (suc-inj eq) 

inst₁-closed : ∀ {m} (τ : Typ m) f
               → [ m ↦ f ]₁ (inject₁ τ) ≡ τ
inst₁-closed {m} (bv i) f with m ≟ℕ toℕ (injectF i)
... | yes m≡i = ⊥-elim (n∉Finn i m≡i)
... | no  m≠i rewrite lower₁-inject₁′ i m≠i = refl
inst₁-closed (fv x) f = refl
inst₁-closed (σ ⇒ τ) f 
  rewrite inst₁-closed σ f
        | inst₁-closed τ f = refl
inst₁-closed (Ȧ τ) f 
  rewrite inst₁-closed τ (inject₁ f) = refl

subst₁-inst₁ : ∀ {m} x (τ : Typ m) (σ : Typ m) (e : Typ(suc m))
              → [ x ↝ τ ]₁ ([ m ↦ σ ]₁ e) ≡
                   [ m ↦ ([ x ↝ τ ]₁ σ) ]₁ ([ x ↝ (inject₁ τ) ]₁ e)
subst₁-inst₁ {m} x τ σ (bv i) with m ≟ℕ toℕ i
... | yes _ = refl
... | no  _ = refl
subst₁-inst₁ x τ σ (fv y) with x ≟S y
... | yes _ rewrite inst₁-closed τ ([ x ↝ τ ]₁ σ) = refl
... | no  _ = refl
subst₁-inst₁ x τ σ (γ₁ ⇒ γ₂) 
 rewrite subst₁-inst₁ x τ σ γ₁ 
       | subst₁-inst₁ x τ σ γ₂ = refl
subst₁-inst₁ x τ σ (Ȧ e) 
 rewrite subst₁-inst₁ x (inject₁ τ) (inject₁ σ) e 
       | inject₁-subst₁ x τ σ = refl

postulate
 
 subst₁-instVar₁ : ∀ {n} x (τ : Typ n) y (σ : Typ (suc n))
                  → ¬ (y ≡ x) 
                  → [ x ↝ τ ]₁ ([ n ↦ fv y ]₁ σ) ≡ 
                    [ n ↦ fv y ]₁ ([ x ↝ (inject₁ τ) ]₁ σ)

 substτ-instVar : ∀ {m n} x (τ : Typ m) y (e : Exp m (suc n))
                  → ¬ (y ≡ x) 
                  → [ x ↝ τ ]τ ([ n ↦ fv y ] e) ≡ 
                    [ n ↦ fv y ] ([ x ↝ τ ]τ e)

 substτ-instVarτ : ∀ {m n} x (τ : Typ m) y (e : Exp (suc m) n)
                   → ¬ (y ≡ x) 
                   → [ x ↝ τ ]τ ([ m ↦ fv y ]τ e) ≡ 
                       [ m ↦ fv y ]τ ([ x ↝ inject₁ τ ]τ e)

 subst-instVarτ : ∀ {m n} x (t : Exp m n) y (e : Exp (suc m) n)
                 → ¬ (y ≡ x) 
                 → [ x ↝ t ] ([ m ↦ fv y ]τ e) ≡ 
                    [ m ↦ fv y ]τ ([ x ↝ injectτ t ] e)

 subst-instVar : ∀ {m n} x (t : Exp m n) y (e : Exp m (suc n))
                 → ¬ (y ≡ x) 
                 → [ x ↝ t ] ([ n ↦ fv y ] e) ≡ 
                    [ n ↦ fv y ] ([ x ↝ (inject t) ] e)

{-

inject-subst : ∀ {n} x (t u : Exp n) 
               → inject ([ x ↝ t ] u) ≡ [ x ↝ inject t ] (inject u)
inject-subst x t (bv i) = refl
inject-subst x t (fv y) with x ≟S y
... | yes _ = refl
... | no  _ = refl
inject-subst x t zero = refl
inject-subst x t (suc u) 
  rewrite inject-subst x t u = refl
inject-subst x t (ifz u u₀ u₁)
  rewrite inject-subst x t u
        | inject-subst x t u₀
        | inject-subst x (inject t) u₁ = refl
inject-subst x t (ƛ _ u)
  rewrite inject-subst x (inject t) u = refl
inject-subst x t (u₁ · u₂) 
  rewrite inject-subst x t u₁ | inject-subst x t u₂ = refl
inject-subst x t (μ _ u)
  rewrite inject-subst x (inject t) u = refl

open-term : ∀ {n} (e : Exp n) f
            → [ n ↦ f ] (inject e) ≡ e
open-term {n} (bv i) f with n ≟ℕ toℕ (inject₁ i)
... | yes n=i = ⊥-elim (n∉Finn i n=i)
... | no  n≠i rewrite lowerF-inject n≠i = refl
open-term (fv x) f = refl
open-term zero f = refl
open-term (suc e) f rewrite open-term e f = refl
open-term (ifz e e₀ e₁) f 
  rewrite open-term e f
        | open-term e₀ f
        | open-term e₁ (inject f) = refl
open-term (ƛ _ e) f rewrite open-term e (inject f) = refl
open-term (e₁ · e₂) f rewrite open-term e₁ f | open-term e₂ f = refl
open-term (μ _ e) f rewrite open-term e (inject f) = refl

subst-fresh : ∀ {n} x t (e : Exp n) → x ∉ fvars e → [ x ↝ t ] e ≡ e
subst-fresh x t (bv i) x∉ = refl
subst-fresh x t (fv y) x∉ with x ≟S y
... | yes x≡y = ⊥-elim (x∉ (here x≡y))
... | no  _ = refl
subst-fresh x t zero x∉ = refl
subst-fresh x t (suc e) x∉ rewrite 
    subst-fresh x t e x∉ = refl
subst-fresh x t (ifz e e₀ e₁) x∉ rewrite
    subst-fresh x t e (∉-++-l (fvars e) _ x∉)
  | subst-fresh x t e₀ (∉-++-l (fvars e₀) _ (∉-++-r (fvars e) _ x∉))
  | subst-fresh x (inject t) e₁ 
          (∉-++-r (fvars e₀) _ (∉-++-r (fvars e) _ x∉))
   = refl 
subst-fresh x t (ƛ _ e) x∉ rewrite 
    subst-fresh x (inject t) e x∉ = refl
subst-fresh x t (e₁ · e₂) x∉ rewrite 
    subst-fresh x t e₁ (∉-++-l (fvars e₁) _ x∉)
  | subst-fresh x t e₂ (∉-++-r (fvars e₁) _ x∉) = refl
subst-fresh x t (μ _ e) x∉ rewrite 
    subst-fresh x (inject t) e x∉ = refl

subst-open : ∀ {n} x (t : Exp n) (u : Exp n) (e : Exp (suc n))
             → [ x ↝ t ] ([ n ↦ u ] e) ≡ 
                 [ n ↦ ([ x ↝ t ] u) ] ([ x ↝ (inject t) ] e)
subst-open {n} x t u (bv i) with n ≟ℕ toℕ i 
... | yes _ = refl
... | no  _ = refl
subst-open x t u (fv y) with x ≟S y
... | yes _ = sym (open-term t ([ x ↝ t ] u))
... | no  _ = refl
subst-open x t u zero = refl
subst-open x t u (suc e) 
  rewrite subst-open x t u e = refl
subst-open x t u (ifz e e₀ e₁) 
  rewrite subst-open x t u e
        | subst-open x t u e₀
        | subst-open x (inject t) (inject u) e₁
        | inject-subst x t u
  = refl
subst-open x t u (ƛ _ e) 
  rewrite subst-open x (inject t) (inject u) e 
        | inject-subst x t u = refl
subst-open x t u (e₁ · e₂) 
  rewrite subst-open x t u e₁ | subst-open x t u e₂ = refl
subst-open x t u (μ _ e) 
  rewrite subst-open x (inject t) (inject u) e 
        | inject-subst x t u = refl


subst-openVar : ∀ {n} x (t : Exp n) y (e : Exp (suc n))
                → ¬ (y ≡ x) 
                → [ x ↝ t ] ([ n ↦ fv y ] e) ≡ 
                   [ n ↦ fv y ] ([ x ↝ (inject t) ] e)
subst-openVar x t y e y≠x 
  with subst-open x t (fv y) e
... | eq with x ≟S y
...      | yes x≡y = ⊥-elim (y≠x (sym x≡y))
...      | no  _  = eq

subst-intro : ∀ {n} x t (e : Exp (suc n)) → x ∉ fvars e
              → [ n ↦ t ] e ≡ [ x ↝ t ] ([ n ↦ fv x ] e)
subst-intro x t e x∉ 
  with subst-open x t (fv x) e 
... | eq with x ≟S x 
...      | yes refl rewrite subst-fresh x (inject t) e x∉ = sym eq
...      | no x≠x = ⊥-elim (x≠x refl)

-}
