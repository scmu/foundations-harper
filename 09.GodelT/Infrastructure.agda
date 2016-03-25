module Infrastructure where

open import Data.Empty using (⊥-elim)
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_; inject)
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Membership
open import Data.List.Any hiding (map)
open Data.List.Any.Membership-≡
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (¬_; yes; no)

open import Exp

-- [_↦_] : ∀ n → Exp n → Exp (suc n) → Exp n
-- [_↝_] : ∀ {n} → FName → Exp n → Exp n → Exp n

inject-subst : ∀ {n} x (t u : Exp n) 
               → inject ([ x ↝ t ] u) ≡ [ x ↝ inject t ] (inject u)
inject-subst x t (bv i) = refl
inject-subst x t (fv y) with x ≟S y
... | yes _ = refl
... | no  _ = refl
inject-subst x t zero = refl
inject-subst x t (suc u) 
  rewrite inject-subst x t u = refl
inject-subst x t (elimℕ u₁ u₂ u)
  rewrite inject-subst x t u₁
        | inject-subst x (inject (inject t)) u₂ 
        | inject-subst x t u = refl
inject-subst x t (ƛ _ u)
  rewrite inject-subst x (inject t) u = refl
inject-subst x t (u₁ · u₂) 
  rewrite inject-subst x t u₁ | inject-subst x t u₂ = refl

private 

 suc-inj : ∀ {x y : ℕ} → _≡_ {A = ℕ} (suc x) (suc y) → x ≡ y
 suc-inj refl = refl

 n∉Finn : ∀ {n} (i : Fin n) → ¬ (n ≡ toℕ (inject₁ i))
 n∉Finn zero ()
 n∉Finn (suc i) eq = n∉Finn i (suc-inj eq) 

open-term : ∀ {n} (e : Exp n) f
            → [ n ↦ f ] (inject e) ≡ e
open-term {n} (bv i) f with n ≟ℕ toℕ (inject₁ i)
... | yes n=i = ⊥-elim (n∉Finn i n=i)
... | no  n≠i rewrite lowerF-inject n≠i = refl
open-term (fv x) f = refl
open-term zero f = refl
open-term (suc e) f rewrite open-term e f = refl
open-term (elimℕ e₁ e₂ e) f 
  rewrite open-term e₁ f
        | open-term e₂ (inject (inject f))
        | open-term e f = refl
open-term (ƛ _ e) f rewrite open-term e (inject f) = refl
open-term (e₁ · e₂) f rewrite open-term e₁ f | open-term e₂ f = refl

subst-fresh : ∀ {n} x t (e : Exp n) → x ∉ fvars e → [ x ↝ t ] e ≡ e
subst-fresh x t (bv i) x∉ = refl
subst-fresh x t (fv y) x∉ with x ≟S y
... | yes x≡y = ⊥-elim (x∉ (here x≡y))
... | no  _ = refl
subst-fresh x t zero x∉ = refl
subst-fresh x t (suc e) x∉ rewrite 
    subst-fresh x t e x∉ = refl
subst-fresh x t (elimℕ e₁ e₂ e) x∉ rewrite
    subst-fresh x t e₁ (∉-++-l (fvars e₁) _ x∉)
  | subst-fresh x (inject (inject t)) e₂ (∉-++-l (fvars e₂) _ (∉-++-r (fvars e₁) _ x∉))
  | subst-fresh x t e (∉-++-r (fvars e₂) _ (∉-++-r (fvars e₁) _ x∉)) = refl 
subst-fresh x t (ƛ _ e) x∉ rewrite 
    subst-fresh x (inject t) e x∉ = refl
subst-fresh x t (e₁ · e₂) x∉ rewrite 
    subst-fresh x t e₁ (∉-++-l (fvars e₁) _ x∉)
  | subst-fresh x t e₂ (∉-++-r (fvars e₁) _ x∉) = refl

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
subst-open x t u (elimℕ e₁ e₂ e) 
  rewrite subst-open x t u e₁ 
        | subst-open x (inject (inject t)) (inject (inject u)) e₂
        | inject-subst x t u
        | subst-open x t u e
        | inject-subst x (inject t) (inject u)
  = refl
subst-open x t u (ƛ _ e) 
  rewrite subst-open x (inject t) (inject u) e 
        | inject-subst x t u = refl
subst-open x t u (e₁ · e₂) 
  rewrite subst-open x t u e₁ | subst-open x t u e₂ = refl

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

