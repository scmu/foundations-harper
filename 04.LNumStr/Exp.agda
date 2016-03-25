module Exp where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_; inject)
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.List 
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)

FName : Set
FName = String

FNames : Set
FNames = List FName

data Exp : ℕ → Set where
  bv : ∀ {n} → (i : Fin n) → Exp n
  fv : ∀ {n} → (x : FName) → Exp n
  num : ∀ {n} → (m : ℕ) → Exp n
  str : ∀ {n} → (s : String) → Exp n
  _∔_ : ∀ {n} → (e₁ : Exp n) → (e₂ : Exp n) → Exp n
  _^_ : ∀ {n} → (e₁ : Exp n) → (e₂ : Exp n)→ Exp n
  len : ∀ {n} → (e : Exp n) → Exp n 
  lett : ∀ {n} → (e₁ : Exp n) → (e₂ : Exp (suc n)) → Exp n

Expr : Set
Expr = Exp 0

private
 postulate i+1+j≡1+i+j : ∀ i j → i + suc j ≡ suc (i + j)

inject : ∀ {n} →  Exp n → Exp (suc n)
inject (bv i) = bv (inject₁ i)
inject (fv x) = fv x
inject (num m) = num m
inject (str s) = str s
inject (e₁ ∔ e₂) = inject e₁ ∔ inject e₂
inject (e₁ ^ e₂) = inject e₁ ^ inject e₂
inject (len e) = len (inject e)
inject {n} (lett e₁ e₂) with inject e₂
... | e₂' = lett (inject e₁) e₂'
       
-- open the outermost bound variable

private 

  ne₁ : ∀ {n m} {i : Fin m} → ¬ (suc n ≡ toℕ (suc i)) → ¬ (n ≡ toℕ i)
  ne₁ {n} {m} {i} ne n≡i rewrite n≡i = ne refl

  lowerF : ∀ n → (i : Fin (suc n)) → ¬ (n ≡ toℕ i) → Fin n
  lowerF zero zero ne with ne refl
  lowerF zero zero ne | ()
  lowerF zero (suc ()) _
  lowerF (suc n) zero _ = zero
  lowerF (suc n) (suc i) ne = suc (lowerF n i (ne₁ ne))
 
lowerF-inject : ∀ {n i} neq → (lowerF n (inject₁ i) neq) ≡ i
lowerF-inject {zero} {()} _
lowerF-inject {suc n} {zero} _ = refl
lowerF-inject {suc n} {suc i} neq rewrite lowerF-inject {n} {i} (ne₁ neq) = refl

[_↦_] : ∀ n → Exp n → Exp (suc n) → Exp n
[ n ↦ t ] (bv i) with n ≟ℕ toℕ i
... | yes _ = t
... | no  n≠i = bv (lowerF n i n≠i)
[ n ↦ t ] (fv x) = fv x 
[ n ↦ t ] (num m) = num m 
[ n ↦ t ] (str s) = str s
[ n ↦ t ] (e₁ ∔ e₂) = [ n ↦ t ] e₁ ∔ [ n ↦ t ] e₂
[ n ↦ t ] (e₁ ^ e₂) = [ n ↦ t ] e₁ ^ [ n ↦ t ] e₂
[ n ↦ t ] (len e) = len ([ n ↦ t ] e)
[ n ↦ t ] (lett e₁ e₂) = lett ([ n ↦ t ] e₁) ([ suc n ↦ inject t ] e₂)

inst : Exp 0 → Exp 1 → Exp 0
inst u = [ 0 ↦ u ]

instVar : FName → Exp 1 → Exp 0
instVar x = inst (fv x)

-- close a free variable to be the outermost bound variable

[_↤_] : ∀ n → FName → Exp n → Exp (suc n)
[ n ↤ x ] (bv i) = bv (inject₁ i)
[ n ↤ x ] (fv y) with x ≟S y
... | yes _ = bv (fromℕ n)
... | no  _ = fv y
[ n ↤ x ] (num m) = num m
[ n ↤ x ] (str s) = str s
[ n ↤ x ] (e₁ ∔ e₂) = [ n ↤ x ] e₁ ∔ [ n ↤ x ] e₂
[ n ↤ x ] (e₁ ^ e₂) = [ n ↤ x ] e₁ ^ [ n ↤ x ] e₂
[ n ↤ x ] (len e) = len ([ n ↤ x ] e)
[ n ↤ x ] (lett e₁ e₂) = lett ([ n ↤ x ] e₁) ([ suc n ↤ x ] e₂)

abs : FName → Exp 0 → Exp 1
abs x = [ 0 ↤ x ]

[_↝_] : ∀ {n} → FName → Exp n → Exp n → Exp n
[ x ↝ t ] (bv i) = bv i
[ x ↝ t ] (fv y) with x ≟S y
... | yes _ = t
... | no  _ = fv y
[ x ↝ t ] (num m) = num m 
[ x ↝ t ] (str s) = str s
[ x ↝ t ] (e₁ ∔ e₂) = [ x ↝ t ] e₁ ∔ [ x ↝ t ] e₂
[ x ↝ t ] (e₁ ^ e₂) = [ x ↝ t ] e₁ ^ [ x ↝ t ] e₂
[ x ↝ t ] (len e) = len ([ x ↝ t ] e)
[ x ↝ t ] (lett e₁ e₂) = lett ([ x ↝ t ] e₁) ([ x ↝ inject t ] e₂)

inject-subst : ∀ {n} x (t u : Exp n) 
               → inject ([ x ↝ t ] u) ≡ [ x ↝ inject t ] (inject u)
inject-subst x t (bv i) = refl
inject-subst x t (fv y) with x ≟S y
... | yes _ = refl
... | no  _ = refl
inject-subst x t (num m) = refl
inject-subst x t (str s) = refl
inject-subst x t (u₁ ∔ u₂) 
  rewrite inject-subst x t u₁ | inject-subst x t u₂ = refl
inject-subst x t (u₁ ^ u₂)
  rewrite inject-subst x t u₁ | inject-subst x t u₂ = refl
inject-subst x t (len u) 
  rewrite inject-subst x t u = refl
inject-subst x t (lett u₁ u₂)
  rewrite inject-subst x t u₁
        | inject-subst x (inject t) u₂ = refl

fvars : ∀ {n} → Exp n → FNames
fvars (bv i) = []
fvars (fv x) = x ∷ []
fvars (num m) = []
fvars (str s) = []
fvars (e₁ ∔ e₂) = fvars e₁ ++ fvars e₂
fvars (e₁ ^ e₂) = fvars e₁ ++ fvars e₂
fvars (len e) = fvars e
fvars (lett e₁ e₂) = fvars e₁ ++ fvars e₂

{-
unicity-[]= : ∀ {A : Set} {n} → {xs : Vec A n} → {i : Fin n} → {x₁ x₂ : A}
              → xs [ i ]= x₁ → xs [ i ]= x₂ → x₁ ≡ x₂
unicity-[]= here here = refl
unicity-[]= (there eq1) (there eq2) = unicity-[]= eq1 eq2

unicity : ∀ {n} → (Γ : Cxt n) → (e : Exp n) → {τ₁ τ₂ : Typ}
          → Γ ⊢ e ∶ τ₁ →  Γ ⊢ e ∶ τ₂ → τ₁ ≡ τ₂
unicity {n} Γ .(var x) 
        (var {.n} {.Γ} {x} Γ[n]=τ₁)
        (var Γ[n]=τ₂) = unicity-[]= Γ[n]=τ₁ Γ[n]=τ₂
unicity {n} Γ .(num m) (num {.n} {.Γ} m) (num .m) = refl
unicity {n} Γ .(str s) (str {.n} {.Γ} s) (str .s) = refl
unicity {n} Γ .(e₁ ∔ e₂) (plus {.n} {.Γ} {e₁} {e₂} _ _) (plus _ _) = refl
unicity {n} Γ .(e₁ ^ e₂) (cat {.n} {.Γ} {e₁} {e₂} _ _) (cat _ _) = refl
unicity {n} Γ .(len e) (len {.n} {.Γ} {e} _) (len _) = refl
unicity {n} Γ .(lett e₁ e₂) (lett {.n} {.Γ} {e₁} {e₂} t₁₁ t₁₂) (lett t₂₁ t₂₂) 
  rewrite unicity Γ e₁ t₁₁ t₂₁ = unicity (_ ∷ Γ) e₂ t₁₂ t₂₂

weakening : ∀ {n} → (Γ : Cxt n) → {e : Exp n} → {τ τ' : Typ} 
            → Γ ⊢ e ∶ τ → (τ' ∷ Γ) ⊢  
-}