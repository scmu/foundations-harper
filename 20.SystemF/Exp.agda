module Exp where

open import Data.Nat hiding (_*_) renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_; inject) renaming (inject₁ to injectFin)

open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.List 
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)

FName : Set
FName = String

FNames : Set
FNames = List FName

data Typ : ℕ → Set where
  bv : ∀ {n} → (i : Fin n) → Typ n
  fv : ∀ {n} → (x : FName) → Typ n 
  _⇒_ : ∀ {n} → Typ n → Typ n → Typ n
  Ȧ : ∀ {n} → Typ (suc n) → Typ n

data Exp : ℕ → ℕ → Set where
  bv : ∀ {m n} → (i : Fin n) → Exp m n
  fv : ∀ {m n} → (x : FName) → Exp m n
  ƛ : ∀ {m n} → Typ m → (e : Exp m (suc n)) → Exp m n
  _·_ : ∀ {m n} → (e₁ : Exp m n) → (e₂ : Exp m n) → Exp m n
  Λ : ∀ {m n} → (e : Exp (suc m) n) → Exp m n
  _⋆_ : ∀ {m n} → (e₁ : Exp m n) → Typ m → Exp m n
 
Expr : Set
Expr = Exp 0 0

-- ** Instantiation and Substitution For Types ** --

inject₁ : ∀ {m} → Typ m → Typ (suc m)
inject₁ (bv i) = bv (injectFin i)
inject₁ (fv x) = fv x
inject₁ (Ȧ e) = Ȧ (inject₁ e)
inject₁ (σ ⇒ τ) = inject₁ σ ⇒ inject₁ τ

[_↦_]₁ : ∀ m → Typ m → Typ (suc m) → Typ m
[ n ↦ t ]₁ (bv i) with n ≟ℕ toℕ i
... | yes _ = t
... | no  n≠i = bv (lower₁ i n≠i)
[ n ↦ t ]₁ (fv x) = fv x
[ n ↦ t ]₁ (Ȧ e) = Ȧ ([ suc n ↦ inject₁ t ]₁ e)
[ n ↦ t ]₁ (e₁ ⇒ e₂) = [ n ↦ t ]₁ e₁ ⇒ [ n ↦ t ]₁ e₂

inst₁ : Typ 0 → Typ 1 → Typ 0
inst₁ u = [ 0 ↦ u ]₁

instVar₁ : FName → Typ 1 → Typ 0
instVar₁ x = inst₁ (fv x)

[_↝_]₁ : ∀ {m} → FName → Typ m → Typ m → Typ m
[ x ↝ τ ]₁ (bv i) = bv i
[ x ↝ τ ]₁ (fv y) with x ≟S y
... | yes _ = τ
... | no  _ = fv y
[ x ↝ τ ]₁ (σ ⇒ γ) = [ x ↝ τ ]₁ σ ⇒ [ x ↝ τ ]₁ γ
[ x ↝ τ ]₁ (Ȧ e) = Ȧ ([ x ↝ inject₁ τ ]₁ e)


-- ** Instantiation and Substitution For Expressions ** --

inject : ∀ {m n} → Exp m n → Exp m (suc n)
inject (bv i) = bv (injectFin i)
inject (fv x) = fv x
inject (ƛ τ e) = ƛ τ (inject e)
inject (e₁ · e₂) = inject e₁ · inject e₂
inject (Λ e) = Λ (inject e)
inject (e ⋆ τ) = inject e ⋆ τ

injectτ : ∀ {m n} → Exp m n → Exp (suc m) n
injectτ (bv i) = bv i
injectτ (fv x) = fv x
injectτ (ƛ τ e) = ƛ (inject₁ τ) (injectτ e)
injectτ (e₁ · e₂) = injectτ e₁ · injectτ e₂
injectτ (Λ e) = Λ (injectτ e)
injectτ (e ⋆ τ) = injectτ e ⋆ inject₁ τ

-- open the outermost bound variable

[_↦_] : ∀ {m} n → Exp m n → Exp m (suc n) → Exp m n
[ n ↦ t ] (bv i) with n ≟ℕ toℕ i
... | yes _ = t
... | no  n≠i = bv (lower₁ i n≠i)
[ n ↦ t ] (fv x) = fv x
[ n ↦ t ] (ƛ τ e) = ƛ τ ([ suc n ↦ inject t ] e)
[ n ↦ t ] (e₁ · e₂) = [ n ↦ t ] e₁ · [ n ↦ t ] e₂
[ n ↦ t ] (Λ e) = Λ ([ n ↦ injectτ t ] e)
[ n ↦ t ] (e ⋆ τ) = [ n ↦ t ] e ⋆ τ

inst : ∀ {m} → Exp m 0 → Exp m 1 → Exp m 0
inst u = [ 0 ↦ u ]

instVar : ∀ {m} → FName → Exp m 1 → Exp m 0
instVar x = inst (fv x)

[_↦_]τ : ∀ m {n} → Typ m → Exp (suc m) n → Exp m n
[ m ↦ t ]τ (bv i) = bv i
[ m ↦ t ]τ (fv x) = fv x
[ m ↦ t ]τ (ƛ τ e) = ƛ ([ m ↦ t ]₁ τ) ([ m ↦ t ]τ e)
[ m ↦ t ]τ (e₁ · e₂) = [ m ↦ t ]τ e₁ · [ m ↦ t ]τ e₂
[ m ↦ t ]τ (Λ e) = Λ ([ suc m ↦ inject₁ t ]τ e)
[ m ↦ t ]τ (e ⋆ τ) = [ m ↦ t ]τ e ⋆ ([ m ↦ t ]₁ τ)

instτ : ∀ {n} → Typ 0 → Exp 1 n → Exp 0 n
instτ τ e = [ 0 ↦ τ ]τ e

instVarτ : ∀ {n} → FName → Exp 1 n → Exp 0 n
instVarτ x e = [ 0 ↦ fv x ]τ e
 
[_↝_] : ∀ {m n} → FName → Exp m n → Exp m n → Exp m n
[ x ↝ t ] (bv i) = bv i
[ x ↝ t ] (fv y) with x ≟S y
... | yes _ = t
... | no  _ = fv y
[ x ↝ t ] (ƛ τ e) = ƛ τ ([ x ↝ inject t ] e)
[ x ↝ t ] (e₁ · e₂) = [ x ↝ t ] e₁ · [ x ↝ t ] e₂
[ x ↝ t ] (Λ e) = Λ ([ x ↝ injectτ t ] e)
[ x ↝ t ] (e ⋆ τ) = [ x ↝ t ] e ⋆ τ

[_↝_]τ : ∀ {m n} → FName → Typ m → Exp m n → Exp m n
[ x ↝ τ ]τ (bv i) = bv i
[ x ↝ τ ]τ (fv y) = fv y
[ x ↝ τ ]τ (ƛ σ e) = ƛ ([ x ↝ τ ]₁ σ) ([ x ↝ τ ]τ e)
[ x ↝ τ ]τ (e₁ · e₂) = [ x ↝ τ ]τ e₁ · [ x ↝ τ ]τ e₂
[ x ↝ τ ]τ (Λ e) = Λ ([ x ↝ inject₁ τ ]τ e)
[ x ↝ τ ]τ (e ⋆ σ) = [ x ↝ τ ]τ e ⋆ [ x ↝ τ ]₁ σ

-- close a free variable to be the outermost bound variable

[_↤_] : ∀ {m} n → FName → Exp m n → Exp m (suc n)
[ n ↤ x ] (bv i) = bv (injectFin i)
[ n ↤ x ] (fv y) with x ≟S y
... | yes _ = bv (fromℕ n)
... | no  _ = fv y
[ n ↤ x ] (ƛ τ e) = ƛ τ ([ suc n ↤ x ] e)
[ n ↤ x ] (e₁ · e₂) = [ n ↤ x ] e₁ · [ n ↤ x ] e₂
[ n ↤ x ] (Λ e) = Λ ([ n ↤ x ] e)
[ n ↤ x ] (e ⋆ τ) = [ n ↤ x ] e ⋆ τ

abs : ∀ {m} → FName → Exp m 0 → Exp m 1
abs x = [ 0 ↤ x ]

fvars : ∀ {m n} → Exp m n → FNames
fvars (bv i) = []
fvars (fv x) = x ∷ []
fvars (ƛ x e) = fvars e
fvars (e₁ · e₂) = fvars e₁ ++ fvars e₂
fvars (Λ e) = fvars e
fvars (e ⋆ τ) = fvars e
