module Exp where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_; inject)
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.List 
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)

data Typ : Set where
  nat : Typ
  _⇒_ : Typ → Typ → Typ

FName : Set
FName = String

FNames : Set
FNames = List FName

data Exp : ℕ → Set where
  bv : ∀ {n} → (i : Fin n) → Exp n
  fv : ∀ {n} → (x : FName) → Exp n
  zero : ∀ {n} → Exp n
  suc  : ∀ {n} → (e : Exp n) → Exp n
  elimℕ : ∀ {n} → (e₀ : Exp n) → (e₁ : Exp (suc (suc n)))
          → (e : Exp n) → Exp n
  ƛ : ∀ {n} → Typ → (e : Exp (suc n)) → Exp n
  _·_ : ∀ {n} → (e₁ : Exp n) → (e₂ : Exp n) → Exp n

Expr : Set
Expr = Exp 0

private
 postulate i+1+j≡1+i+j : ∀ i j → i + suc j ≡ suc (i + j)

inject : ∀ {n} → Exp n → Exp (suc n)
inject (bv i) = bv (inject₁ i)
inject (fv x) = fv x
inject zero = zero
inject (suc e) = suc (inject e)
inject (elimℕ e₁ e₂ e) = elimℕ (inject e₁) (inject e₂) (inject e)
inject (ƛ τ e) = ƛ τ (inject e)
inject (e₁ · e₂) = inject e₁ · inject e₂


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
[ n ↦ t ] zero = zero
[ n ↦ t ] (suc e) = suc ([ n ↦ t ] e)
[ n ↦ t ] (elimℕ e₁ e₂ e) = 
  elimℕ ([ n ↦ t ] e₁) ([ suc (suc n) ↦ inject (inject t) ] e₂) ([ n ↦ t ] e)
[ n ↦ t ] (ƛ τ e) = ƛ τ ([ suc n ↦ inject t ] e)
[ n ↦ t ] (e₁ · e₂) = [ n ↦ t ] e₁ · [ n ↦ t ] e₂

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
[ n ↤ x ] zero = zero
[ n ↤ x ] (suc e) = suc ([ n ↤ x ] e)
[ n ↤ x ] (elimℕ e₁ e₂ e) = elimℕ ([ n ↤ x ] e₁) ([ suc (suc n) ↤ x ] e₂) ([ n ↤ x ] e)
[ n ↤ x ] (ƛ τ e) = ƛ τ ([ suc n ↤ x ] e)
[ n ↤ x ] (e₁ · e₂) = [ n ↤ x ] e₁ · [ n ↤ x ] e₂

abs : FName → Exp 0 → Exp 1
abs x = [ 0 ↤ x ]

[_↝_] : ∀ {n} → FName → Exp n → Exp n → Exp n
[ x ↝ t ] (bv i) = bv i
[ x ↝ t ] (fv y) with x ≟S y
... | yes _ = t
... | no  _ = fv y
[ x ↝ t ] zero = zero
[ x ↝ t ] (suc e) = suc ([ x ↝ t ] e)
[ x ↝ t ] (elimℕ e₁ e₂ e) =
   elimℕ ([ x ↝ t ] e₁) ([ x ↝ inject (inject t)] e₂) ([ x ↝ t ] e)
[ x ↝ t ] (ƛ τ e) = ƛ τ ([ x ↝ inject t ] e)
[ x ↝ t ] (e₁ · e₂) = [ x ↝ t ] e₁ · [ x ↝ t ] e₂

fvars : ∀ {n} → Exp n → FNames
fvars (bv i) = []
fvars (fv x) = x ∷ []
fvars zero = []
fvars (suc e) = fvars e
fvars (elimℕ e₁ e₂ e) = fvars e₁ ++ fvars e₂ ++ fvars e
fvars (ƛ x e) = fvars e
fvars (e₁ · e₂) = fvars e₁ ++ fvars e₂