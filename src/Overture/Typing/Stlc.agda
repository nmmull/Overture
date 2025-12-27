module Overture.Typing.Stlc where

open import Overture.Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Substitution using (Sub)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (inj₁; inj₂; _⊎_; [_,_])
open import Data.Vec as Vec using (Vec; []; _∷_; _++_; lookup; allFin)
open import Overture.Data.Vec.Properties using (lookup-map; lookup-shift; lookup-allFin)
open import Relation.Binary.PropositionalEquality hiding (subst; [_])
open import Relation.Nullary.Decidable using (Dec; yes; no)

data Expr (n : ℕ) : Set where
  𝑣 : Fin n -> Expr n
  λ̂ : Expr (suc n) → Expr n
  _·_ : Expr n → Expr n → Expr n

shift : ∀ {n} m p → Expr (m + n) → Expr (m + (p + n))
shift m p (𝑣 i) = 𝑣 (Fin.shift m p i)
shift m p (λ̂ e) = λ̂ (shift (suc m) p e)
shift m p (e₁ · e₂) = (shift m p e₁) · (shift m p e₂)

inject₁ : ∀ {n} → Expr n → Expr (suc n)
inject₁ = shift 0 1

_/_ : ∀ {m n} → Expr m → Sub Expr m n → Expr n
𝑣 i / ρ = lookup ρ i
λ̂ e / ρ = λ̂ (e / (𝑣 zero ∷ Vec.map inject₁ ρ))
(e₁ · e₂) / ρ = (e₁ / ρ) · (e₂ / ρ)

vars : {n : ℕ} → Sub Expr n n
vars {n} = Vec.map 𝑣 (allFin n)

lookup-vars : ∀ {n} (i : Fin n) → lookup vars i ≡ 𝑣 i
lookup-vars {n} i
  rewrite lookup-map i 𝑣 (allFin n)
  rewrite lookup-allFin i = refl

_/⁰_ : ∀ {n} → Expr (suc n) → Expr n → Expr n
_/⁰_ {n} e₁ e₂ = e₁ / (e₂ ∷ vars)

infix 5 _⟶_
data _⟶_ {n : ℕ} : Expr n → Expr n → Set where
  β-red : (e₁ : Expr (suc n)) → (e₂ : Expr n) →
    (λ̂ e₁) · e₂ ⟶ e₁ /⁰ e₂
  λ̂-red : ∀ {e₁ e₂} →
    e₁ ⟶ e₂ →
    λ̂ e₁ ⟶ λ̂ e₂
  ·ˡ-red : ∀ {e₁ e₂ e} →
    e₁ ⟶ e₂ →
    e₁ · e ⟶ e₂ · e
  ·ʳ-red : ∀ {e₁ e₂ e} →
    e₁ ⟶ e₂ →
    e · e₁ ⟶ e · e₂

infixr 25 _→̂_
data Type : Set where
  ⊥ : Type
  _→̂_ : Type → Type → Type

Ctxt : ℕ → Set
Ctxt n = Vec Type n

data _⊢_⦂_ : ∀ {n} → Ctxt n → Expr n → Type → Set where
  start :
    ∀ {n} {Γ : Ctxt n} (i : Fin n) →
    Γ ⊢ 𝑣 i ⦂ lookup Γ i
  abstr :
    ∀ {n e t₁ t₂} {Γ : Ctxt n} →
    (t₁ ∷ Γ) ⊢ e ⦂ t₂ →
    Γ ⊢ λ̂ e ⦂ t₁ →̂ t₂
  app :
    ∀ {n e₁ e₂ t₁ t₂} {Γ : Ctxt n} →
    Γ ⊢ e₁ ⦂ t₁ →̂ t₂ →
    Γ ⊢ e₂ ⦂ t₁ →
    Γ ⊢ e₁ · e₂ ⦂ t₂

module Properties where
  progress :
    ∀ {n} {Γ : Ctxt n} {e₁ : Expr n} {τ} →
    Γ ⊢ e₁ ⦂ τ →
    Dec (∃[ e₂ ] (e₁ ⟶ e₂))
  progress (start i) = no λ ()
  progress (abstr Γx⊢e) with progress Γx⊢e
  ... | yes (e' , e→e') = yes (λ̂ e' , λ̂-red e→e')
  ... | no ¬e→ = no λ (_ , λe→) → ¬e→ (lemma λe→)  where
    lemma :
      ∀ {n} {e₁ : Expr (suc n)} {e₂ : Expr n} →
      (λ̂ e₁) ⟶ e₂ →
      ∃[ e ] (e₁ ⟶ e)
    lemma (λ̂-red {e₂ = e} e₁→e) = e , e₁→e
  progress (app Γ⊢e₁ Γ⊢e₂) with progress Γ⊢e₁
  progress (app {e₂ = e₂} Γ⊢e₁ Γ⊢e₂)
    | yes (e' , e₁→e') = yes (e' · e₂ , ·ˡ-red e₁→e')
  progress (app Γ⊢e₁ Γ⊢e₂)
    | no _ with progress Γ⊢e₂
  progress (app {e₁ = e₁} Γ⊢e₁ Γ⊢e₂)
    | no _
    | yes (e' , e₂→e') = yes (e₁ · e' , ·ʳ-red e₂→e')
  progress {Γ = _} {𝑣 i · _} (app Γ⊢e₁ Γ⊢e₂)
    | no _
    | no ¬e₂→ = no λ (_ , ve→) → ¬e₂→ (lemma ve→) where
      lemma :
        ∀ {n} {e₁ e₂ : Expr n} {i : Fin n} →
        (𝑣 i · e₁) ⟶ e₂ →
        ∃[ e ] (e₁ ⟶ e)
      lemma (·ʳ-red {e₂ = e} e₁→e) = e , e₁→e
  progress {e₁ = λ̂ e₁ · e₂} (app Γ⊢e₁ Γ⊢e₂)
    | no _
    | no _ = yes (e₁ /⁰ e₂ , β-red e₁ e₂)
  progress {e₁ = (e₁ · e₂) · e₃} (app Γ⊢e₁e₂ Γ⊢e₃)
    | no ¬e₁e₂→
    | no ¬e₃→ =
      no λ ∃e₁e₂e₃→ → [ ¬e₁e₂→ , ¬e₃→ ] (lemma ∃e₁e₂e₃→) where
        lemma :
          ∀ {n} {e₁ e₂ e₃ : Expr n} →
          ∃[ e ] ((e₁ · e₂) · e₃ ⟶ e) →
          ∃[ e ] ((e₁ · e₂) ⟶ e) ⊎ ∃[ e ] (e₃ ⟶ e)
        lemma ((e · _) , ·ˡ-red e₁e₂→e) = inj₁ (e , e₁e₂→e)
        lemma (((_ · _) · e) , ·ʳ-red e₃→e) = inj₂ (e , e₃→e)

  thinning :
    ∀ {m n} {Δ : Ctxt m} {Γ : Ctxt n} {e τ τ'} →
    (Δ ++ Γ) ⊢ e ⦂ τ →
    (Δ ++ τ' ∷ Γ) ⊢ shift m 1 e ⦂ τ
  thinning {m = m} {Δ = Δ} {Γ = Γ} {τ' = τ'} (start i)
    rewrite lookup-shift τ' Δ Γ i = start (Fin.shift m 1 i)
  thinning {Δ = Δ} {τ = t₁ →̂ _} (abstr ΔΓ⊢e) = abstr (thinning {Δ = t₁ ∷ Δ} ΔΓ⊢e)
  thinning (app ΔΓ⊢e₁ ΔΓ⊢e₂) = app (thinning ΔΓ⊢e₁) (thinning ΔΓ⊢e₂)

  weakening :
    ∀ {n} {Γ : Ctxt n} {e τ τ'} →
    Γ ⊢ e ⦂ τ →
    (τ' ∷ Γ) ⊢ inject₁ e ⦂ τ
  weakening = thinning {Δ = []}

  substitution :
    ∀ {m n} {Γ : Ctxt n} {Δ : Ctxt m} {e τ ρ} →
    (∀ (i : Fin n) → Δ ⊢ lookup ρ i ⦂ lookup Γ i) →
    Γ ⊢ e ⦂ τ →
    Δ ⊢ e / ρ ⦂ τ
  substitution Γ⊢ρ (start i) = Γ⊢ρ i
  substitution {_} {n} {Γ} {Δ} {_} {τ} {ρ} Γ⊢ρ (abstr Γx⊢e) =
    abstr (substitution lemma Γx⊢e) where
      lemma :
        ∀ {τ} (i : Fin (suc n)) →
        (τ ∷ Δ) ⊢ lookup (𝑣 zero ∷ Vec.map inject₁ ρ) i ⦂ lookup (τ ∷ Γ) i
      lemma zero = start zero
      lemma (suc i) rewrite lookup-map i inject₁ ρ = weakening (Γ⊢ρ i)
  substitution Γ⊢ρ (app Γ⊢e₁ Γ⊢e₂) =
    app (substitution Γ⊢ρ Γ⊢e₁) (substitution Γ⊢ρ Γ⊢e₂)

  substitution₁ :
    ∀ {n} {Γ : Ctxt n} {e₁ : Expr (suc n)} {e₂ : Expr n} {τ₁ τ₂} →
    (τ₂ ∷ Γ) ⊢ e₁ ⦂ τ₁ →
    Γ ⊢ e₂ ⦂ τ₂ →
    Γ ⊢ e₁ /⁰ e₂ ⦂ τ₁
  substitution₁ {n} {Γ} {e₁} {e₂} {τ₁} {τ₂} Γx⊢e₁ Γ⊢e₂ = substitution lemma Γx⊢e₁ where
    lemma : ∀ (i : Fin (suc n)) → Γ ⊢ lookup (e₂ ∷ vars) i ⦂ lookup (τ₂ ∷ Γ) i
    lemma zero = Γ⊢e₂
    lemma (suc i) rewrite (lookup-vars i) = start i

  preservation :
    ∀ {n} {Γ : Ctxt n} {e₁ e₂ : Expr n} {τ} →
    e₁ ⟶ e₂ →
    Γ ⊢ e₁ ⦂ τ →
    Γ ⊢ e₂ ⦂ τ
  preservation {n} {Γ} {τ} (β-red e₁ e₂) (app (abstr Γx⊢e₁) Γ⊢e₂) = substitution₁ Γx⊢e₁ Γ⊢e₂
  preservation (λ̂-red e₁→e₂) (abstr Γx⊢e) = abstr (preservation e₁→e₂ Γx⊢e)
  preservation (·ˡ-red e₁→e₂) (app Γ⊢e₁ Γ⊢e₂) = app (preservation e₁→e₂ Γ⊢e₁) Γ⊢e₂
  preservation (·ʳ-red e₁→e₂) (app Γ⊢e₁ Γ⊢e₂) = app Γ⊢e₁ (preservation e₁→e₂ Γ⊢e₂)
