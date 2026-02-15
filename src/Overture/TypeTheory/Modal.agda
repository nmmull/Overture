open import Overture.Algebra.Bundles using (ModalityRingoid)

module Overture.TypeTheory.Modal {a ℓ} (M : ModalityRingoid a ℓ) where

open import Level using (Level; suc; _⊔_)
open import Algebra.Core using (Op₂)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; lookup)

open ModalityRingoid M

data ModExp : ℕ → Set (suc (a ⊔ ℓ))  where
  𝑝_ : ∀{n} → Carrier → ModExp n
  𝑚_ : ∀{n} → (x : Fin n) → ModExp n
  _+ᵉ_ : ∀{n} → Op₂ (ModExp n)
  _*ᵉ_ : ∀{n} → Op₂ (ModExp n)
  _∧ᵉ_ : ∀{n} → Op₂ (ModExp n)

eval : ∀ {n} → Vec Carrier n → ModExp n → Carrier
eval γ (𝑝 m) = m
eval γ (𝑚 x) = lookup γ x
eval γ (e₁ +ᵉ e₂) = (eval γ e₁) + (eval γ e₂)
eval γ (e₁ *ᵉ e₂) = (eval γ e₁) * (eval γ e₂)
eval γ (e₁ ∧ᵉ e₂) = (eval γ e₁) ∧ (eval γ e₂)
