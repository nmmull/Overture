open import Axiom.Extensionality.Propositional using (Extensionality)

module Overture.Algebra.CategoryTheory.Kan
  (extensionality : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Level using (Level; suc; _⊔_)
open import Overture.Algebra.CategoryTheory.Functor as Functor using (Functor)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Overture.Algebra.CategoryTheory.NaturalTransformation using (_⇒_; _∘F_; _∘η_)

open Functor.Functor {{...}} public

private
  variable
    ℓ ℓ′ ℓ′′ : Level

Ran :
  (K : Set ℓ → Set ℓ′) →
  (D : Set ℓ → Set ℓ′′) →
  Set ℓ′ → Set (suc ℓ ⊔ ℓ′ ⊔ ℓ′′)
Ran K D A = ∀ I → (A → K I) → D I

functor : ∀ {K D : Set ℓ → Set ℓ′} → Functor (Ran K D)
functor = record
  { _<$>_ = λ f ran → λ I h → ran I (λ a → h (f a))
  ; isFunctor = record
      { identity = refl
      ; composition = refl
      }
  }

σ :
  {K : Set ℓ → Set ℓ′}
  {D : Set ℓ → Set (suc ℓ ⊔ ℓ′)}
  {F' : Set ℓ′ → Set (suc ℓ ⊔ ℓ′)} →
  {{isFunctor : Functor F'}} →
  (ϵ' : (F' ∘ K) ⇒ D) →
  F' ⇒ (Ran K D)
σ ϵ' _ x I g = ϵ' I (g <$> x)

ϵ :
  {K : Set ℓ → Set ℓ′}
  {D : Set ℓ → Set (suc ℓ ⊔ ℓ′)} →
  (Ran K D ∘ K) ⇒ D
ϵ A g = g A id

ϵ∘σK≡ϵ' :
  {K : Set ℓ → Set ℓ′}
  {D : Set ℓ → Set (suc ℓ ⊔ ℓ′)}
  {F' : Set ℓ′ → Set (suc ℓ ⊔ ℓ′)}
  {A : Set ℓ}
  {{isFunctor : Functor F'}} →
  (ϵ' : (F' ∘ K) ⇒ D) →
  ϵ ∘η (σ ϵ' ∘F K) ≡ ϵ'
ϵ∘σK≡ϵ' {K = K} ϵ' =
   extensionality λ A →
   extensionality λ x →
   begin
     (ϵ ∘η (σ ϵ' ∘F K)) A x
   ≡⟨ refl ⟩
     ϵ A (λ I g → ϵ' I (g <$> x))
   ≡⟨ refl ⟩
     (λ I g → ϵ' I (g <$> x)) A id
   ≡⟨ refl ⟩
     ϵ' A (id <$> x)
   ≡⟨ cong (λ y → ϵ' A y) identity ⟩
     ϵ' A x
   ∎
