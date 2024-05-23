open import Algebra.Bundles using (Semiring)

module Overture.Algebra.Properties.Semiring.Sum {a ℓ} (R : Semiring a ℓ) where

open import Data.Nat using (ℕ; zero; suc)
import Data.Fin as F
open import Data.Vec.Functional

open Semiring R
open import Algebra.Properties.Semiring.Sum R
open import Algebra.Properties.Semiring.Divisibility R
open import Relation.Binary.Reasoning.Setoid setoid

∣-sum : ∀ {n} d (v : Vector Carrier n) → (∀ i → d ∣ v i) → d ∣ sum v
∣-sum {zero} d v d∣v = 0# , eq where
  eq : 0# * d ≈ sum v
  eq =
    begin
      0# * d
    ≈⟨ zeroˡ d ⟩
      0#
    ≈⟨ refl ⟩
      sum v
    ∎
∣-sum {suc n} d v d∣v with d∣v F.zero | ∣-sum d (tail v) (λ i → d∣v (F.suc i))
... | k₁ , k₁*d≈head | k₂ , k₂*d≈∑tail = (k₁ + k₂) , eq where
  eq : (k₁ + k₂) * d ≈ sum v
  eq =
    begin
      (k₁ + k₂) * d
    ≈⟨ distribʳ d k₁ k₂ ⟩
      k₁ * d + k₂ * d
    ≈⟨ +-congʳ k₁*d≈head ⟩
      head v + k₂ * d
    ≈⟨ +-congˡ k₂*d≈∑tail ⟩
      head v + sum (tail v)
    ≈⟨ refl ⟩
      sum v
    ∎
