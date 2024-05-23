module Overture.Data.Nat.Binomial where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Combinatorics
open import Data.Fin using (toℕ)

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Algebra.Bundles using (CommutativeSemiring; Semiring)
open CommutativeSemiring +-*-commutativeSemiring using (semiring) renaming (_+_ to _+̂_; _*_ to _*̂_)
import Algebra.Properties.CommutativeSemiring.Binomial +-*-commutativeSemiring as Binomial
open import Algebra.Properties.Semiring.Sum semiring
open import Algebra.Properties.Semiring.Mult semiring
open import Algebra.Properties.Semiring.Exp semiring renaming ( _^_ to _^̂_ )

binomialTheorem : ∀ n x y → (x + y) ^ n ≡ ∑[ k ≤ n ] ((n C toℕ k) * (x ^ toℕ k * y ^ (n ∸ toℕ k)))
binomialTheorem n x y =
  begin
    (x + y) ^ n
  ≡⟨ ^-to-^̂ (x + y) n ⟩
    (x + y) ^̂ n
  ≡⟨ Binomial.theorem n x y ⟩
    ∑[ k ≤ n ] ((n C toℕ k) × (x ^̂ toℕ k * y ^̂ (n ∸ toℕ k)))
  ≡⟨ sum-cong-≗ {suc n} (λ k → sym (*-to-× (n C toℕ k) (x ^̂ toℕ k * y ^̂ (n ∸ toℕ k)))) ⟩
    ∑[ k ≤ n ] ((n C toℕ k) * (x ^̂ toℕ k * y ^̂ (n ∸ toℕ k)))
  ≡⟨ sum-cong-≗ {suc n} (λ k → cong₂ (λ a b → (n C toℕ k) * (a * b)) (sym (^-to-^̂ x (toℕ k))) (sym (^-to-^̂ y (n ∸ toℕ k)))) ⟩
    ∑[ k ≤ n ] ((n C toℕ k) * (x ^ toℕ k * y ^ (n ∸ toℕ k)))
  ∎
  where
    ^-to-^̂ : ∀ m n → m ^ n ≡ m ^̂ n
    ^-to-^̂ m zero = refl
    ^-to-^̂ m (suc n) = cong (m *_) (^-to-^̂ m n)

    *-to-× : ∀ m n → m * n ≡ m × n
    *-to-× zero n = refl
    *-to-× (suc m) n = cong (n +_) (*-to-× m n)

binomialTheorem-suc : ∀ n x → (suc x) ^ n ≡ ∑[ k ≤ n ] ((n C toℕ k) * x ^ toℕ k)
binomialTheorem-suc n x =
  begin
    (suc x) ^ n
  ≡⟨⟩
    (1 + x) ^ n
  ≡⟨ cong (_^ n) (+-comm 1 x) ⟩
    (x + 1) ^ n
  ≡⟨ binomialTheorem n x 1 ⟩
    ∑[ k ≤ n ] ((n C toℕ k) * (x ^ toℕ k * 1 ^ (n ∸ toℕ k)))
  ≡⟨ sum-cong-≗ {suc n} (λ k → cong (λ a → (n C toℕ k) * (x ^ toℕ k * a)) (^-zeroˡ (n ∸ toℕ k))) ⟩
    ∑[ k ≤ n ] ((n C toℕ k) * (x ^ toℕ k * 1))
  ≡⟨ sum-cong-≗ {suc n} (λ k → cong (λ a → (n C toℕ k) * a) (*-identityʳ (x ^ toℕ k))) ⟩
    ∑[ k ≤ n ] ((n C toℕ k) * x ^ toℕ k)
  ∎
