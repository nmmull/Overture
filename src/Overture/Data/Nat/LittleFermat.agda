module Overture.Data.Nat.LittleFermat where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Primality
open import Data.Nat.Divisibility
open import Data.Nat.DivMod
open import Data.Nat.Combinatorics

open import Data.Fin as F using (Fin; toℕ; fromℕ; inject₁)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ; toℕ-inject₁)
open import Data.Vec.Functional
open import Data.Product using (∃-syntax; _,_)

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Algebra.Properties.Semiring.Sum +-*-semiring

open import Overture.Data.Nat.Sum
open import Overture.Data.Nat.Properties
open import Overture.Data.Nat.Binomial

private
  prime⇒p∣∑ : ∀ {p} a → Prime p → p ∣ ∑[ i < pred p ] ((p C suc (toℕ i)) * a ^ suc (toℕ i))
  prime⇒p∣∑ {p} a prime[p] = ∣-sum p v p∣v  where
    v : Vector ℕ (pred p)
    v i = (p C suc (toℕ i)) * a ^ suc (toℕ i)

    i<p : ∀ (i : Fin (pred p)) → suc (toℕ i) < p
    i<p i rewrite sym (suc-pred p ⦃ prime⇒nonZero prime[p] ⦄) = s<s (toℕ<n i)

    p∣v : ∀ i → p ∣ (p C suc (toℕ i)) * a ^ suc (toℕ i)
    p∣v i = ∣m⇒∣m*n (a ^ suc (toℕ i)) (prime⇒p∣pCk prime[p] (i<p i))

hs-dream : ∀ {p} a → Prime p → ∃[ k ] (suc a) ^ p ≡ suc (a ^ p) + k * p
hs-dream {p} a prime[p] with prime⇒p∣∑ a prime[p]
... | divides k ∑≡k*p = k , eq where
  v : Fin (suc (pred p)) → ℕ
  v i = (p C suc (toℕ i)) * a ^ suc (toℕ i)

  e = suc (toℕ (fromℕ (pred p)))

  e≡p : e ≡ p
  e≡p =
    begin
      e
    ≡⟨ cong suc (toℕ-fromℕ (pred p)) ⟩
      suc (pred p)
    ≡⟨ suc-pred p ⦃ prime⇒nonZero prime[p] ⦄ ⟩
      p
    ∎

  lst≡a^p : (p C e) * a ^ e ≡ a ^ p
  lst≡a^p =
    begin
      (p C e) * a ^ e
    ≡⟨ cong (λ x → (p C x) * a ^ x) e≡p ⟩
      (p C p) * a ^ p
    ≡⟨ cong (_* a ^ p) (nCn≡1 p) ⟩
      1 * a ^ p
    ≡⟨ *-identityˡ (a ^ p) ⟩
      a ^ p
    ∎

  eq : (1 + a) ^ p ≡ 1 + a ^ p + k * p
  eq =
    begin
      (1 + a) ^ p
    ≡⟨ binomialTheorem-suc p a ⟩
      ∑[ i ≤ p ] ((p C toℕ i) * a ^ toℕ i)
    ≡⟨⟩
      1 + ∑[ i < p ] ((p C suc (toℕ i)) * a ^ suc (toℕ i))
    ≡⟨ cong (λ x → 1 + ∑[ i < x ] ((p C suc (toℕ i)) * a ^ suc (toℕ i))) (sym (suc-pred p ⦃ prime⇒nonZero prime[p] ⦄)) ⟩
      1 + ∑[ i < suc (pred p) ] ((p C suc (toℕ i)) * a ^ suc (toℕ i))
    ≡⟨⟩
      1 + sum v
    ≡⟨ cong (1 +_) (sum-init-last v) ⟩
      1 + (sum (init v) + last v)
    ≡⟨ cong (1 +_) (+-comm (sum (init v)) (last v)) ⟩
      1 + (last v + sum (init v))
    ≡⟨ sym (+-assoc 1 (last v) (sum (init v))) ⟩
      1 + last v + sum (init v)
    ≡⟨ cong (λ x → 1 + x + sum (init v)) lst≡a^p ⟩
      1 + a ^ p + sum (init v)
    ≡⟨ cong (λ x → 1 + a ^ p + x) (sum-cong-≗ {pred p} (λ i → cong (λ x → (p C suc x) * a ^ suc x) (toℕ-inject₁ i))) ⟩
      1 + a ^ p + ∑[ i < pred p ] ((p C suc (toℕ i)) * a ^ suc (toℕ i))
    ≡⟨ cong (λ x → 1 + a ^ p + x) ∑≡k*p ⟩
      1 + a ^ p + k * p
    ∎

theorem : ∀ {p} a → Prime p → ∃[ k ] a ^ p ≡ a + k * p
theorem zero is-prime = 0 , nonZero⇒0^n≡0 ⦃ prime⇒nonZero is-prime ⦄
theorem {p} (suc a) is-prime with theorem a is-prime | hs-dream a is-prime
theorem {p} (suc a) is-prime | k₁ , prf₁ | k₂ , prf₂ = k₁ + k₂ , eq where
  eq : (suc a) ^ p ≡ suc a + (k₁ + k₂) * p
  eq =
    begin
      (suc a) ^ p
    ≡⟨ prf₂ ⟩
      suc (a ^ p) + k₂ * p
    ≡⟨ cong (λ x → suc x + k₂ * p) prf₁ ⟩
      suc (a + k₁ * p) + k₂ * p
    ≡⟨⟩
      suc a + k₁ * p + k₂ * p
    ≡⟨ +-assoc (suc a) (k₁ * p) (k₂ * p) ⟩
      suc a + (k₁ * p + k₂ * p)
    ≡⟨ cong (λ x → suc a + x) (sym (*-distribʳ-+ p k₁ k₂)) ⟩
      suc a + (k₁ + k₂) * p
    ∎
