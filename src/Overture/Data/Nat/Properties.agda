module Overture.Data.Nat.Properties where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Combinatorics
open import Data.Nat.Primality
open import Data.Nat.Divisibility
open import Data.Nat.DivMod

open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Empty using (⊥-elim)

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

nonZero⇒0^n≡0 : ∀ {n} → .⦃ NonZero n ⦄ → 0 ^ n ≡ 0
nonZero⇒0^n≡0 {suc n} = refl

1+m<n⇒m<n : ∀ {m n} → suc m < n → m < n
1+m<n⇒m<n {m} {n} 1+m<n = ≤-trans (n≤1+n (suc m)) 1+m<n

nonZero⇒n∸k<n : ∀ n k → .⦃ NonZero n ⦄ → .⦃ NonZero k ⦄ → n ∸ k < n
nonZero⇒n∸k<n (suc n) (suc k) = s≤s (m∸n≤m n k)

nonZero⇒n∣n! : ∀{n} → .⦃ NonZero n ⦄ → n ∣ (n !)
nonZero⇒n∣n! {suc n} = divides (n !) (*-comm (suc n) (n !))

nonTrivial⇒n∤1 : ∀ n → .⦃ NonTrivial n ⦄ → n ∤ 1
nonTrivial⇒n∤1 n = >⇒∤ (nonTrivial⇒n>1 n)

prime⇒p∤k! : ∀{p k} → Prime p → k < p → p ∤ k !
prime⇒p∤k! {p} {zero} prime[p] k<p p∣1 = nonTrivial⇒n∤1 p p∣1
prime⇒p∤k! {p} {suc k} prime[p] [1+k]<p p∣[1+k]! with euclidsLemma (suc k) (k !) prime[p] p∣[1+k]!
... | inj₁ p∣1+k = >⇒∤ [1+k]<p p∣1+k
... | inj₂ p∣k! = prime⇒p∤k! prime[p] (1+m<n⇒m<n [1+k]<p) p∣k!

n!≡nCk*k!*[n∸k]! : ∀{n k} → k ≤ n → n ! ≡ (n C k) * k ! * (n ∸ k) !
n!≡nCk*k!*[n∸k]! {n} {k} k≤n = sym eq where
  eq =
    begin
      (n C k) * k ! * (n ∸ k) !
    ≡⟨ *-assoc (n C k) (k !) ((n ∸ k) !) ⟩
      (n C k) * (k ! * (n ∸ k) !)
    ≡⟨ cong (_* (k ! * (n ∸ k) !)) (nCk≡n!/k![n-k]! k≤n) ⟩
      (n ! / (k ! * (n ∸ k) !)) {{k !* (n ∸ k) !≢0}} * (k ! * (n ∸ k) !)
    ≡⟨ m/n*n≡m {{k !* (n ∸ k) !≢0}} (k![n∸k]!∣n! k≤n) ⟩
      n !
    ∎

prime⇒p∣pCk : ∀{p k} → Prime p → .⦃ NonZero k ⦄ → k < p → p ∣ (p C k)
prime⇒p∣pCk {p} {k} prime[p] k<p = p∣pCk where
  p∣pCk*k!*[n∸k]! : p ∣ (p C k) * k ! * (p ∸ k) !
  p∣pCk*k!*[n∸k]! rewrite (sym (n!≡nCk*k!*[n∸k]! (<⇒≤ k<p))) = nonZero⇒n∣n! ⦃ prime⇒nonZero prime[p] ⦄

  p∣pCk*k! : p ∣ (p C k) * k !
  p∣pCk*k! with euclidsLemma ((p C k) * k !) ((p ∸ k) !) prime[p] p∣pCk*k!*[n∸k]!
  ... | inj₁ prf = prf
  ... | inj₂ p∣[p-k]! = ⊥-elim (prime⇒p∤k! prime[p] (nonZero⇒n∸k<n p k ⦃ prime⇒nonZero prime[p] ⦄) p∣[p-k]!)

  p∣pCk : p ∣ p C k
  p∣pCk with euclidsLemma (p C k) (k !) prime[p] p∣pCk*k!
  ... | inj₁ prf = prf
  ... | inj₂ p∣k! = ⊥-elim (prime⇒p∤k! prime[p] k<p p∣k!)

∃[k]a≡b+kc⇒a%c≡b%c : ∀ a b c .⦃ _ : NonZero c ⦄ → ∃[ k ] (a ≡ b + k * c) → a % c ≡ b % c
∃[k]a≡b+kc⇒a%c≡b%c a b c (k , eq) =
  begin
    a % c
  ≡⟨ cong (_% c) eq ⟩
    (b + k * c) % c
  ≡⟨ [m+kn]%n≡m%n b k c ⟩
    b % c
  ∎
