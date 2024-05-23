module Overture.Data.Nat.Sum where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility
open import Data.Vec.Functional

open import Algebra.Bundles using (Semiring)

open Semiring +-*-semiring
open import Algebra.Properties.Semiring.Sum +-*-semiring
open import Algebra.Properties.Semiring.Divisibility +-*-semiring renaming (_∣_ to _∣̂_)
open import Overture.Algebra.Properties.Semiring.Sum +-*-semiring renaming (∣-sum to ∣̂-sum)

∣-sum : ∀ {n} d (v : Vector ℕ n) → (∀ i → d ∣ v i) → d ∣ sum v
∣-sum d v d∣v =  ∣̂-to-∣ d (sum v) (∣̂-sum d v (λ i → ∣-to-∣̂ d (v i) (d∣v i)))  where
  ∣-to-∣̂ : ∀ m n → m ∣ n → m ∣̂ n
  ∣-to-∣̂ m n (divides k n≡k*m) = k , sym n≡k*m

  ∣̂-to-∣ : ∀ m n → m ∣̂ n → m ∣ n
  ∣̂-to-∣ m n (k , k*m≡n) = divides k (sym k*m≡n)
