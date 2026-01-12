module Overture.Data.Fin.Properties where

open import Data.Fin using (Fin; zero; suc; toℕ; opposite)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

private
  variable
    n : ℕ

toℕ-opposite : ∀ (i : Fin (suc n)) → toℕ i + toℕ (opposite i) ≡ n
toℕ-opposite {n = n} zero = toℕ-fromℕ n
toℕ-opposite {n = suc n} (suc i)
  rewrite toℕ-inject₁ (opposite i) =
  cong suc (toℕ-opposite i)

toℕ-suc-opposite : ∀ (i : Fin n) → toℕ i + suc (toℕ (opposite i)) ≡ n
toℕ-suc-opposite {n = suc n} i =
  begin
    toℕ i + suc (toℕ (opposite i))
  ≡⟨ +-suc (toℕ i) (toℕ (opposite i)) ⟩
    suc (toℕ i + toℕ (opposite i))
  ≡⟨ cong suc (toℕ-opposite i) ⟩
    suc n
  ∎

open import Data.Fin.Properties public
