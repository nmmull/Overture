module Overture.Data.Fin.Properties where

open import Data.Fin using (Fin; zero; suc; toℕ; opposite)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality

private
  variable
    n : ℕ

toℕ-opposite : ∀ (i : Fin (suc n)) → toℕ i + toℕ (opposite i) ≡ n
toℕ-opposite {n = n} zero = toℕ-fromℕ n
toℕ-opposite {n = suc n} (suc i)
  rewrite toℕ-inject₁ (opposite i) =
  cong suc (toℕ-opposite i)

open import Data.Fin.Properties public
