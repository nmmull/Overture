module Overture.Data.Vec.Properties where

open import Level using (Level)
open import Overture.Data.Fin using (Fin; zero; suc; shift)
open import Data.Nat using (ℕ; _+_)
open import Data.Vec using (Vec; []; _∷_; lookup; _++_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

private
  variable
    ℓ : Level
    A : Set ℓ
    m n : ℕ

lookup-shift :
  (x : A)
  (u : Vec A m)
  (v : Vec A n)
  (i : Fin (m + n)) →
  lookup (u ++ (x ∷ v)) (shift m 1 i) ≡ lookup (u ++ v) i
lookup-shift x [] v i = refl
lookup-shift x (_ ∷ _) _ zero = refl
lookup-shift x (_ ∷ xs) v (suc i) = lookup-shift x xs v i

open import Data.Vec.Properties public
