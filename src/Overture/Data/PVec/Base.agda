module Overture.Data.PVec.Base where

open import Level using (Level)
open import Data.Fin using (Fin; zero; suc; toℕ; opposite)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Unary using (Pred)

private
  variable
    ℓ : Level
    A : Set ℓ
    P Q : Pred ℕ ℓ
    m n : ℕ

infixr 5 _∷_

data PVec (P : Pred ℕ ℓ) : ℕ → Set ℓ where
  [] : PVec P zero
  _∷_ : P n → PVec P n → PVec P (suc n)

PVecExt : Pred ℕ ℓ → ℕ → ℕ → Set ℓ
PVecExt P m n = PVec (λ k → P (k + m)) n

------------------------------------------------------------------------
-- Basic operations

length : PVec P n → ℕ
length {n = n} _ = n

head : PVec P (suc n) → P n
head (x ∷ _) = x

tail : PVec P (suc n) → PVec P n
tail (_ ∷ xs) = xs

lookup : ∀ {P : Pred ℕ ℓ} → PVec P n → (i : Fin n) → P (toℕ (opposite i))
lookup {n = suc n} (x ∷ _) zero rewrite toℕ-fromℕ n = x
lookup (_ ∷ xs) (suc i) rewrite toℕ-inject₁ (opposite i) = lookup xs i

------------------------------------------------------------------------
-- Operations for transforming vectors

map : (∀ i → P i → Q i) → PVec P n → PVec Q n
map f [] = []
map {n = suc n} f (x ∷ xs) = f n x ∷ map f xs

-- Concatenation.

infixr 5 _++_

_++_ : PVecExt P n m → PVec P n → PVec P (m + n)
[] ++ v = v
(x ∷ u) ++ v = x ∷ (u ++ v)

------------------------------------------------------------------------
-- Operations for converting between vectors

toVec : PVec P n → Vec (∃[ i ] P i) n
toVec [] = []
toVec {n = suc n} (x ∷ xs) = (n , x) ∷ toVec xs

fromVec : Vec A n → PVec (λ _ → A) n
fromVec [] = []
fromVec (x ∷ xs) = x ∷ fromVec xs
