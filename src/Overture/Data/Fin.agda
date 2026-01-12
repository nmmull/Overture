module Overture.Data.Fin where

open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Nat using (_+_; suc; zero)
open import Data.Nat.Properties using (+-suc; +-comm; +-identityʳ)
open import Relation.Binary.PropositionalEquality

shift : ∀ m p n → Fin (m + n) → Fin (m + (p + n))
shift m 0 n f = f
shift 0 (suc p) n f = suc (shift 0 p n f)
shift (suc m) (suc p) n zero = zero
shift (suc m) (suc p) n (suc f) = suc (shift m (suc p) n f)

-- shift' : ∀ m n p → Fin (m + n) → Fin (m + (p + n))
-- shift' zero n p i rewrite +-comm p n = i Fin.↑ˡ p
-- shift' (suc m) zero p zero
--   rewrite +-identityʳ p
--   rewrite +-comm (suc m) p = p Fin.↑ʳ zero
-- shift' (suc m) zero p (suc i) = suc (shift' m zero p i)
-- shift' (suc m) (suc n) p zero = zero
-- shift' (suc m) (suc n) p (suc i)
--   rewrite (+-suc p n)
--   rewrite (+-suc m (p + n))
--   rewrite (+-suc m n) = suc (shift' (suc m) n p i)

-- shift' : ∀ m n p → Fin (m + n) → Fin (m + (n + p))
-- shift' zero n p i = i Fin.↑ˡ p
-- shift' (suc m) zero p i
--   rewrite +-identityʳ m
--   rewrite +-comm (suc m) p = p Fin.↑ʳ i
-- shift' (suc m) (suc n) p zero = zero
-- shift' (suc m) (suc n) p (suc i)
--   rewrite (+-suc m (n + p))
--   rewrite (+-suc m n) = suc (shift' (suc m) n p i)

-- shift' : ∀ m n p → Fin (m + n) → Fin ((n + p) + m)
-- shift' zero n p i rewrite +-identityʳ (n + p) = i Fin.↑ˡ p
-- shift' (suc m) zero p i = {!!}
--   -- rewrite +-identityʳ m
--   -- rewrite +-comm (suc m) p = p Fin.↑ʳ i
-- shift' (suc m) (suc n) p zero = zero
-- shift' (suc m) (suc n) p (suc i) = {!!}
--   -- rewrite (+-suc m (n + p))
--   -- rewrite (+-suc m n) = suc (shift' (suc m) n p i)

open import Data.Fin public
