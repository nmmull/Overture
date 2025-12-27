
module Overture.Data.Fin where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (_+_; suc)


shift : ∀ {n} m p → Fin (m + n) → Fin (m + (p + n))
shift m 0 f = f
shift 0 (suc p) f = suc (shift 0 p f)
shift (suc m) (suc p) zero = zero
shift (suc m) (suc p) (suc f) = suc (shift m (suc p) f)


open import Data.Fin public
