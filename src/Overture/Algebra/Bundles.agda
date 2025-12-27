
module Overture.Algebra.Bundles where

open import Level using (suc; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Algebra.Core using (Op₂)
open import Overture.Algebra.Structures using (IsModalityRingoid)

record ModalityRingoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  4 _≈_
  infixl 5 _+_
  infixl 6 _*_
  infixl 7 _∧_
  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ
    _+_ : Op₂ Carrier
    _*_ : Op₂ Carrier
    _∧_ : Op₂ Carrier
    0# : Carrier
    1# : Carrier
    isRingoid : IsModalityRingoid _≈_ _+_ _*_ _∧_ 0# 1#
