
open import Relation.Binary.Core using (Rel)
open import Algebra.Core using (Op₂)

module Overture.Algebra.Structures
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Level using (suc; _⊔_)
open import Algebra.Structures _≈_ using (IsCommutativeMonoid; IsMonoid)
open import Algebra.Definitions _≈_ using (_DistributesOverˡ_; _DistributesOverʳ_; Zero)
open import Algebra.Lattice.Structures _≈_ using (IsSemilattice)

record IsModalityRingoid (+ * ∧ : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    +-isCommutativeMonoid : IsCommutativeMonoid + 0#
    *-isMonoid : IsMonoid * 1#
    ∧-isSemilattice : IsSemilattice ∧
    *-distrib-+ : * DistributesOverˡ +
    *-distrib-∧ : * DistributesOverˡ ∧
    +-distrib-∧ : + DistributesOverʳ ∧
    zero : Zero 0# *
