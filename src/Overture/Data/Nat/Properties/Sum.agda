module Overture.Data.Nat.Properties.Sum where

open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Nat.Properties using (+-0-monoid; *-zeroʳ; *-distribˡ-+; *-comm)
open import Data.Vec.Functional using (Vector; head; tail; map)
open import Data.Vec.Functional.Properties using (map-cong)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

open import Algebra.Bundles using (Monoid)
open Monoid +-0-monoid using (rawMonoid)
open import Algebra.Definitions.RawMonoid rawMonoid using (sum)
open import Algebra.Properties.Monoid.Sum +-0-monoid using (sum-cong-≗)

*-distribˡ-sum : ∀ {n} a (v : Vector ℕ n) → a * sum v ≡ sum (map (_*_ a) v)
*-distribˡ-sum {0} a v =
  begin
    a * sum v              ≡⟨⟩
    a * 0                  ≡⟨ *-zeroʳ a ⟩
    0                      ≡⟨⟩
    sum (map (_*_ a) v)
  ∎
*-distribˡ-sum {suc n} a v =
  begin
    a * sum v                                ≡⟨⟩
    a * (head v + sum (tail v))              ≡⟨ *-distribˡ-+ a (head v) (sum (tail v)) ⟩
    a * head v + a * sum (tail v)            ≡⟨ cong (_+_ (a * head v)) (*-distribˡ-sum a (tail v))  ⟩
    a * head v + sum (map (_*_ a) (tail v))  ≡⟨⟩
    sum (map (_*_ a) v)
  ∎

*-distribʳ-sum : ∀ {n} a (v : Vector ℕ n) → sum v * a ≡ sum (map (λ x → x * a) v)
*-distribʳ-sum {n} a v =
  begin
    sum v * a                  ≡⟨ *-comm (sum v) a ⟩
    a * sum v                  ≡⟨ *-distribˡ-sum a v ⟩
    sum (map (_*_ a) v)        ≡⟨ sum-cong-≗ (map-cong {f = (_*_ a)} {g = (λ x → x * a)} (λ k → *-comm a k) v) ⟩
    sum (map (λ x → x * a) v)
  ∎
