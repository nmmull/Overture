module Overture.CompTheory.PrimRec where

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties using (+-comm)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

private
  variable
    m n : ℕ

data Expr : ℕ → Set where
  zero : Expr 0
  zero₁ : Expr 1
  suc : Expr 1
  proj : (i : Fin n) → Expr n
  comp : (f : Expr m) → (gs : Vec (Expr n) m) -> Expr n
  rec : Expr n → Expr (suc n) → Expr (suc n)

eval : Expr n → Vec ℕ n → ℕ
eval-vec : Vec (Expr m) n → Vec ℕ m → Vec ℕ n

eval zero _ = 0
eval zero₁ (_ ∷ []) = 0
eval suc (n ∷ []) = suc n
eval (proj i) args = lookup args i
eval (comp f gs) args = eval f (eval-vec gs args)
eval (rec f g) (zero ∷ args) = eval f args
eval (rec f g) (suc x ∷ args) = eval g (eval (rec f g) (x ∷ args) ∷ args)

eval-vec [] args = []
eval-vec (g ∷ gs) args = eval g args ∷ eval-vec gs args

+-expr : Expr 2
+-expr =
  rec
    -- (0, n) → n
    (proj zero)
    -- (S m, n) → S (m + n)
    (comp suc (proj zero ∷ []) )

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
m + n = eval +-expr (m ∷ n ∷ [])

+≡+ : m + n ≡ m ℕ.+ n
+≡+ {zero} = refl
+≡+ {suc m} {n} =
  begin
    suc m + n
  ≡⟨ refl ⟩
    suc (m + n)
  ≡⟨ cong suc (+≡+ {m} {n}) ⟩
    suc m ℕ.+ n
  ∎

*-expr : Expr 2
*-expr =
  rec
    -- (0, n) → 0
    zero₁
    -- (S m, n) → (m * n) + n
    +-expr

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
m * n = eval *-expr (m ∷ n ∷ [])

*≡* : m * n ≡ m ℕ.* n
*≡* {zero} = refl
*≡* {suc m} {n} =
  begin
    suc m * n
  ≡⟨ refl ⟩
    (m * n) + n
  ≡⟨ +≡+ {m * n} {n} ⟩
    (m * n) ℕ.+ n
  ≡⟨ cong (λ x → x ℕ.+ n) (*≡* {m} {n}) ⟩
    (m ℕ.* n) ℕ.+ n
  ≡⟨ +-comm (m ℕ.* n) n ⟩
    n ℕ.+ (m ℕ.* n)
  ≡⟨ refl ⟩
    suc m ℕ.* n
  ∎
