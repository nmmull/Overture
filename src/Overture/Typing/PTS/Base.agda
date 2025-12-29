open import Overture.Typing.PTS.Specification using (Spec)

module Overture.Typing.PTS.Base (𝒮 : Spec) where

open import Overture.Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁)
open import Data.Fin.Substitution using (Sub)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Level renaming (zero to ℓ0) using (Level)
open import Relation.Binary.PropositionalEquality

private
  variable
    ℓ : Level
    m n : ℕ

infix 25 λ̂_·_
infix 25 Π_·_
data Expr (n : ℕ) : Set where
  𝑠 : Spec.Sort 𝒮 → Expr n
  𝑣 : Fin n → Expr n
  λ̂_·_ : Expr n → Expr (suc n) → Expr n
  Π_·_ : Expr n → Expr (suc n) → Expr n
  _§_ : Expr n → Expr n → Expr n

shift : ∀ m p → Expr (m + n) → Expr (m + (p + n))
shift m p (𝑠 i) = 𝑠 i
shift m p (𝑣 i) = 𝑣 (Fin.shift m p i)
shift m p (λ̂ a · b) =  λ̂ (shift m p a) · (shift (suc m) p b)
shift m p (Π a · b) = Π (shift m p a) · (shift (suc m) p b)
shift m p (a § b) = (shift m p a) § (shift m p b)

_/_ : Expr m → Sub Expr m n → Expr n
𝑠 i / ρ = 𝑠 i
𝑣 i / ρ = Vec.lookup ρ i
λ̂ a · b / ρ = λ̂ (a / ρ) · (b / (𝑣 zero ∷ Vec.map (shift 0 1) ρ))
Π a · b / ρ = Π (a / ρ) · (b / (𝑣 zero ∷ Vec.map (shift 0 1) ρ))
(e₁ § e₂) / ρ = (e₁ / ρ) § (e₂ / ρ)

vars : Sub Expr n n
vars {n} = Vec.map 𝑣 (Vec.allFin n)

_/⁰_ : Expr (suc n) → Expr n → Expr n
e₁ /⁰ e₂ = e₁ / (e₂ ∷ vars)

infix 15 _⟶ᵇ_
data _⟶ᵇ_ : Rel (Expr n) ℓ0 where
  β-rule :
    ∀ {a : Expr n} {b : Expr (suc n)} c →
    (λ̂ a · b) § c ⟶ᵇ b /⁰ c
  comp-Πˡ :
    ∀ {a a' : Expr n} {b : Expr (suc n)} →
    a ⟶ᵇ a' →
    Π a · b ⟶ᵇ Π a · b
  comp-Πʳ :
    ∀ {a : Expr n} {b b' : Expr (suc n)} →
    b ⟶ᵇ b' →
    Π a · b ⟶ᵇ Π a · b'
  comp-λˡ :
    ∀ {a a' : Expr n} {b : Expr (suc n)} →
    a ⟶ᵇ a' →
    λ̂ a · b ⟶ᵇ λ̂ a' · b
  comp-λʳ :
    ∀ {a : Expr n} {b b' : Expr (suc n)} →
    b ⟶ᵇ b' →
    λ̂ a · b ⟶ᵇ λ̂ a · b'
  comp-§ˡ :
    ∀ {a a' b : Expr n} →
    a ⟶ᵇ a' →
    a § b ⟶ᵇ a' § b
  comp-app₂ :
    ∀ {a b b' : Expr n} →
    b ⟶ᵇ b' →
    a § b ⟶ᵇ a § b'

-- Ctxt : Pred ℕ ℓ0
-- Ctxt n = Vec (Expr n) n

-- data WF : Ctxt n → Set

-- data _⊢_⦂_ : Ctxt n → Expr n → Expr n → Set

-- data WF where
--   wf-[] : WF []
--   wf-∷ : (a : Expr n) → (i : Spec.Sort 𝒮) → (Γ : Ctxt n) → Γ ⊢ a ⦂ 𝑠 i → WF (a ∷ Γ)

-- data _⊢_⦂_ where
--   axiom : ∀{i j} {Γ : Ctxt n} →
--     WF Γ →
--     Spec.axiom 𝒮 i j →
--     Γ ⊢ 𝑠 i ⦂ 𝑠 j

infixr 5 _∷_
data PVec (P : Pred ℕ ℓ) : ℕ → Set ℓ where
  [] : PVec P 0
  _∷_ : P n → PVec P n → PVec P (suc n)

lookup : ∀ {P : Pred ℕ ℓ} → PVec P n → (i : Fin n) → P (Fin.toℕ (Fin.opposite i))
lookup {n = suc n} (x ∷ _) zero rewrite toℕ-fromℕ n = x
lookup {n = suc n} (_ ∷ v) (suc i) rewrite toℕ-inject₁ (Fin.opposite i) = lookup v i

_++_ : ∀ {P : Pred ℕ ℓ} → PVec (λ k → P (k + n)) m → PVec P n → PVec P (m + n)
[] ++ v = v
(x ∷ u) ++ v = x ∷ (u ++ v)

Ctxt : ℕ → Set
Ctxt n = PVec Expr n

ExtCtxt : ℕ → ℕ → Set
ExtCtxt m n = PVec (λ k → Expr (k + m)) n

lemma : ∀ (i : Fin n) → Fin.toℕ i + Fin.toℕ (Fin.opposite i) ≡ n
lemma = {!!}

lookup' : Ctxt n → Fin n → Expr n
lookup' {n} Γ i = resp Expr (lemma i) (shift 0 (Fin.toℕ i) (lookup Γ i))

data WF : Pred (Ctxt n) ℓ0
data _⊢_⦂_ : Ctxt n → Rel (Expr n) ℓ0

data WF where
  []-wf : WF []
  ∷-wf : ∀ {i a} (Γ : Ctxt n) → Γ ⊢ a ⦂ 𝑠 i → WF (a ∷ Γ)

data _⊢_⦂_ where
  axiom :
    ∀ {i j} {Γ : Ctxt n} →
    Spec.axiom 𝒮 i j →
    WF Γ →
    Γ ⊢ 𝑠 i ⦂ 𝑠 j

  𝑣-intro :
    ∀ {Γ : Ctxt n} i →
    WF Γ →
    Γ ⊢ 𝑣 i ⦂ lookup' Γ i

  Π-intro :
    ∀ {i j k a b} {Γ : Ctxt n} →
    Spec.rule 𝒮 i j k →
    Γ ⊢ a ⦂ 𝑠 i →
    (a ∷ Γ) ⊢ b ⦂ 𝑠 j →
    Γ ⊢ Π a · b ⦂ 𝑠 k

  abstr :
    ∀ {i j k a b c} {Γ : Ctxt n} →
    Spec.rule 𝒮 i j k →
    Γ ⊢ a ⦂ 𝑠 i →
    (a ∷ Γ) ⊢ b ⦂ 𝑠 j →
    (a ∷ Γ) ⊢ c ⦂ b →
    Γ ⊢ λ̂ a · c ⦂ Π a · b

  app :
    ∀ {a b c d} {Γ : Ctxt n} →
    Γ ⊢ a ⦂ Π c · d →
    Γ ⊢ b ⦂ c →
    Γ ⊢ (a § b) ⦂ (d /⁰ b)

  conv-red :
    ∀ {i a b c} {Γ : Ctxt n} →
    Γ ⊢ a ⦂ b →
    Γ ⊢ c ⦂ 𝑠 i →
    b ⟶ᵇ c →
    Γ ⊢ a ⦂ c

  conv-exp :
    ∀ {i a b c} {Γ : Ctxt n} →
    Γ ⊢ a ⦂ b →
    Γ ⊢ c ⦂ 𝑠 i →
    c ⟶ᵇ b →
    Γ ⊢ a ⦂ c

shift' : ∀ p → ExtCtxt n m → ExtCtxt (p + n) m
shift' p [] = []
shift' {m} {suc n} p (a ∷ Γ) = shift n p a ∷ shift' p Γ

module Properties where


  ctxt-thinning :
    {c : Expr n}
    {Δ : ExtCtxt n m}
    {Γ : Ctxt n} →
    WF (Δ ++ Γ) →
    WF (c ∷ Γ) →
    WF ((shift' 1 Δ) ++ (c ∷ Γ))

  thinning :
    {a b : Expr (m + n)}
    {c : Expr n}
    {Δ : ExtCtxt n m}
    {Γ : Ctxt n} →
    WF (c ∷ Γ) →
    (Δ ++ Γ) ⊢ a ⦂ b →
    ((shift' 1 Δ) ++ (c ∷ Γ)) ⊢ shift m 1 a ⦂ shift m 1 b

  ctxt-thinning {Δ = []} _ wf-cΓ = wf-cΓ
  ctxt-thinning {m} {suc n} {c} {a ∷ Δ} {Γ} (∷-wf {i = i} .(Δ ++ Γ) ⊢a) wf-cΓ
    = ∷-wf (shift' 1 Δ ++ (c ∷ Γ)) (thinning wf-cΓ ⊢a)

  lemma2 :
    (i : Fin (m + n))
    (c : Expr n)
    (Δ : ExtCtxt n m)
    (Γ : Ctxt n) →
    lookup' (shift' 1 Δ ++ (c ∷ Γ)) (Fin.shift m 1 i) ≡ shift m 1 (lookup' (Δ ++ Γ) i)
  lemma2 = {!!}

  lemma3 :
    (a : Expr (suc (m + n)))
    (b : Expr (m + n)) →
    shift m 1 (a /⁰ b) ≡ shift (suc m) 1 a /⁰ shift m 1 b
  lemma3 = {!!}

  lemma4 :
    {a : Expr (m + n)}
    {b : Expr (m + n)} →
    a ⟶ᵇ b →
    shift m 1 a ⟶ᵇ shift m 1 b
  lemma4 = {!!}

  thinning wf-cΓ (axiom ax wf-ΔΓ) =
    axiom ax (ctxt-thinning wf-ΔΓ wf-cΓ)
  thinning {m = m} {c = c} {Δ = Δ} {Γ = Γ} wf-cΓ (𝑣-intro i wf-ΓΔ)
    rewrite sym (lemma2 i c Δ Γ) =
    𝑣-intro (Fin.shift m 1 i) (ctxt-thinning wf-ΓΔ wf-cΓ)
  thinning wf-cΓ (Π-intro r ⊢a ⊢b) =
    Π-intro r (thinning wf-cΓ ⊢a) (thinning wf-cΓ ⊢b)
  thinning wf-cΓ (abstr r ⊢a ⊢b ⊢c) =
    abstr r (thinning wf-cΓ ⊢a) (thinning wf-cΓ ⊢b) (thinning wf-cΓ ⊢c)
  thinning {m} {n} wf-cΓ (app {b = b} {d = d} ⊢a ⊢b)
    rewrite lemma3 {m} {n} d b =
    app (thinning wf-cΓ ⊢a) (thinning wf-cΓ ⊢b)
  thinning wf-cΓ (conv-red ⊢a ⊢c red) =
    conv-red (thinning wf-cΓ ⊢a) (thinning wf-cΓ ⊢c) (lemma4 red)
  thinning wf-cΓ (conv-exp ⊢a ⊢c exp) =
    conv-exp (thinning wf-cΓ ⊢a) (thinning wf-cΓ ⊢c) (lemma4 exp)

  substitution :
    {a b : Expr m}
    {ρ : Sub Expr m n}
    {Γ : Ctxt m}
    {Δ : Ctxt n} →
    (∀ (i : Fin m) → Δ ⊢ Vec.lookup ρ i ⦂ (lookup' Γ i / ρ)) →
    Γ ⊢ a ⦂ b →
    Δ ⊢ (a / ρ) ⦂ (b / ρ)
  substitution = {!!}

-- data Ctxt where
--   nil : Ctxt 0
--   cons : (a : Expr n) → Ctxt n → Ctxt (suc n)

-- lookup : Ctxt n → (i : Fin n) → Expr (Fin.toℕ (Fin.opposite i))
-- lookup {suc n} (cons a _) zero rewrite toℕ-fromℕ n = a
-- lookup {suc n} (cons _ Γ) (suc i) rewrite toℕ-inject₁ (Fin.opposite i) = lookup Γ i

-- data _⊢_⦂_ where
--   -- axiom : ∀ {i j} → Spec.axiom 𝒮 i j →
  --   nil ⊢ 𝑠 i ⦂ 𝑠 j
  -- 𝑣-intro : ∀ {} →
  --   Γ ⊢ 𝑣 i ⦂ lookup Γ i

-- Ctxt : ℕ → Set
-- Ctxt = Vec (Expr n) n

-- data _↠ᵇ_ : Expr n → Expr n → Set where
--   β-refl : ∀ {a : Expr n} → a ↠ᵇ a
--   β-step : ∀ {a b c : Expr n} → a ⟶ᵇ b → b ↠ᵇ c → a ↠ᵇ c

-- ↠ᵇ-trans : ∀ {a b c : Expr n} →
--   a ↠ᵇ b →
--   b ↠ᵇ c →
--   a ↠ᵇ c
-- ↠ᵇ-trans β-refl bc = bc
-- ↠ᵇ-trans (β-step ab bb') b'c = β-step ab (↠ᵇ-trans bb' b'c)

-- data _=ᵇ_ : Expr n → Expr n → Set where
--   =ᵇ-refl : ∀ {a b : Expr n} → a ↠ᵇ b → a =ᵇ b
--   =ᵇ-sym : ∀ {a b : Expr n} → a =ᵇ b → b =ᵇ a
--   =ᵇ-trans : ∀ {a b c : Expr n} → a =ᵇ b → b =ᵇ c → a =ᵇ c
