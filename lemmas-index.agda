open import Nat
open import Prelude
open import core-type
open import core-exp
open import core-subst
open import core

module lemmas-index where
  
  ↑10 : (x : Nat) → (↑Nat Z 1 x) == 1+ x
  ↑10 Z = refl 
  ↑10 (1+ x) rewrite (↑10 x) = refl

  ↑NatZ : (t x : Nat) → ↑Nat t Z x == x
  ↑NatZ Z x = refl
  ↑NatZ (1+ t) Z = refl
  ↑NatZ (1+ t) (1+ x) rewrite ↑NatZ t x = refl

  ↑Z : (t : Nat) → (τ : htyp) → ↑ t Z τ == τ
  ↑Z t b = refl
  ↑Z t (T x) rewrite ↑NatZ t x = refl
  ↑Z t ⦇-⦈ = refl
  ↑Z t (τ ==> τ₁) rewrite ↑Z t τ rewrite ↑Z t τ₁ = refl
  ↑Z t (·∀ τ) rewrite ↑Z (1+ t) τ = refl

  ↑dZ : (t1 t2 : Nat) → (d : ihexp) → ↑d t1 Z t2 Z d == d
  ↑dZ t1 t2 c = refl
  ↑dZ t1 t2 ⦇-⦈ = refl
  ↑dZ t1 t2 ⦇⌜ d ⌟⦈ rewrite ↑dZ t1 t2 d = refl
  ↑dZ t1 t2 (d ∘ d₁) rewrite ↑dZ t1 t2 d rewrite ↑dZ t1 t2 d₁ = refl
  ↑dZ t1 t2 (d < x >) rewrite ↑Z t2 x rewrite ↑dZ t1 t2 d = refl
  ↑dZ t1 t2 (d ⟨ x ⇒ x₁ ⟩) rewrite ↑Z t2 x rewrite ↑Z t2 x₁ rewrite ↑dZ t1 t2 d = refl
  ↑dZ t1 t2 (d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) rewrite ↑Z t2 x rewrite ↑Z t2 x₁ rewrite ↑dZ t1 t2 d = refl
  ↑dZ t1 t2 (·λ[ x ] d) rewrite ↑Z t2 x rewrite ↑dZ (1+ t1) t2 d = refl
  ↑dZ t1 t2 (·Λ d) rewrite ↑dZ t1 (1+ t2) d = refl
  ↑dZ t1 t2 (X x) rewrite ↑NatZ t1 x = refl
  
  ↑Natcompose : (t i x : Nat) → ↑Nat t 1 (↑Nat t i x) == ↑Nat t (1+ i) x
  ↑Natcompose Z Z x = refl
  ↑Natcompose Z (1+ i) x = refl
  ↑Natcompose (1+ t) i Z = refl
  ↑Natcompose (1+ t) i (1+ x) rewrite ↑Natcompose t i x = refl

  ↑compose : (t i : Nat) → (τ : htyp) → ↑ t 1 (↑ t i τ) == (↑ t (1+ i) τ)
  ↑compose _ _ b = refl
  ↑compose t i (T x) rewrite ↑Natcompose t i x = refl
  ↑compose _ _ ⦇-⦈ = refl
  ↑compose t i (τ ==> τ₁) rewrite ↑compose t i τ rewrite ↑compose t i τ₁ = refl
  ↑compose t i (·∀ τ) rewrite ↑compose (1+ t) i τ = refl

  ↑ctx-compose : (t i : Nat) → (Γ : ctx) → ↑ctx t 1 (↑ctx t i Γ) == (↑ctx t (1+ i) Γ)
  ↑ctx-compose t i ∅ = refl
  ↑ctx-compose t i (x , Γ) rewrite ↑compose t i x rewrite ↑ctx-compose t i Γ = refl
  ↑ctx-compose t i (TVar, Γ) rewrite ↑ctx-compose (1+ t) i Γ = refl

  -- ↓↑Nat-invert : (t x : Nat) → ↓Nat t 1 (↑Nat t 1 x) == x
  -- ↓↑Nat-invert Z x = refl 
  -- ↓↑Nat-invert (1+ t) Z = refl
  -- ↓↑Nat-invert (1+ t) (1+ x) rewrite ↓↑Nat-invert t x = refl
  
  -- ↓↑invert : (t : Nat) → (τ : htyp) → ↓ t 1 (↑ t 1 τ) == τ
  -- ↓↑invert t b = refl 
  -- ↓↑invert t (T x) rewrite ↓↑Nat-invert t x = refl
  -- ↓↑invert t ⦇-⦈ = refl
  -- ↓↑invert t (τ ==> τ₁) rewrite ↓↑invert t τ rewrite ↓↑invert t τ₁ = refl
  -- ↓↑invert t (·∀ τ) rewrite ↓↑invert (1+ t) τ = refl

  ↓↑Nat-invert : (n m x : Nat) → ↓Nat (n nat+ m) 1 (↑Nat m (n nat+ 1) x) == ↑Nat m n x
  ↓↑Nat-invert Z Z x = refl
  ↓↑Nat-invert Z (1+ m) Z = refl
  ↓↑Nat-invert Z (1+ m) (1+ x) rewrite ↓↑Nat-invert Z m x = refl
  ↓↑Nat-invert (1+ n) Z x rewrite nat+Z n with ↓↑Nat-invert n Z x
  ... | result rewrite nat+Z n rewrite result = refl
  ↓↑Nat-invert (1+ n) (1+ m) Z = refl
  ↓↑Nat-invert (1+ n) (1+ m) (1+ x) with ↓↑Nat-invert (1+ n) m x 
  ... | result rewrite nat+1+ n m rewrite result = refl
  
  ↓↑-invert : ∀{n m τ} → ↓ (n nat+ m) 1 (↑ m (n nat+ 1) τ) == ↑ m n τ
  ↓↑-invert {n} {m} {b} = refl
  ↓↑-invert {n} {m} {T x} rewrite ↓↑Nat-invert n m x = refl
  ↓↑-invert {n} {m} {⦇-⦈} = refl
  ↓↑-invert {n} {m} {τ ==> τ₁} rewrite ↓↑-invert {n} {m} {τ} rewrite ↓↑-invert {n} {m} {τ₁} = refl
  ↓↑-invert {n} {m} {·∀ τ} with ↓↑-invert {n} {1+ m} {τ} 
  ... | result rewrite nat+1+ n m rewrite result = refl
