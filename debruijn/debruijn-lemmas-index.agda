open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core-subst
open import debruijn.debruijn-core

module debruijn.debruijn-lemmas-index where
  
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

  -- Only used to proof correctness w.r.t old implementation:

  ↑d'Z : (t : Nat) → (d : ihexp) → ↑d' t Z d == d
  ↑d'Z t c = refl
  ↑d'Z t (X x) rewrite ↑NatZ t x = refl
  ↑d'Z t (·λ[ x ] d) rewrite ↑d'Z (1+ t) d = refl
  ↑d'Z t (·Λ d) rewrite ↑d'Z t d = refl
  ↑d'Z t ⦇-⦈ = refl
  ↑d'Z t ⦇⌜ d ⌟⦈ rewrite ↑d'Z t d = refl
  ↑d'Z t (d1 ∘ d2) rewrite ↑d'Z t d1 rewrite ↑d'Z t d2 = refl
  ↑d'Z t (d < x >) rewrite ↑d'Z t d = refl
  ↑d'Z t (d ⟨ x ⇒ x₁ ⟩) rewrite ↑d'Z t d = refl
  ↑d'Z t (d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) rewrite ↑d'Z t d = refl

  ↑tdZ : (t : Nat) → (d : ihexp) → ↑td t Z d == d
  ↑tdZ t c = refl
  ↑tdZ t (X x) = refl
  ↑tdZ t (·λ[ x ] d) rewrite ↑Z t x rewrite ↑tdZ t d = refl
  ↑tdZ t (·Λ d) rewrite ↑tdZ (1+ t) d = refl
  ↑tdZ t ⦇-⦈ = refl
  ↑tdZ t ⦇⌜ d ⌟⦈ rewrite ↑tdZ t d = refl
  ↑tdZ t (d1 ∘ d2) rewrite ↑tdZ t d1 rewrite ↑tdZ t d2 = refl
  ↑tdZ t (d < x >) rewrite ↑Z t x rewrite ↑tdZ t d = refl
  ↑tdZ t (d ⟨ x1 ⇒ x2 ⟩) rewrite ↑Z t x1 rewrite ↑Z t x2 rewrite ↑tdZ t d = refl
  ↑tdZ t (d ⟨ x1 ⇒⦇-⦈⇏ x2 ⟩) rewrite ↑Z t x1 rewrite ↑Z t x2 rewrite ↑tdZ t d = refl

  ↑d'-compose : (t i : Nat) → (d : ihexp) → ↑d' t 1 (↑d' t i d) == (↑d' t (1+ i) d)
  ↑d'-compose t i c = refl
  ↑d'-compose t i (X x) rewrite ↑Natcompose t i x = refl
  ↑d'-compose t i (·λ[ x ] d) rewrite ↑d'-compose (1+ t) i d = refl
  ↑d'-compose t i (·Λ d) rewrite ↑d'-compose t i d = refl
  ↑d'-compose t i ⦇-⦈ = refl
  ↑d'-compose t i ⦇⌜ d ⌟⦈ rewrite ↑d'-compose t i d = refl
  ↑d'-compose t i (d ∘ d₁) rewrite ↑d'-compose t i d rewrite ↑d'-compose t i d₁ = refl
  ↑d'-compose t i (d < x >) rewrite ↑d'-compose t i d = refl
  ↑d'-compose t i (d ⟨ x ⇒ x₁ ⟩) rewrite ↑d'-compose t i d = refl
  ↑d'-compose t i (d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) rewrite ↑d'-compose t i d = refl

  ↑td-compose : (t i : Nat) → (d : ihexp) → ↑td t 1 (↑td t i d) == (↑td t (1+ i) d)
  ↑td-compose t i c = refl
  ↑td-compose t i (X x) rewrite ↑Natcompose t i x = refl
  ↑td-compose t i (·λ[ x ] d) rewrite ↑td-compose t i d rewrite ↑compose t i x = refl
  ↑td-compose t i (·Λ d) rewrite ↑td-compose (1+ t) i d = refl
  ↑td-compose t i ⦇-⦈ = refl
  ↑td-compose t i ⦇⌜ d ⌟⦈ rewrite ↑td-compose t i d = refl
  ↑td-compose t i (d ∘ d₁) rewrite ↑td-compose t i d rewrite ↑td-compose t i d₁ = refl
  ↑td-compose t i (d < x >) rewrite ↑td-compose t i d rewrite ↑compose t i x = refl
  ↑td-compose t i (d ⟨ x ⇒ x₁ ⟩) rewrite ↑td-compose t i d rewrite ↑compose t i x rewrite ↑compose t i x₁ = refl
  ↑td-compose t i (d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) rewrite ↑td-compose t i d rewrite ↑compose t i x rewrite ↑compose t i x₁ = refl

  ↓↑d'-invert : ∀{n m d} → ↓d' (n nat+ m) 1 (↑d' m (n nat+ 1) d) == ↑d' m n d
  ↓↑d'-invert {d = c} = refl 
  ↓↑d'-invert {n = n} {m = m} {d = X x} rewrite ↓↑Nat-invert n m x = refl  
  ↓↑d'-invert {n = n} {m = m} {d = ·λ[ x ] d} rewrite nat+comm 1 n with ↓↑d'-invert {n = n} {m = 1+ m} {d = d} 
  ... | result rewrite nat+1+ n m rewrite result = refl
  ↓↑d'-invert {n = n} {m = m} {d = ·Λ d} rewrite ↓↑d'-invert {n = n} {m = m} {d = d} = refl
  ↓↑d'-invert {d = ⦇-⦈} = refl
  ↓↑d'-invert {n = n} {m = m} {d = ⦇⌜ d ⌟⦈} rewrite ↓↑d'-invert {n = n} {m = m} {d = d} = refl
  ↓↑d'-invert {n = n} {m = m} {d = d1 ∘ d2} rewrite ↓↑d'-invert {n = n} {m = m} {d = d1} rewrite ↓↑d'-invert {n = n} {m = m} {d = d2} = refl
  ↓↑d'-invert {n = n} {m = m} {d = d < x >} rewrite ↓↑d'-invert {n = n} {m = m} {d = d} = refl
  ↓↑d'-invert {n = n} {m = m} {d = d ⟨ x ⇒ x₁ ⟩} rewrite ↓↑d'-invert {n = n} {m = m} {d = d} = refl    
  ↓↑d'-invert {n = n} {m = m} {d = d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} rewrite ↓↑d'-invert {n = n} {m = m} {d = d} = refl 

  ↓↑td-invert : ∀{n m d} → ↓td (n nat+ m) 1 (↑td m (n nat+ 1) d) == ↑td m n d
  ↓↑td-invert {d = c} = refl
  ↓↑td-invert {d = X x} = refl
  ↓↑td-invert {n} {m} {·λ[ x ] d} rewrite ↓↑td-invert {n} {m} {d} rewrite ↓↑-invert {n} {m} {x} = refl
  ↓↑td-invert {n} {m} {·Λ d} with ↓↑td-invert {n} {1+ m} {d}
  ... | eq rewrite nat+1+ n m rewrite eq = refl
  ↓↑td-invert {n} {m} {⦇-⦈} = refl
  ↓↑td-invert {n} {m} {⦇⌜ d ⌟⦈} rewrite ↓↑td-invert {n} {m} {d} = refl
  ↓↑td-invert {n} {m} {d ∘ d₁} rewrite ↓↑td-invert {n} {m} {d} rewrite ↓↑td-invert {n} {m} {d₁} = refl
  ↓↑td-invert {n} {m} {d < x >} rewrite ↓↑td-invert {n} {m} {d} rewrite ↓↑-invert {n} {m} {x} = refl
  ↓↑td-invert {n} {m} {d ⟨ x ⇒ x₁ ⟩} rewrite ↓↑td-invert {n} {m} {d} rewrite ↓↑-invert {n} {m} {x} rewrite ↓↑-invert {n} {m} {x₁} = refl
  ↓↑td-invert {n} {m} {d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} rewrite ↓↑td-invert {n} {m} {d} rewrite ↓↑-invert {n} {m} {x} rewrite ↓↑-invert {n} {m} {x₁} = refl

  ↑d'-↑td-comm : ∀{n m t s d} → ↑d' t n (↑td s m d) == ↑td s m (↑d' t n d)
  ↑d'-↑td-comm {d = c} = refl 
  ↑d'-↑td-comm {d = X x} = refl
  ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = ·λ[ x ] d} rewrite ↑d'-↑td-comm {n = n} {m = m} {t = 1+ t} {s = s} {d = d} = refl   
  ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = ·Λ d} rewrite ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = 1+ s} {d = d} = refl
  ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = ⦇-⦈} = refl
  ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = ⦇⌜ d ⌟⦈} rewrite ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d} = refl
  ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d ∘ d₁} 
    rewrite ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d} 
    rewrite ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d₁} = refl
  ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d < x >} rewrite ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d} = refl
  ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d ⟨ x ⇒ x₁ ⟩} rewrite ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d} = refl  
  ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} rewrite ↑d'-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d} = refl