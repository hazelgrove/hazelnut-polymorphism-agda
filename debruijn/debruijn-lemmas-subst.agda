{-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-weakening
open import debruijn.debruijn-lemmas-index
open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-meet

module debruijn.debruijn-lemmas-subst where

  wf-TTSub-helper2 :
    ∀{t n Θ} →
    (t == n → ⊥) →
    (1+ (t nat+ Θ)) ⊢ T n wf →
    (1+ (t nat+ Θ)) ⊢ T (1+ (↓Nat t 1 n)) wf
  wf-TTSub-helper2 {t = Z} neq WFVarZ = abort (neq refl)
  wf-TTSub-helper2 {t = 1+ t} neq WFVarZ = WFVarS WFVarZ
  wf-TTSub-helper2 {t = Z} neq (WFVarS wf) = WFVarS wf
  wf-TTSub-helper2 {t = 1+ t} neq (WFVarS {n = n} wf) = WFVarS (wf-TTSub-helper2 {t = t} (h1 neq) wf)
    where 
      h1 : (1+ t == 1+ n → ⊥) → t == n → ⊥
      h1 neq eq rewrite eq = neq refl

  wf-TTSub-helper3 :
    ∀{m n Θ τ} → 
    Θ ⊢ τ wf →
    1+ ((n nat+ Θ)) ⊢ ↓ (m nat+ (1+ n)) 1 (↑ m (1+ (1+ n)) τ) wf
  wf-TTSub-helper3 {m = Z} {n = Z} {Θ = .(1+ _)} WFVarZ = WFVarS WFVarZ
  wf-TTSub-helper3 {m = Z} {n = 1+ n} {Θ = .(1+ _)} WFVarZ = WFVarS (wf-TTSub-helper3 {m = Z} {n = n} WFVarZ)
  wf-TTSub-helper3 {m = Z} {n = Z} {Θ = .(1+ _)} (WFVarS wf) = WFVarS (WFVarS wf)
  wf-TTSub-helper3 {m = Z} {n = 1+ n} {Θ = .(1+ _)} (WFVarS wf) = WFVarS (wf-TTSub-helper3 {m = Z} {n = n} (WFVarS wf))
  wf-TTSub-helper3 {m = 1+ m} {n = Z} {Θ = .(1+ _)} WFVarZ = WFVarZ
  wf-TTSub-helper3 {m = 1+ m} {n = 1+ n} {Θ = .(1+ _)} WFVarZ = WFVarZ
  wf-TTSub-helper3 {m = 1+ m} {n = Z} {Θ = .(1+ _)} (WFVarS wf) = WFVarS (wf-TTSub-helper3 {m = m} {n = Z} wf)
  wf-TTSub-helper3 {m = 1+ m} {n = 1+ n} {Θ = (1+ Θ)} (WFVarS wf) with wf-TTSub-helper3 {m = m} {n = 1+ n} wf 
  ... | result rewrite nat+1+ n Θ = WFVarS result
  wf-TTSub-helper3 {m = m} {n = n} {Θ = Θ} WFBase = WFBase
  wf-TTSub-helper3 {m = m} {n = n} {Θ = Θ} WFHole = WFHole
  wf-TTSub-helper3 {m = m} {n = n} {Θ = Θ} (WFArr wf wf₁) = WFArr (wf-TTSub-helper3 wf) (wf-TTSub-helper3 wf₁)
  wf-TTSub-helper3 {m = m} {n = n} {Θ = Θ} (WFForall wf) with wf-TTSub-helper3 {m = 1+ m} {n = n} wf
  ... | result rewrite nat+1+ n Θ = WFForall result

  wf-TTSub-helper : ∀{Θ n τ1 τ2} → (Θ ⊢ τ1 wf) → (1+ (n nat+ Θ) ⊢ τ2 wf) → ((n nat+ Θ) ⊢ TTSub n τ1 τ2 wf)
  wf-TTSub-helper wf1 WFBase = WFBase
  wf-TTSub-helper wf1 WFHole = WFHole
  wf-TTSub-helper wf1 (WFArr wf2 wf3) = WFArr (wf-TTSub-helper wf1 wf2) (wf-TTSub-helper wf1 wf3)
  wf-TTSub-helper {Θ = Z} {n = Z} {τ1 = τ1} wf1 WFVarZ rewrite ↓↑invert Z τ1 = wf1
  wf-TTSub-helper {n = 1+ n} wf1 WFVarZ = WFVarZ 
  wf-TTSub-helper {Θ = 1+ Θ} {n = Z} {τ1 = τ1} wf1 WFVarZ rewrite ↓↑invert Z τ1 = wf1
  wf-TTSub-helper {n = Z} wf1 (WFVarS wf2) = wf2
  wf-TTSub-helper {n = 1+ n} wf1 (WFVarS {n = m} wf2) with natEQ n m 
  wf-TTSub-helper {Θ = Θ} {1+ n} {τ1 = τ1} wf1 (WFVarS {n = m} wf2) | Inl refl = wf-TTSub-helper3 {m = Z} {n = n} wf1
  wf-TTSub-helper {n = 1+ n} wf1 (WFVarS {n = m} wf2) | Inr neq = wf-TTSub-helper2 neq wf2
  wf-TTSub-helper {n = n} {τ1 = τ1} wf1 (WFForall wf2) with (↑compose Z (1+ n) τ1)
  ... | eq rewrite eq = WFForall (wf-TTSub-helper wf1 wf2)

  wf-TTSub : ∀{Θ τ1 τ2} → (Θ ⊢ τ1 wf) → (1+ Θ ⊢ τ2 wf) → (Θ ⊢ (TTSub Z τ1 τ2) wf)
  wf-TTSub {Θ = Θ} {τ1 = τ1} wf1 WFVarZ rewrite ↓↑invert Z τ1 = wf1
  wf-TTSub wf1 (WFVarS wf2) = wf2
  wf-TTSub wf1 WFBase = WFBase
  wf-TTSub wf1 WFHole = WFHole
  wf-TTSub wf1 (WFArr wf2 wf3) = WFArr (wf-TTSub wf1 wf2) (wf-TTSub wf1 wf3)
  wf-TTSub {τ1 = τ1} wf1 (WFForall wf2) rewrite ↑compose Z 1 τ1 = WFForall (wf-TTSub-helper wf1 wf2)

  ~TTSub-helper : ∀{n Θ τ1 τ2 τ3} → (n nat+ (1+ Θ)) ⊢ τ2 wf → (n nat+ (1+ Θ)) ⊢ τ3 wf → τ2 ~ τ3 → TTSub n τ1 τ2 ~ TTSub n τ1 τ3
  ~TTSub-helper wf2 wf3 ConsistBase = ConsistBase
  ~TTSub-helper wf2 wf3 ConsistVar = ~refl
  ~TTSub-helper wf2 wf3 ConsistHole1 = ConsistHole1
  ~TTSub-helper wf2 wf3 ConsistHole2 = ConsistHole2 
  ~TTSub-helper (WFArr wf2 wf3) (WFArr wf4 wf5) (ConsistArr con1 con2) = ConsistArr (~TTSub-helper wf2 wf4 con1) (~TTSub-helper wf3 wf5 con2)
  ~TTSub-helper {n = n} {τ1 = τ1} (WFForall wf2) (WFForall wf3) (ConsistForall con) with ↑compose Z (1+ n) τ1
  ...| eq rewrite eq = ConsistForall (~TTSub-helper wf2 wf3 con)

  ~TTSub : ∀ {Θ τ1 τ2 τ3} → 1+ Θ ⊢ τ2 wf → 1+ Θ ⊢ τ3 wf → τ2 ~ τ3 → TTSub Z τ1 τ2 ~ TTSub Z τ1 τ3
  ~TTSub {Θ = Θ} wf2 wf3 con = ~TTSub-helper wf2 wf3 con

  -- inctx-sub : ∀ {n Γ τ1 τ2} → 
  --   (n , τ2 ∈ Γ) → 
  --   (n , TTSub τ1 τ2 ∈ TCtxSub τ1 Γ)
  -- inctx-sub InCtxZ = InCtxZ
  -- inctx-sub (InCtx1+ inctx) = InCtx1+ (inctx-sub inctx)
  
  SubSub-helper : 
    (n m : Nat) → 
    (τ1 τ2 τ3 : htyp) →
    TTSub (m nat+ n) τ1 (TTSub m τ2 τ3) == 
    TTSub m (TTSub n τ1 τ2) (TTSub (m nat+ 1+ n) τ1 τ3)
  SubSub-helper n m τ1 τ2 b = refl
  SubSub-helper n m τ1 τ2 (T x) = {!   !}

  -- SubSub-helper n m τ1 τ2 (T x) with natEQ m x
  -- SubSub-helper n m τ1 τ2 (T x) | Inl refl with natEQ (m nat+ 1+ n) m
  -- SubSub-helper n m τ1 τ2 (T x) | Inl refl | Inl eq = abort (h1 m n eq)
  --   where 
  --     h1 : (m n : Nat) → (m nat+ 1+ n) == m → ⊥
  --     h1 Z n () 
  --     h1 (1+ m) n eq = h1 m n (1+inj (m nat+ 1+ n) m eq)
  -- SubSub-helper n m τ1 τ2 (T x) | Inl refl | Inr neq = {!   !}
  -- SubSub-helper n m τ1 τ2 (T x) | Inr neq with natEQ (m nat+ n) (↓Nat m 1 x) | natEQ (m nat+ 1+ n) x
  -- SubSub-helper n m τ1 τ2 (T x) | Inr neq | Inl eq | Inl eq2 = {! eq  !}
  -- SubSub-helper n m τ1 τ2 (T x) | Inr neq | Inl eq | Inr neq2 = {! eq  !}
  -- SubSub-helper n m τ1 τ2 (T x) | Inr neq | Inr neq2 | Inl eq = {!   !} 
  -- SubSub-helper n m τ1 τ2 (T x) | Inr neq | Inr neq2 | Inr neq3 = {!   !} 

  SubSub-helper n m τ1 τ2 ⦇-⦈ = refl
  SubSub-helper n m τ1 τ2 (τ3 ==> τ4) rewrite SubSub-helper n m τ1 τ2 τ3 rewrite SubSub-helper n m τ1 τ2 τ4 = refl
  SubSub-helper n m τ1 τ2 (·∀ τ3) with SubSub-helper n (1+ m) τ1 τ2 τ3 
  ... | result rewrite ↑compose Z (m nat+ 1) τ2 
    rewrite ↑compose Z (1+ (m nat+ n)) τ1
    rewrite ↑compose Z (1+ m) τ2
    rewrite ↑compose Z (1+ m) (↓ n 1 (TT[ ↑ 0 (1+ n) τ1 / n ] τ2)) 
    rewrite ↑compose Z (1+ (m nat+ 1+ n)) τ1 rewrite result = refl

  SubSub : ∀{n τ1 τ2 τ3} →
    TTSub n τ1 (TTSub Z τ2 τ3) ==
    TTSub Z (TTSub n τ1 τ2) (TTSub (1+ n) τ1 τ3)
  SubSub {n = n} {τ1 = τ1} {τ2 = τ2} {τ3 = τ3} = SubSub-helper n Z τ1 τ2 τ3