open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-weakening
open import debruijn.debruijn-lemmas-index
open import debruijn.debruijn-lemmas-meet
open import debruijn.debruijn-lemmas-subst

module debruijn.debruijn-lemmas-wf where

  wf-ctx-var : ∀{τ n Θ Γ} → 
    (Θ ⊢ Γ ctxwf) →
    (n , τ ∈ Γ) → 
    Θ ⊢ τ wf
  wf-ctx-var (CtxWFExtend x ctxwf) InCtxZ = x
  wf-ctx-var (CtxWFExtend x ctxwf) (InCtx1+ inctx) = wf-ctx-var ctxwf inctx

  wf-inc : ∀{Θ τ m} → Θ ⊢ τ wf → 1+ Θ ⊢ ↑ m 1 τ wf
  wf-inc {m = Z} WFVarZ = WFVarS WFVarZ
  wf-inc {m = 1+ m} WFVarZ = WFVarZ
  wf-inc {m = Z} (WFVarS wf) = WFVarS (WFVarS wf)
  wf-inc {m = 1+ m} (WFVarS wf) = WFVarS (wf-inc wf)
  wf-inc WFBase = WFBase
  wf-inc WFHole = WFHole
  wf-inc (WFArr wf wf₁) = WFArr (wf-inc wf) (wf-inc wf₁)
  wf-inc (WFForall wf) = WFForall (wf-inc wf)

  wf-ctx-inc : ∀{Θ Γ} → Θ ⊢ Γ ctxwf → 1+ Θ ⊢ ↑ctx Z 1 Γ ctxwf
  wf-ctx-inc CtxWFEmpty = CtxWFEmpty
  wf-ctx-inc (CtxWFExtend x ctxwf) = CtxWFExtend (wf-inc x) (wf-ctx-inc ctxwf)

  wf-⊑t : ∀{Θ τ1 τ2} → Θ ⊢ τ1 wf → τ1 ⊑t τ2 → Θ ⊢ τ2 wf
  wf-⊑t wf PTBase = wf 
  wf-⊑t _ PTHole = WFHole
  wf-⊑t wf PTTVar = wf
  wf-⊑t (WFArr wf1 wf2) (PTArr prec1 prec2) = WFArr (wf-⊑t wf1 prec1) (wf-⊑t wf2 prec2)
  wf-⊑t (WFForall wf) (PTForall prec) = WFForall (wf-⊑t wf prec)

  wf-⊓ : ∀{τ1 τ2 τ3 Θ} → τ1 ⊓ τ2 == τ3 → Θ ⊢ τ1 wf → Θ ⊢ τ2 wf → Θ ⊢ τ3 wf
  wf-⊓ MeetHoleL wf1 wf2 = wf2 
  wf-⊓ MeetHoleR wf1 wf2 = wf1
  wf-⊓ MeetBase wf1 wf2 = wf2
  wf-⊓ MeetVar wf1 wf2 = wf2
  wf-⊓ (MeetArr meet meet₁) (WFArr wf1 wf2) (WFArr wf3 wf4) = WFArr (wf-⊓ meet wf1 wf3) (wf-⊓ meet₁ wf2 wf4)
  wf-⊓ (MeetForall meet) (WFForall wf1) (WFForall wf2) = WFForall (wf-⊓ meet wf1 wf2)

  wf-syn : ∀{τ e Θ Γ} → 
    (Θ ⊢ Γ ctxwf) → 
    (Θ , Γ ⊢ e => τ) → 
    Θ ⊢ τ wf
  wf-syn ctxwf SConst = WFBase
  wf-syn ctxwf (SAsc x x₁) = x
  wf-syn ctxwf (SVar x) = wf-ctx-var ctxwf x
  wf-syn ctxwf (SAp syn meet _) with wf-⊓ meet (wf-syn ctxwf syn) (WFArr WFHole WFHole)
  ... | WFArr _ wf = wf
  wf-syn ctxwf SEHole = WFHole
  wf-syn ctxwf (SNEHole syn) = WFHole
  wf-syn ctxwf (SLam x syn) = WFArr x (wf-syn (CtxWFExtend x ctxwf) syn)
  wf-syn ctxwf (STLam syn) = WFForall (wf-syn (wf-ctx-inc ctxwf) syn)
  wf-syn ctxwf (STAp wf syn meet refl) with wf-⊓ meet (wf-syn ctxwf syn) (WFForall WFHole) 
  ... | WFForall wf' = wf-TTSub wf wf'
  
  wf-elab-syn : ∀{τ e d Θ Γ} → 
    (Θ ⊢ Γ ctxwf) → 
    (Θ , Γ ⊢ e ⇒ τ ~> d) → 
    Θ ⊢ τ wf
  wf-elab-syn ctxwf ESConst = WFBase
  wf-elab-syn ctxwf (ESVar x) = wf-ctx-var ctxwf x
  wf-elab-syn ctxwf (ESLam x syn) = WFArr x (wf-elab-syn (CtxWFExtend x ctxwf) syn)
  wf-elab-syn ctxwf (ESTLam syn) = WFForall (wf-elab-syn (wf-ctx-inc ctxwf) syn)
  wf-elab-syn ctxwf (ESAp syn meet _ _) with wf-⊓ meet (wf-syn ctxwf syn) (WFArr WFHole WFHole)
  ... | WFArr _ wf = wf
  wf-elab-syn ctxwf (ESTAp wf syn meet _ refl) with wf-⊓ meet (wf-syn ctxwf syn) (WFForall WFHole) 
  ... | WFForall wf' = wf-TTSub wf wf'
  wf-elab-syn ctxwf ESEHole = WFHole
  wf-elab-syn ctxwf (ESNEHole syn) = WFHole
  wf-elab-syn ctxwf (ESAsc x x₁) = x

  wf-ta : ∀{τ d Θ Γ} → 
    (Θ ⊢ Γ ctxwf) → 
    (Θ , Γ ⊢ d :: τ) → 
    Θ ⊢ τ wf
  wf-ta ctxwf TAConst = WFBase
  wf-ta ctxwf (TAVar x) = wf-ctx-var ctxwf x
  wf-ta ctxwf (TALam x wt) = WFArr x (wf-ta (CtxWFExtend x ctxwf) wt)
  wf-ta ctxwf (TATLam wt) = WFForall (wf-ta (wf-ctx-inc ctxwf) wt)
  wf-ta ctxwf (TAAp wt wt₁) with wf-ta ctxwf wt 
  ... | WFArr _ wf = wf
  wf-ta ctxwf (TATAp x wt refl) with wf-ta ctxwf wt 
  ... | WFForall wf = wf-TTSub x wf
  wf-ta ctxwf (TAEHole wf) = wf 
  wf-ta ctxwf (TANEHole wf _) = wf
  wf-ta ctxwf (TACast _ wf _) = wf
  wf-ta ctxwf (TAFailedCast wt _ GBase _) = WFBase
  wf-ta ctxwf (TAFailedCast wt _ GArr _) = WFArr WFHole WFHole
  wf-ta ctxwf (TAFailedCast wt _ GForall _) = WFForall WFHole