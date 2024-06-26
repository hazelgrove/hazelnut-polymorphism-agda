open import Nat
open import Prelude
open import core-type
open import core-exp
open import core-subst
open import core
open import lemmas-index

module lemmas-complete where

  ↑-complete : ∀{n m τ} → τ tcomplete → ↑ n m τ tcomplete
  ↑-complete TCBase = TCBase
  ↑-complete TCVar = TCVar
  ↑-complete (TCArr tc tc₁) = TCArr (↑-complete tc) (↑-complete tc₁)
  ↑-complete (TCForall tc) = TCForall (↑-complete tc)

  ↓-complete : ∀{n m τ} → τ tcomplete → ↓ n m τ tcomplete
  ↓-complete TCBase = TCBase
  ↓-complete TCVar = TCVar
  ↓-complete (TCArr tc tc₁) = TCArr (↓-complete tc) (↓-complete tc₁)
  ↓-complete (TCForall tc) = TCForall (↓-complete tc)

  ↑d-complete : ∀{t1 n t2 m d} → d dcomplete → ↑d t1 n t2 m d dcomplete
  ↑d-complete DCVar = DCVar
  ↑d-complete DCConst = DCConst
  ↑d-complete (DCLam dc x) = DCLam (↑d-complete dc) (↑-complete x)
  ↑d-complete (DCTLam dc) = DCTLam (↑d-complete dc)
  ↑d-complete (DCAp dc dc₁) = DCAp (↑d-complete dc) (↑d-complete dc₁)
  ↑d-complete (DCTAp x dc) = DCTAp (↑-complete x) (↑d-complete dc)
  ↑d-complete (DCCast dc x x₁) = DCCast (↑d-complete dc) (↑-complete x) (↑-complete x₁)

  inctx-complete : ∀{x τ Γ} → Γ gcomplete → x , τ ∈ Γ → τ tcomplete
  inctx-complete GCEmpty ()
  inctx-complete (GCVar gc x) InCtxZ = x
  inctx-complete (GCVar gc x) (InCtx1+ inctx) = inctx-complete gc inctx
  inctx-complete (GCTVar gc) (InCtxSkip inctx) = ↑-complete (inctx-complete gc inctx) 

  meet-complete : ∀{τ1 τ2 τ3} → τ1 tcomplete → (τ1 ⊓ τ2 == τ3) → τ3 tcomplete
  meet-complete tc MeetHoleR = tc
  meet-complete tc MeetBase = tc
  meet-complete tc MeetVar = tc
  meet-complete (TCArr tc tc₁) (MeetArr meet1 meet2) = TCArr (meet-complete tc meet1) (meet-complete tc₁ meet2)
  meet-complete (TCForall tc) (MeetForall meet) = TCForall (meet-complete tc meet)

  TTSub-complete : ∀{τ1 τ2 n} → τ1 tcomplete → τ2 tcomplete → TTSub n τ1 τ2 tcomplete
  TTSub-complete tc1 TCBase = TCBase
  TTSub-complete {n = n} tc1 (TCVar {n = x}) with natEQ n x 
  ... | Inl refl = ↓-complete (↑-complete tc1) 
  ... | Inr neq = TCVar
  TTSub-complete tc1 (TCArr tc2 tc3) = TCArr (TTSub-complete tc1 tc2) (TTSub-complete tc1 tc3)
  TTSub-complete {τ1 = τ1} {n = n} tc1 (TCForall tc2) with TTSub-complete {n = 1+ n} tc1 tc2 
  ... | tc rewrite ↑compose 0 (1+ n) τ1 = TCForall tc

  TtSub-complete : ∀{n τ d} → τ tcomplete → d dcomplete → TtSub n τ d dcomplete
  TtSub-complete tc DCVar = DCVar
  TtSub-complete tc DCConst = DCConst
  TtSub-complete tc (DCLam dc x) = DCLam (TtSub-complete tc dc) (TTSub-complete tc x)
  TtSub-complete {n} {τ} tc (DCTLam dc) with TtSub-complete {1+ n} tc dc
  ... | dc' rewrite sym (↑compose Z (1+ n) τ) = DCTLam dc'
  TtSub-complete tc (DCAp dc dc₁) = DCAp (TtSub-complete tc dc) (TtSub-complete tc dc₁)
  TtSub-complete tc (DCTAp x dc) = DCTAp (TTSub-complete tc x) (TtSub-complete tc dc)
  TtSub-complete tc (DCCast dc x x₁) = DCCast (TtSub-complete tc dc) (TTSub-complete tc x) (TTSub-complete tc x₁)

  ttSub-complete : ∀{n m d1 d2} → d1 dcomplete → d2 dcomplete → ttSub n m d1 d2 dcomplete
  ttSub-complete {n} dc1 (DCVar {x = x}) with natEQ x n 
  ... | Inl refl = ↑d-complete dc1
  ... | Inr neq = DCVar
  ttSub-complete dc1 DCConst = DCConst
  ttSub-complete {n} {m} {d1} dc1 (DCLam dc2 x) with ttSub-complete {1+ n} {m} dc1 dc2 
  ... | dc3 = DCLam dc3 x
  ttSub-complete {n} {m} {d1} dc1 (DCTLam dc2) with ttSub-complete {n} {1+ m} dc1 dc2 
  ... | dc3 = DCTLam dc3
  ttSub-complete dc1 (DCAp dc2 dc3) = DCAp (ttSub-complete dc1 dc2) (ttSub-complete dc1 dc3)
  ttSub-complete dc1 (DCTAp x dc2) = DCTAp x (ttSub-complete dc1 dc2)
  ttSub-complete dc1 (DCCast dc2 x x₁) = DCCast (ttSub-complete dc1 dc2) x x₁

  complete-indet : ∀{d} → d dcomplete → d indet → ⊥
  complete-indet DCVar ()
  complete-indet DCConst ()
  complete-indet (DCLam comp x₁) ()
  complete-indet (DCAp comp comp₁) (IAp x ind x₁) = complete-indet comp ind
  complete-indet (DCCast comp x x₁) (ICastArr x₂ ind) = complete-indet comp ind
  complete-indet (DCCast comp x x₁) (ICastGroundHole x₂ ind) = complete-indet comp ind
  complete-indet (DCCast comp x x₁) (ICastHoleGround x₂ ind x₃) = complete-indet comp ind
  complete-indet {d < x₁ >} (DCTAp x₂ x₃) (ITAp x x₄) = complete-indet x₃ x₄
  complete-indet {d ⟨ ·∀ x₁ ⇒ ·∀ τ2 ⟩} (DCCast x₂ x₃ x₄)
    (ICastForall x₅ x₆) = complete-indet x₂ x₆

  complete-consistency : ∀{τ1 τ2} → τ1 ~ τ2 → τ1 tcomplete → τ2 tcomplete → τ1 == τ2
  complete-consistency ConsistBase TCBase TCBase = refl
  complete-consistency ConsistVar TCVar TCVar = refl
  complete-consistency ConsistHole1 TCBase ()
  complete-consistency ConsistHole1 TCVar ()
  complete-consistency ConsistHole1 (TCArr tc1 tc2) ()
  complete-consistency ConsistHole1 (TCForall tc1) ()
  complete-consistency ConsistHole2 () tc2
  complete-consistency (ConsistArr con1 con2) (TCArr tc1 tc2) (TCArr tc3 tc4) 
    rewrite complete-consistency con1 tc1 tc3 rewrite complete-consistency con2 tc2 tc4 = refl
  complete-consistency (ConsistForall con) (TCForall tc1) (TCForall tc2) 
    rewrite complete-consistency con tc1 tc2 = refl