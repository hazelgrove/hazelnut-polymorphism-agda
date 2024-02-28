-- {-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import core-type
open import core-exp
open import core-subst
open import core
open import weakening
open import lemmas-index
open import lemmas-ctx
open import lemmas-consistency
open import lemmas-meet
open import lemmas-subst
open import lemmas-wf

module typing-subst where

  -- TtSub section
  
  consist-sub : ∀{m τ1 τ2 τ3} → τ2 ~ τ3 → TTSub m τ1 τ2 ~ TTSub m τ1 τ3
  consist-sub ConsistBase = ConsistBase
  consist-sub {m} (ConsistVar {x}) with natEQ m x
  ... | Inl refl = ~refl 
  ... | Inr neq = ~refl
  consist-sub ConsistHole1 = ConsistHole1
  consist-sub ConsistHole2 = ConsistHole2
  consist-sub (ConsistArr con1 con2) = ConsistArr (consist-sub con1) (consist-sub con2)
  consist-sub (ConsistForall con) = ConsistForall (consist-sub con)
  
  nat-shift-miss : (t x : Nat) → t ≠ ↑Nat t 1 x
  nat-shift-miss Z x ()
  nat-shift-miss (1+ t) Z ()
  nat-shift-miss (1+ t) (1+ x) eq = nat-shift-miss t x (1+inj _ _ eq)

  sub-shift-miss : (t : Nat) → (τ' τ : htyp) → TTSub t τ' (↑ t 1 τ) == τ
  sub-shift-miss t τ' b = refl
  sub-shift-miss t τ' (T x) with natEQ t (↑Nat t 1 x) 
  ... | Inl eq = abort (nat-shift-miss _ _ eq) 
  ... | Inr neq rewrite ↓↑Nat-invert Z t x rewrite ↑NatZ t x = refl
  sub-shift-miss t τ' ⦇-⦈ = refl
  sub-shift-miss t τ' (τ1 ==> τ2) rewrite sub-shift-miss t τ' τ1 rewrite sub-shift-miss t τ' τ2 = refl
  sub-shift-miss t τ' (·∀ τ) rewrite sub-shift-miss (1+ t) τ' τ = refl

  some-equation-nat : (n m x : Nat) → ↓Nat (1+ n nat+ m) 1 (↑Nat n 1 x) == ↑Nat n 1 (↓Nat (n nat+ m) 1 x)
  some-equation-nat Z m x = refl
  some-equation-nat (1+ n) m Z = refl
  some-equation-nat (1+ n) m (1+ x) rewrite some-equation-nat n m x = refl

  some-equation : (n m : Nat) → (τ : htyp) → ↓ (1+ n nat+ m) 1 (↑ n 1 τ) == ↑ n 1 (↓ (n nat+ m) 1 τ)
  some-equation n m b = refl
  some-equation n m (T x) rewrite some-equation-nat n m x = refl
  some-equation n m ⦇-⦈ = refl
  some-equation n m (τ1 ==> τ2) rewrite some-equation n m τ1 rewrite some-equation n m τ2 = refl
  some-equation n m (·∀ τ) rewrite some-equation (1+ n) m τ = refl

  other-equation-nat : (m n x : Nat) → ↑Nat m 1 (↑Nat (m nat+ n) 1 x) == ↑Nat (1+ m nat+ n) 1 (↑Nat m 1 x)
  other-equation-nat Z n x = refl
  other-equation-nat (1+ m) n Z = refl
  other-equation-nat (1+ m) n (1+ x) rewrite other-equation-nat m n x = refl

  other-equation : (m n : Nat) → (τ : htyp) → ↑ m 1 (↑ (m nat+ n) 1 τ) == ↑ (1+ m nat+ n) 1 (↑ m 1 τ)
  other-equation m n b = refl
  other-equation m n (T x) rewrite other-equation-nat m n x = refl
  other-equation m n ⦇-⦈ = refl
  other-equation m n (τ1 ==> τ2) rewrite other-equation m n τ1 rewrite other-equation m n τ2 = refl
  other-equation m n (·∀ τ) rewrite other-equation (1+ m) n τ = refl

  sub-incr : (m x : Nat) → (τ : htyp) → TTSub (1+ m) τ (T (1+ x)) == ↑ Z 1 (TTSub m τ (T x))
  sub-incr m x τ with natEQ m x 
  ... | Inr neq = refl
  ... | Inl refl rewrite sym (some-equation Z m (↑ 0 (1+ m) τ)) rewrite ↑compose Z (1+ m) τ = refl 

  sub-shift : (n m : Nat) → (τ' τ : htyp) → TTSub (1+ n nat+ m) τ' (↑ n 1 τ) == ↑ n 1 (TTSub (n nat+ m) τ' τ)
  sub-shift n m τ' b = refl
  sub-shift n m τ' ⦇-⦈ = refl
  sub-shift n m τ' (τ1 ==> τ2) rewrite sub-shift n m τ' τ1 rewrite sub-shift n m τ' τ2 = refl
  sub-shift n m τ' (·∀ τ) rewrite sub-shift (1+ n) m τ' τ = refl
  sub-shift Z m τ' (T x) with natEQ m x 
  ... | Inl refl rewrite sym (↑compose Z (1+ m) τ') rewrite some-equation Z m (↑ 0 (1+ m) τ') = refl 
  ... | Inr neq = refl
  sub-shift (1+ n) m τ' (T Z) = refl
  sub-shift (1+ n) m τ' (T (1+ x)) with sub-shift n m τ' (T x)
  ... | eq 
    rewrite sub-incr (1+ (n nat+ m)) (↑Nat n 1 x) τ' 
    rewrite sub-incr (n nat+ m) x τ' 
    rewrite eq = other-equation Z n _

  inctx-subst : ∀{m τ1 n Γ τ2} → n , τ2 ∈ Γ → n , TTSub m τ1 τ2 ∈ TCtxSub m τ1 Γ
  inctx-subst {Z} {τ1} (InCtxSkip {τ = τ} inctx) rewrite sub-shift-miss Z τ1 τ = inctx
  inctx-subst {1+ m} {τ1} (InCtxSkip {τ = τ} inctx) rewrite sub-shift Z m τ1 τ = InCtxSkip (inctx-subst inctx)
  inctx-subst InCtxZ = InCtxZ
  inctx-subst (InCtx1+ inctx) = InCtx1+ (inctx-subst inctx)

  wf-subst : ∀{m τ1 τ2 Γ} → ∅ ⊢ τ1 wf → Γ ⊢ τ2 wf → TCtxSub m τ1 Γ ⊢ TTSub m τ1 τ2 wf
  wf-subst wf1 (WFSkip wf2) =  weakening-wf-var (wf-subst wf1 wf2)
  wf-subst {Z} {τ1} wf1 WFVarZ rewrite ↓↑-invert {Z} {Z} {τ1} rewrite ↑Z Z τ1 = weakening-wf wf1
  wf-subst {1+ m} wf1 WFVarZ = WFVarZ
  wf-subst {Z} wf1 (WFVarS wf2) = wf2
  wf-subst {1+ m} {τ1} wf1 (WFVarS {n = n} wf2) rewrite sub-incr m n τ1 = wf-inc (wf-subst {m} wf1 wf2)
  wf-subst wf1 WFBase = WFBase
  wf-subst wf1 WFHole = WFHole
  wf-subst wf1 (WFArr wf2 wf3) = WFArr (wf-subst wf1 wf2) (wf-subst wf1 wf3)
  wf-subst wf1 (WFForall wf2) = WFForall (wf-subst wf1 wf2)

  subsub : (n m : Nat) → (τ1 τ2 τ3 : htyp) → TTSub (n nat+ m) τ1 (TTSub n τ2 τ3) == TTSub n (TTSub m τ1 τ2) (TTSub (1+ n nat+ m) τ1 τ3)
  subsub n m τ1 τ2 b = refl
  subsub n m τ1 τ2 (T x) = {!   !}
  subsub n m τ1 τ2 ⦇-⦈ = refl
  subsub n m τ1 τ2 (τ3 ==> τ4) rewrite subsub n m τ1 τ2 τ3 rewrite subsub n m τ1 τ2 τ4 = refl
  subsub n m τ1 τ2 (·∀ τ3) rewrite subsub (1+ n) m τ1 τ2 τ3 = refl

  wt-TtSub-strong : ∀{Γ m d τ1 τ2} →
    (⊢ Γ ctxwf) →
    (∅ ⊢ τ1 wf) → 
    (Γ ⊢ d :: τ2) → 
    (TCtxSub m τ1 Γ ⊢ TtSub m τ1 d :: TTSub m τ1 τ2)
  wt-TtSub-strong ctxwf wf TAConst = TAConst
  wt-TtSub-strong ctxwf wf (TAAp wt wt₁) = TAAp (wt-TtSub-strong ctxwf wf wt) (wt-TtSub-strong ctxwf wf wt₁)
  wt-TtSub-strong ctxwf wf (TATAp x wt refl) = TATAp (wf-subst wf x) (wt-TtSub-strong ctxwf wf wt) (sym {!   !})
  wt-TtSub-strong ctxwf wf TAEHole = TAEHole
  wt-TtSub-strong ctxwf wf (TANEHole wt) = TANEHole (wt-TtSub-strong ctxwf wf wt)
  wt-TtSub-strong {m = m} ctxwf wf (TACast wt x con) = TACast (wt-TtSub-strong ctxwf wf wt) (wf-subst wf x) (consist-sub con) 
  wt-TtSub-strong ctxwf wf (TALam x wt) = TALam (wf-subst wf x) (wt-TtSub-strong (CtxWFVar x ctxwf) wf wt)
  wt-TtSub-strong ctxwf wf (TATLam wt) = TATLam (wt-TtSub-strong (CtxWFTVar ctxwf) wf wt)
  wt-TtSub-strong ctxwf wf (TAVar x) = TAVar (inctx-subst x)
  wt-TtSub-strong ctxwf wf (TAFailedCast wt GBase GBase incon) = abort (incon ConsistBase)
  wt-TtSub-strong ctxwf wf (TAFailedCast wt GArr GArr incon) = abort (incon (ConsistArr ConsistHole1 ConsistHole1))
  wt-TtSub-strong ctxwf wf (TAFailedCast wt GForall GForall incon) = abort (incon (ConsistForall ConsistHole1))
  wt-TtSub-strong ctxwf wf (TAFailedCast wt GBase GArr incon) = TAFailedCast (wt-TtSub-strong ctxwf wf wt) GBase GArr incon
  wt-TtSub-strong ctxwf wf (TAFailedCast wt GBase GForall incon) = TAFailedCast (wt-TtSub-strong ctxwf wf wt) GBase GForall incon
  wt-TtSub-strong ctxwf wf (TAFailedCast wt GArr GBase incon) = TAFailedCast (wt-TtSub-strong ctxwf wf wt) GArr GBase incon
  wt-TtSub-strong ctxwf wf (TAFailedCast wt GArr GForall incon) = TAFailedCast (wt-TtSub-strong ctxwf wf wt) GArr GForall incon
  wt-TtSub-strong ctxwf wf (TAFailedCast wt GForall GBase incon) = TAFailedCast (wt-TtSub-strong ctxwf wf wt) GForall GBase incon
  wt-TtSub-strong ctxwf wf (TAFailedCast wt GForall GArr incon) = TAFailedCast (wt-TtSub-strong ctxwf wf wt) GForall GArr incon

  wt-TtSub : ∀{d τ1 τ2} →
    ∅ ⊢ τ1 wf → 
    (TVar, ∅) ⊢ d :: τ2 →
    ∅ ⊢ TtSub Z τ1 d :: TTSub Z τ1 τ2
  wt-TtSub wf wt = wt-TtSub-strong (CtxWFTVar CtxWFEmpty) wf wt

  no-fvs-lemma-type : ∀{Γ t1 t2 τ} → (m : Nat) → context-counter Γ t1 t2 → Γ ⊢ τ wf → ↑ t2 m τ == τ
  no-fvs-lemma-type m (CtxCtVar ctxct) (WFSkip wf) = no-fvs-lemma-type m ctxct wf 
  no-fvs-lemma-type m (CtxCtTVar ctxct) WFVarZ = refl
  no-fvs-lemma-type m (CtxCtTVar ctxct) (WFVarS wf) with h1 (no-fvs-lemma-type m ctxct wf) 
    where 
      h1 : ∀{x1 x2} → T x1 == T x2 → x1 == x2
      h1 refl = refl
  ... | eq rewrite eq = refl
  no-fvs-lemma-type m ctxct WFBase = refl
  no-fvs-lemma-type m ctxct WFHole = refl
  no-fvs-lemma-type m ctxct (WFArr wf wf₁) rewrite no-fvs-lemma-type m ctxct wf rewrite no-fvs-lemma-type m ctxct wf₁ = refl
  no-fvs-lemma-type m ctxct (WFForall wf) rewrite no-fvs-lemma-type m (CtxCtTVar ctxct) wf = refl
  
  inc-var-eq : ∀{x1 x2 : Nat} → (eq : Prelude._==_ {A = ihexp} (X x1) (X x2)) → (Prelude._==_ {A = ihexp} (X (1+ x1)) (X (1+ x2))) 
  inc-var-eq refl = refl

  no-fvs-lemma : ∀{Γ t1 t2 d τ} → (n m : Nat) → ⊢ Γ ctxwf → context-counter Γ t1 t2 → Γ ⊢ d :: τ → ↑d t1 n t2 m d == d
  no-fvs-lemma n m ctxwf ctxct TAConst = refl
  no-fvs-lemma n m ctxwf (CtxCtVar ctxct) (TAVar InCtxZ) = refl
  no-fvs-lemma n m (CtxWFVar x₁ ctxwf) (CtxCtVar ctxct) (TAVar (InCtx1+ x)) = inc-var-eq (no-fvs-lemma n m ctxwf ctxct (TAVar x))
  no-fvs-lemma n m (CtxWFTVar ctxwf) (CtxCtTVar ctxct) (TAVar (InCtxSkip x)) = no-fvs-lemma n m ctxwf ctxct (TAVar x) 
  no-fvs-lemma n m ctxwf ctxct (TALam x wt) rewrite no-fvs-lemma-type m ctxct x rewrite no-fvs-lemma n m (CtxWFVar x ctxwf) (CtxCtVar ctxct) wt = refl
  no-fvs-lemma n m ctxwf ctxct (TATLam wt) rewrite no-fvs-lemma n m (CtxWFTVar ctxwf) (CtxCtTVar ctxct) wt = refl
  no-fvs-lemma n m ctxwf ctxct (TAAp wt wt₁) rewrite no-fvs-lemma n m ctxwf ctxct wt rewrite no-fvs-lemma n m ctxwf ctxct wt₁ = refl
  no-fvs-lemma n m ctxwf ctxct (TATAp x wt x₁) rewrite no-fvs-lemma-type m ctxct x rewrite no-fvs-lemma n m ctxwf ctxct wt = refl
  no-fvs-lemma n m ctxwf ctxct TAEHole = refl
  no-fvs-lemma n m ctxwf ctxct (TANEHole wt) rewrite no-fvs-lemma n m ctxwf ctxct wt = refl
  no-fvs-lemma n m ctxwf ctxct (TACast wt x x₁) rewrite no-fvs-lemma-type m ctxct x rewrite no-fvs-lemma-type m ctxct (wf-ta ctxwf wt) rewrite no-fvs-lemma n m ctxwf ctxct wt = refl
  no-fvs-lemma n m ctxwf ctxct (TAFailedCast wt x x₁ x₂) rewrite no-fvs-lemma n m ctxwf ctxct wt rewrite no-fvs-lemma-type m ctxct (wf-gnd x) rewrite no-fvs-lemma-type m ctxct (wf-gnd x₁) = refl

  inctx-count1 : ∀{Γ n m τ1 τ2} → context-counter Γ n m → n , τ2 ∈ (Γ ctx+ (τ1 , ∅)) → τ2 == ↑ 0 m τ1
  inctx-count1 {τ1 = τ1} CtxCtEmpty InCtxZ rewrite ↑Z Z τ1 = refl
  inctx-count1 (CtxCtVar ctxct) (InCtx1+ inctx) = inctx-count1 ctxct inctx
  inctx-count1 {m = 1+ m} {τ1 = τ1} (CtxCtTVar ctxct) (InCtxSkip inctx) rewrite inctx-count1 ctxct inctx rewrite ↑compose Z m τ1 = refl

  inctx-count2 : ∀{Γ n m x τ1 τ2} → x ≠ n → context-counter Γ n m → x , τ2 ∈ (Γ ctx+ (τ1 , ∅)) → ↓Nat n 1 x , τ2 ∈ Γ
  inctx-count2 neq CtxCtEmpty InCtxZ = abort (neq refl)
  inctx-count2 neq (CtxCtVar ctxct) InCtxZ = InCtxZ
  inctx-count2 neq (CtxCtVar ctxct) (InCtx1+ inctx) = InCtx1+ (inctx-count2 (\{refl → neq refl}) ctxct inctx)
  inctx-count2 neq (CtxCtTVar ctxct) (InCtxSkip inctx) = InCtxSkip (inctx-count2 neq ctxct inctx)

  wt-ttSub-helper : ∀{Γ n m d1 d2 τ1 τ2} →
    (⊢ Γ ctxwf) →
    (context-counter Γ n m) → 
    (∅ ⊢ d1 :: τ1) → 
    ((Γ ctx+ (τ1 , ∅)) ⊢ d2 :: τ2) → 
    (Γ ⊢ ttSub n m d1 d2 :: τ2)
  wt-ttSub-helper ctxwf ctxct wt1 TAConst = TAConst
  wt-ttSub-helper ctxwf ctxct wt1 (TAAp wt2 wt3) = TAAp (wt-ttSub-helper ctxwf ctxct wt1 wt2) (wt-ttSub-helper ctxwf ctxct wt1 wt3)
  wt-ttSub-helper ctxwf ctxct wt1 (TATAp x wt2 x₁) = TATAp (strengthen-wf-var-reverse x) (wt-ttSub-helper ctxwf ctxct wt1 wt2) x₁
  wt-ttSub-helper ctxwf ctxct wt1 TAEHole = TAEHole 
  wt-ttSub-helper ctxwf ctxct wt1 (TANEHole wt2) = TANEHole (wt-ttSub-helper ctxwf ctxct wt1 wt2)
  wt-ttSub-helper ctxwf ctxct wt1 (TACast wt2 x x₁) = TACast (wt-ttSub-helper ctxwf ctxct wt1 wt2) (strengthen-wf-var-reverse x) x₁
  wt-ttSub-helper ctxwf ctxct wt1 (TAFailedCast wt2 x x₁ x₂) = TAFailedCast (wt-ttSub-helper ctxwf ctxct wt1 wt2) x x₁ x₂
  wt-ttSub-helper {Γ} {n} {m} {d1} ctxwf ctxct wt1 (TALam {τ1 = τ} {d = d} x wt2) = TALam (strengthen-wf-var-reverse x) (wt-ttSub-helper {Γ = (τ , Γ)} (CtxWFVar (strengthen-wf-var-reverse x) ctxwf) (CtxCtVar ctxct) wt1 wt2)
  wt-ttSub-helper {Γ} {n} {m} {d1} ctxwf ctxct wt1 (TATLam {d = d} wt2) = TATLam (wt-ttSub-helper {Γ = (TVar, Γ)} (CtxWFTVar ctxwf) (CtxCtTVar ctxct) wt1 wt2)
  wt-ttSub-helper {Γ} {n} {m} ctxwf ctxct wt1 (TAVar {n = x} inctx) with natEQ x n 
  wt-ttSub-helper {Γ} {n} {m} {d1} ctxwf ctxct wt1 (TAVar inctx) | Inl refl with wf-ta CtxWFEmpty wt1  
  ... | wf rewrite no-fvs-lemma n m CtxWFEmpty CtxCtEmpty wt1 rewrite inctx-count1 ctxct inctx rewrite no-fvs-lemma-type m CtxCtEmpty wf = weakening-wt wt1
  wt-ttSub-helper {Γ} {n} {m} ctxwf ctxct wt1 (TAVar {n = x} inctx) | Inr neq = TAVar (inctx-count2 neq ctxct inctx)
    
  wt-ttSub : ∀{d1 d2 τ1 τ2} →
    (∅ ⊢ d1 :: τ1) → 
    ((τ1 , ∅) ⊢ d2 :: τ2) → 
    (∅ ⊢ ttSub Z Z d1 d2 :: τ2)
  wt-ttSub = wt-ttSub-helper CtxWFEmpty CtxCtEmpty
      