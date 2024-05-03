{-# OPTIONS --no-termination-check #-}

open import Nat
open import Prelude
open import core
open import core-type
open import core-exp
open import core-subst

open import preservation
open import ground-dec
open import lemmas-consistency
open import lemmas-wf
open import eq-dec
open import lemmas-ground

module parametricity2 where
    
  mutual
    data _=0c_ : (d1 d2 : ihexp) → Set where 
      Eq0CastL : ∀{d1 d2 τ1 τ2} → d1 =0c d2 → (d1 ⟨ τ1 ⇒ τ2 ⟩) =0c d2
      Eq0FailedCastL : ∀{d1 d2 τ1 τ2} → d1 =0c d2 → (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) =0c d2
      Eq0NoLeft : ∀{d1 d2} → d1 =0cr d2 → d1 =0c d2
    
    data _=0cr_ : (d1 d2 : ihexp) → Set where
      Eq0CastR : ∀{d1 d2 τ1 τ2} → d1 =0cr d2 → d1 =0cr (d2 ⟨ τ1 ⇒ τ2 ⟩)
      Eq0FailedCastR : ∀{d1 d2 τ1 τ2} → d1 =0cr d2 → d1 =0cr (d2 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
      Eq0NoCasts : ∀{d1 d2} → d1 =0cn d2 → d1 =0cr d2

    data _=0cn_ : (d1 d2 : ihexp) → Set where
      Eq0Const : c =0cn c
      Eq0Var : ∀{x} → (X x) =0cn (X x) 
      Eq0EHole : ⦇-⦈ =0cn ⦇-⦈
      Eq0Lam : ∀{d1 d2 τ1 τ2} → d1 =0c d2 → (·λ[ τ1 ] d1) =0cn (·λ[ τ2 ] d2)
      Eq0TLam : ∀{d1 d2} → d1 =0c d2 → (·Λ d1) =0cn (·Λ d2)
      Eq0NEHole : ∀{d1 d2} → d1 =0c d2 →  ⦇⌜ d1 ⌟⦈ =0cn ⦇⌜ d2 ⌟⦈
      Eq0Ap :  ∀{d1 d2 d3 d4} → d1 =0c d3 →  d2 =0c d4 →  (d1 ∘ d2) =0cn (d3 ∘ d4)
      Eq0TAp : ∀{d1 d2 τ1 τ2} → d1 =0c d2 → (d1 < τ1 >) =0cn (d2 < τ2 >)

    data _=0εc_ : (ε1 ε2 : ectx) → Set where 
      Eq0Dot : ⊙ =0εc ⊙
      Eq0Ap1 : ∀{ε1 ε2 d1 d2} → (ε1 =0εc ε2) → (d1 =0c d2) → (ε1 ∘₁ d1) =0εc (ε2 ∘₁ d2)
      Eq0Ap2 : ∀{ε1 ε2 d1 d2} → (ε1 =0εc ε2) → (d1 =0c d2) → (d1 ∘₂ ε1) =0εc (d2 ∘₂ ε2)
      Eq0TAp : ∀{ε1 ε2 τ1 τ2} → (ε1 =0εc ε2) → (ε1 < τ1 >) =0εc (ε2 < τ2 >)
      Eq0NEHole : ∀{ε1 ε2} → (ε1 =0εc ε2) → ⦇⌜ ε1 ⌟⦈ =0εc ⦇⌜ ε2 ⌟⦈
      Eq0CastL : ∀{ε1 ε2 τ1 τ2} → (ε1 =0εc ε2) → (ε1 ⟨ τ1 ⇒ τ2 ⟩) =0εc ε2
      Eq0CastR : ∀{ε1 ε2 τ1 τ2} → (ε1 =0εc ε2) → ε1 =0εc (ε2 ⟨ τ1 ⇒ τ2 ⟩)
      Eq0FailedCastL : ∀{ε1 ε2 τ1 τ2} → (ε1 =0εc ε2) → (ε1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) =0εc ε2
      Eq0FailedCastR : ∀{ε1 ε2 τ1 τ2} → (ε1 =0εc ε2) → ε1 =0εc (ε2 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)

  eq0cr-lemma : ∀{d d' τ τ'} → 
    d =0c d' → d =0c (d' ⟨ τ ⇒ τ' ⟩)
  eq0cr-lemma (Eq0CastL eq0) = Eq0CastL (eq0cr-lemma eq0)
  eq0cr-lemma (Eq0FailedCastL eq0) = Eq0FailedCastL (eq0cr-lemma eq0)
  eq0cr-lemma (Eq0NoLeft x) = Eq0NoLeft (Eq0CastR x)

  eq0cr-lemma' : ∀{d d' τ τ'} → 
    d =0c d' → d =0c (d' ⟨ τ ⇒⦇-⦈⇏ τ' ⟩)
  eq0cr-lemma' (Eq0CastL eq0) = Eq0CastL (eq0cr-lemma' eq0)
  eq0cr-lemma' (Eq0FailedCastL eq0) = Eq0FailedCastL (eq0cr-lemma' eq0)
  eq0cr-lemma' (Eq0NoLeft x) = Eq0NoLeft (Eq0FailedCastR x)

  eq0c-refl : ∀{d : ihexp} → d =0c d
  eq0c-refl {c} = Eq0NoLeft (Eq0NoCasts Eq0Const)
  eq0c-refl {X x} = Eq0NoLeft (Eq0NoCasts Eq0Var)
  eq0c-refl {·λ[ x ] d} = Eq0NoLeft (Eq0NoCasts (Eq0Lam eq0c-refl))
  eq0c-refl {·Λ d} = Eq0NoLeft (Eq0NoCasts (Eq0TLam eq0c-refl))
  eq0c-refl {⦇-⦈} = Eq0NoLeft (Eq0NoCasts Eq0EHole)
  eq0c-refl {⦇⌜ d ⌟⦈} = Eq0NoLeft (Eq0NoCasts (Eq0NEHole eq0c-refl))
  eq0c-refl {d ∘ d₁} = Eq0NoLeft (Eq0NoCasts (Eq0Ap eq0c-refl eq0c-refl))
  eq0c-refl {d < x >} = Eq0NoLeft (Eq0NoCasts (Eq0TAp eq0c-refl))
  eq0c-refl {d ⟨ x ⇒ x₁ ⟩} = Eq0CastL (eq0cr-lemma eq0c-refl)
  eq0c-refl {d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} = Eq0FailedCastL (eq0cr-lemma' eq0c-refl)

  mutual
    eq0cn-sym : ∀{d d'} →
      d =0cn d' →
      d' =0cn d
    eq0cn-sym Eq0Const = Eq0Const
    eq0cn-sym Eq0Var = Eq0Var
    eq0cn-sym Eq0EHole = Eq0EHole
    eq0cn-sym (Eq0Lam x) = Eq0Lam (eq0c-sym x)
    eq0cn-sym (Eq0TLam x) = Eq0TLam (eq0c-sym x)
    eq0cn-sym (Eq0NEHole x) = Eq0NEHole (eq0c-sym x)
    eq0cn-sym (Eq0Ap x x₁) = Eq0Ap (eq0c-sym x) (eq0c-sym x₁)
    eq0cn-sym (Eq0TAp x) = Eq0TAp (eq0c-sym x)

    eq0cr-sym : ∀{d d'} →
      d =0cr d' →
      d' =0c d
    eq0cr-sym (Eq0NoCasts x) = Eq0NoLeft (Eq0NoCasts (eq0cn-sym x))
    eq0cr-sym (Eq0CastR eq0) = Eq0CastL (eq0cr-sym eq0)
    eq0cr-sym (Eq0FailedCastR eq0) = Eq0FailedCastL (eq0cr-sym eq0)

    eq0c-sym : ∀{d d'} →
      d =0c d' →
      d' =0c d
    eq0c-sym (Eq0CastL eq0) = eq0cr-lemma (eq0c-sym eq0)
    eq0c-sym (Eq0FailedCastL eq0) = eq0cr-lemma' (eq0c-sym eq0)
    eq0c-sym (Eq0NoLeft x) = eq0cr-sym x
  
  mutual
    eq0cn-trans : ∀{d d' d''} →
      d =0cn d' →
      d' =0cn d'' →
      d =0cn d''
    eq0cn-trans Eq0Const Eq0Const = Eq0Const
    eq0cn-trans Eq0Var Eq0Var = Eq0Var
    eq0cn-trans Eq0EHole Eq0EHole = Eq0EHole
    eq0cn-trans (Eq0Lam x) (Eq0Lam x₁) = Eq0Lam (eq0c-trans x x₁)
    eq0cn-trans (Eq0TLam x) (Eq0TLam x₁) = Eq0TLam (eq0c-trans x x₁)
    eq0cn-trans (Eq0NEHole x) (Eq0NEHole x₁) = Eq0NEHole (eq0c-trans x x₁)
    eq0cn-trans (Eq0Ap x x₁) (Eq0Ap x₂ x₃) = Eq0Ap (eq0c-trans x x₂) (eq0c-trans x₁ x₃)
    eq0cn-trans (Eq0TAp x) (Eq0TAp x₁) = Eq0TAp (eq0c-trans x x₁)

    eq0c-trans : ∀{d d' d''} →
      d =0c d' →
      d' =0c d'' →
      d =0c d''
    eq0c-trans eq0 eq0' = {!   !}

  mutual
    eq0cnr-trans : ∀{d d' d''} →
      d =0cn d' →
      d' =0c d'' →
      d =0cr d''
    eq0cnr-trans eqn (Eq0NoLeft x) = eq0cnrr-trans eqn x

    eq0cnrr-trans : ∀{d d' d''} →
      d =0cn d' →
      d' =0cr d'' →
      d =0cr d''
    eq0cnrr-trans eqn (Eq0CastR eqr) = Eq0CastR (eq0cnrr-trans eqn eqr)
    eq0cnrr-trans eqn (Eq0FailedCastR eqr) = Eq0FailedCastR (eq0cnrr-trans eqn eqr)
    eq0cnrr-trans eqn (Eq0NoCasts x) = Eq0NoCasts (eq0cn-trans eqn x)

  eq0ε''-sym : ∀{e e' : ectx} → e =0εc e' → e' =0εc e
  eq0ε''-sym Eq0Dot = Eq0Dot
  eq0ε''-sym (Eq0Ap1 eqe x) = Eq0Ap1 (eq0ε''-sym eqe) (eq0c-sym x)
  eq0ε''-sym (Eq0Ap2 eqe x) = Eq0Ap2 (eq0ε''-sym eqe) (eq0c-sym x)
  eq0ε''-sym (Eq0TAp eqe) = Eq0TAp (eq0ε''-sym eqe)
  eq0ε''-sym (Eq0NEHole eqe) = Eq0NEHole (eq0ε''-sym eqe)
  eq0ε''-sym (Eq0CastL eqe) = Eq0CastR (eq0ε''-sym eqe)
  eq0ε''-sym (Eq0CastR eqe) = Eq0CastL (eq0ε''-sym eqe)
  eq0ε''-sym (Eq0FailedCastL eqe) = Eq0FailedCastR (eq0ε''-sym eqe)
  eq0ε''-sym (Eq0FailedCastR eqe) = Eq0FailedCastL (eq0ε''-sym eqe)

  eq0-ctxinc : 
    ∀ {d1 d2 d1' ε1} →
    d1 =0c d2 →
    d1 == ε1 ⟦ d1' ⟧ →
    Σ[ d2' ∈ ihexp ] Σ[ ε2 ∈ ectx ] ((d2 == ε2 ⟦ d2' ⟧) × (d1' =0c d2') × (ε1 =0εc ε2))
  eq0-ctxinc = {!   !}

  eq0c-ctxout : 
    ∀ {d1 d1' d2' ε1 ε2} →
    d1' =0c d2' →
    ε1 =0εc ε2 →
    d1 == ε1 ⟦ d1' ⟧ →
    Σ[ d2 ∈ ihexp ] ((d2 == ε2 ⟦ d2' ⟧) × (d1 =0c d2))
  eq0c-ctxout = {!   !}

  eq0ccastr-meaning : ∀{d d' d₀ τ τ'} →
    d =0cr d' →
    d ≠ (d₀ ⟨ τ ⇒ τ' ⟩) × d ≠ (d₀ ⟨ τ ⇒⦇-⦈⇏ τ' ⟩)
  eq0ccastr-meaning = {!   !}

  mutual
    eq0cn-ctx : ∀{d0 d0' d1 d1' d2 d2' ε1 ε2} →
      d1 == ε1 ⟦ d0 ⟧ →
      d1' == ε1 ⟦ d0' ⟧ →
      d2 == ε2 ⟦ d2' ⟧ → 
      ε1 =0εc ε2 →
      d0 =0c d0' →
      d1 =0cn d2 →
      d1' =0c d2
    eq0cn-ctx FHOuter FHOuter ctx2 eqe eqin eq0 = eq0c-trans (eq0c-sym eqin) (Eq0NoLeft (Eq0NoCasts eq0))
    eq0cn-ctx (FHAp1 ctx1) (FHAp1 ctx1') (FHAp1 ctx2) (Eq0Ap1 eqe x₂) eqin (Eq0Ap x x₁) = 
      Eq0NoLeft (Eq0NoCasts (Eq0Ap 
        (eq0c-ctx ctx1 ctx1' ctx2 eqe eqin x) x₁))
    eq0cn-ctx (FHAp2 ctx1) (FHAp2 ctx1') (FHAp2 ctx2) (Eq0Ap2 eqe x₂) eqin (Eq0Ap x x₁) = Eq0NoLeft (Eq0NoCasts (Eq0Ap x (eq0c-ctx ctx1 ctx1' ctx2 eqe eqin x₁)))
    eq0cn-ctx (FHTAp ctx1) (FHTAp ctx1') (FHTAp ctx2) (Eq0TAp eqe) eqin (Eq0TAp x) = Eq0NoLeft (Eq0NoCasts (Eq0TAp (eq0c-ctx ctx1 ctx1' ctx2 eqe eqin x)))
    eq0cn-ctx (FHNEHole ctx1) (FHNEHole ctx1') (FHNEHole ctx2) (Eq0NEHole eqe) eqin (Eq0NEHole x) = Eq0NoLeft (Eq0NoCasts (Eq0NEHole (eq0c-ctx ctx1 ctx1' ctx2 eqe eqin x)))


    eq0cr-ctx : ∀{d0 d0' d1 d1' d2 d2' ε1 ε2} →
      d1 == ε1 ⟦ d0 ⟧ →
      d1' == ε1 ⟦ d0' ⟧ →
      d2 == ε2 ⟦ d2' ⟧ → 
      ε1 =0εc ε2 →
      d0 =0c d0' →
      d1 =0cr d2 →
      d1' =0c d2
    eq0cr-ctx ctx1 ctx1' ctx2 eqe eqin eq0 = {!   !}

    eq0c-ctx : ∀{d0 d0' d1 d1' d2 d2' ε1 ε2} →
      d1 == ε1 ⟦ d0 ⟧ →
      d1' == ε1 ⟦ d0' ⟧ →
      d2 == ε2 ⟦ d2' ⟧ → 
      ε1 =0εc ε2 →
      d0 =0c d0' →
      d1 =0c d2 →
      d1' =0c d2
    eq0c-ctx ctx1 ctx1' ctx2 eqe eqin eq0 = {!   !}

  cast-steps-preserve-=0c : ∀{d1 d1' d2 τ1 τ2} →
    (d1 ⟨ τ1 ⇒ τ2 ⟩) →> d1' →
    d1 =0c d2 →
    d1' =0c d2
  cast-steps-preserve-=0c ITCastID eq0 = eq0
  cast-steps-preserve-=0c (ITCastSucceed x) (Eq0CastL eq0) = eq0
  cast-steps-preserve-=0c (ITCastSucceed x) (Eq0NoLeft x₃) = {!   !} -- impossible case noleft meaning
  cast-steps-preserve-=0c (ITCastFail x x₁ x₂) (Eq0CastL eq0) = Eq0FailedCastL eq0
  cast-steps-preserve-=0c (ITCastFail x x₁ x₂) (Eq0NoLeft x₃) = {!   !} -- impossible case by noleft meaning
  cast-steps-preserve-=0c (ITGround x) eq0 = Eq0CastL (Eq0CastL eq0)
  cast-steps-preserve-=0c (ITExpand x) eq0 = Eq0CastL (Eq0CastL eq0)

  eq0-substc : 
    ∀ {d1 d2} →
    (d3 d4 : ihexp) →
    d1 =0c d2 →
    d3 =0c d4 →
    (ttSub Z Z d1 d3) =0c (ttSub Z Z d2 d4)
  eq0-substc = {!   !}



  eq-ctx-eq : ∀{ε d d1 d2} →
    d1 == ε ⟦ d ⟧ → d2 == ε ⟦ d ⟧ →
    d1 == d2
  eq-ctx-eq FHOuter FHOuter = refl
  eq-ctx-eq (FHAp1 ctx1) (FHAp1 ctx2) rewrite eq-ctx-eq ctx1 ctx2 = refl
  eq-ctx-eq (FHAp2 ctx1) (FHAp2 ctx2) rewrite eq-ctx-eq ctx1 ctx2 = refl
  eq-ctx-eq (FHTAp ctx1) (FHTAp ctx2) rewrite eq-ctx-eq ctx1 ctx2 = refl
  eq-ctx-eq (FHNEHole ctx1) (FHNEHole ctx2) rewrite eq-ctx-eq ctx1 ctx2 = refl
  eq-ctx-eq (FHCast ctx1) (FHCast ctx2) rewrite eq-ctx-eq ctx1 ctx2 = refl
  eq-ctx-eq (FHFailedCast ctx1) (FHFailedCast ctx2) rewrite eq-ctx-eq ctx1 ctx2 = refl

  evalctx-compose-func : (ε ε' : ectx) → ectx
  evalctx-compose-func ⊙ e2 = e2
  evalctx-compose-func (e1 ∘₁ x) e2 = ((evalctx-compose-func e1 e2) ∘₁ x)
  evalctx-compose-func (x ∘₂ e1) e2 = (x ∘₂ (evalctx-compose-func e1 e2))
  evalctx-compose-func (e1 < x >) e2 = ((evalctx-compose-func e1 e2) < x >)
  evalctx-compose-func ⦇⌜ e1 ⌟⦈ e2 = ⦇⌜ (evalctx-compose-func e1 e2) ⌟⦈
  evalctx-compose-func (e1 ⟨ x ⇒ x₁ ⟩) e2 = ((evalctx-compose-func e1 e2) ⟨ x ⇒ x₁ ⟩)
  evalctx-compose-func (e1 ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) e2 = ((evalctx-compose-func e1 e2) ⟨ x ⇒⦇-⦈⇏ x₁ ⟩)

  evalctx-compose : ∀{d d' d'' ε ε'} →
    d == ε ⟦ d' ⟧ →
    d' == ε' ⟦ d'' ⟧ →
    (d == (evalctx-compose-func ε ε') ⟦ d'' ⟧)
  evalctx-compose FHOuter ec2 = ec2
  evalctx-compose (FHAp1 ec1) ec2 = FHAp1 (evalctx-compose ec1 ec2)
  evalctx-compose (FHAp2 ec1) ec2 = FHAp2 (evalctx-compose ec1 ec2)
  evalctx-compose (FHTAp ec1) ec2 = FHTAp (evalctx-compose ec1 ec2)
  evalctx-compose (FHNEHole ec1) ec2 = FHNEHole (evalctx-compose ec1 ec2)
  evalctx-compose (FHCast ec1) ec2 = FHCast (evalctx-compose ec1 ec2)
  evalctx-compose (FHFailedCast ec1) ec2 = FHFailedCast (evalctx-compose ec1 ec2)

  evalctx-uncompose : ∀{d d' d'' ε ε'} →
    (d == (evalctx-compose-func ε ε') ⟦ d'' ⟧) →
    d' == ε' ⟦ d'' ⟧ →
    d == ε ⟦ d' ⟧
  evalctx-uncompose {ε = ⊙} ec1 ec2 rewrite eq-ctx-eq ec1 ec2 = FHOuter
  evalctx-uncompose {ε = ε ∘₁ x} (FHAp1 ec1) ec2 = FHAp1 (evalctx-uncompose ec1 ec2)
  evalctx-uncompose {ε = x ∘₂ ε} (FHAp2 ec1) ec2 = FHAp2 (evalctx-uncompose ec1 ec2)
  evalctx-uncompose {ε = ε < x >} (FHTAp ec1) ec2 = FHTAp (evalctx-uncompose ec1 ec2)
  evalctx-uncompose {ε = ⦇⌜ ε ⌟⦈} (FHNEHole ec1) ec2 = FHNEHole (evalctx-uncompose ec1 ec2)
  evalctx-uncompose {ε = ε ⟨ x ⇒ x₁ ⟩} (FHCast ec1) ec2 = FHCast (evalctx-uncompose ec1 ec2)
  evalctx-uncompose {ε = ε ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} (FHFailedCast ec1) ec2 = FHFailedCast (evalctx-uncompose ec1 ec2)

  evalctx-out : ∀{d d1 ε} →
    (d2 : ihexp) → 
    d == ε ⟦ d1 ⟧ →
    Σ[ d' ∈ ihexp ] (d' == ε ⟦ d2 ⟧)
  evalctx-out d2 ec = {!   !}

  evalctx-compose-ms : ∀{d d' din din' ε} →
    din ↦* din' →
    d == ε ⟦ din ⟧ →
    d' == ε ⟦ din' ⟧ →
    d ↦* d'
  evalctx-compose-ms MSRefl ctxin ctxout with eq-ctx-eq ctxin ctxout
  ... | refl = MSRefl
  evalctx-compose-ms (MSStep (Step {d0 = d0} {d0' = d0'} x x₁ x₂) ms) ctxin ctxout with evalctx-out d0' (evalctx-compose ctxin x)
  ... | d'' , ctxmid = MSStep (Step (evalctx-compose ctxin x) x₁ ctxmid) (evalctx-compose-ms ms (evalctx-uncompose ctxmid x₂) ctxout)


  val-cast-final : ∀{d τ1 τ2} →
    d val → ∅ ⊢ d :: τ1 → ∅ ⊢ τ1 wf → ∅ ⊢ τ2 wf → τ1 ≠ τ2 → τ1 ~ τ2 → 
    Σ[ d' ∈ ihexp ] ((d ⟨ τ1 ⇒ τ2 ⟩) =0c d' × ((d ⟨ τ1 ⇒ τ2 ⟩) ↦* d') × d' final)
  val-cast-final v wt wf1 wf2 neq ConsistBase = abort (neq refl)
  val-cast-final v wt wf1 wf2 neq ConsistVar = abort (neq refl)
  val-cast-final {τ1 = τ1} v wt wf1 wf2 neq ConsistHole1 with ground-dec τ1
  ... | Inl gnd = _ , eq0c-refl , MSRefl , FBoxedVal (BVHoleCast gnd (BVVal v))
  val-cast-final {τ1 = b} v wt wf1 wf2 neq ConsistHole1 | Inr gnd = abort (gnd GBase)
  val-cast-final {τ1 = T x} v wt () wf2 neq ConsistHole1 | Inr gnd
  val-cast-final {τ1 = ⦇-⦈} v wt wf1 wf2 neq ConsistHole1 | Inr gnd = abort (neq refl)
  val-cast-final {τ1 = τ1 ==> τ2} v wt wf1 wf2 neq ConsistHole1 | Inr gnd with htyp-eq-dec (τ1 ==> τ2) (⦇-⦈ ==> ⦇-⦈)
  ... | Inl refl = abort (gnd GArr)
  ... | Inr neq' = _ , Eq0CastL (eq0cr-lemma (eq0cr-lemma eq0c-refl)) , MSStep (Step FHOuter (ITGround (MGArr neq')) FHOuter) MSRefl , FBoxedVal (BVHoleCast GArr (BVArrCast neq' (BVVal v)))
  val-cast-final {τ1 = ·∀ τ1} v wt wf1 wf2 neq ConsistHole1 | Inr gnd with htyp-eq-dec (·∀ τ1) (·∀ ⦇-⦈)
  ... | Inl refl = abort (gnd GForall)
  ... | Inr neq' = _ , Eq0CastL (eq0cr-lemma (eq0cr-lemma eq0c-refl)) , MSStep (Step FHOuter (ITGround (MGForall neq')) FHOuter) MSRefl , FBoxedVal (BVHoleCast GForall (BVForallCast neq' (BVVal v)))
  val-cast-final VConst () wf1 wf2 neq ConsistHole2
  val-cast-final VLam () wf1 wf2 neq ConsistHole2
  val-cast-final VTLam () wf1 wf2 neq ConsistHole2
  val-cast-final v wt wf1 wf2 neq (ConsistArr consis consis₁) = _ , eq0c-refl , MSRefl , FBoxedVal (BVArrCast neq (BVVal v))
  val-cast-final v wt wf1 wf2 neq (ConsistForall consis) = _ , eq0c-refl , MSRefl , FBoxedVal (BVForallCast neq (BVVal v))

  eq0cn-val-val : ∀{d d'} →
    d val → d =0cn d' → d' val
  eq0cn-val-val VConst Eq0Const = VConst
  eq0cn-val-val VLam (Eq0Lam x) = VLam
  eq0cn-val-val VTLam (Eq0TLam x) = VTLam

  mstrans : ∀{d d' d''} →
    d ↦* d' → d' ↦* d'' → d ↦* d''
  mstrans = {!   !}

  preservation-trans : ∀ { d d' τ } →
    ∅ ⊢ d :: τ →
    d ↦* d' →
    ∅ ⊢ d' :: τ
  preservation-trans = {!   !}

  fin-arr-lemma : ∀{d τ1 τ2 τ3 τ4} →
    d final → τ1 ==> τ2 ≠ τ3 ==> τ4 → (d ⟨ τ1 ==> τ2 ⇒ τ3 ==> τ4 ⟩) final
  fin-arr-lemma (FBoxedVal x) ne = FBoxedVal (BVArrCast ne x)
  fin-arr-lemma (FIndet x) ne = FIndet (ICastArr ne x)

  fin-forall-lemma : ∀{d τ1 τ2 } →
    d final → ·∀ τ1 ≠ ·∀ τ2 → (d ⟨ ·∀ τ1 ⇒ ·∀ τ2 ⟩) final
  fin-forall-lemma (FBoxedVal x) ne = FBoxedVal (BVForallCast ne x)
  fin-forall-lemma (FIndet x) ne = FIndet (ICastForall ne x)

  fin-gndhole-lemma : ∀{d τ} →
    d final → τ ground → (d ⟨ τ ⇒ ⦇-⦈ ⟩) final
  fin-gndhole-lemma (FBoxedVal x) gnd = FBoxedVal (BVHoleCast gnd x)
  fin-gndhole-lemma (FIndet x) gnd = FIndet (ICastGroundHole gnd x)

  fin-gndhole-lemma' : ∀{d τ} →
     (d ⟨ τ ⇒ ⦇-⦈ ⟩) final → d final
  fin-gndhole-lemma' (FBoxedVal (BVHoleCast x x₁)) = FBoxedVal x₁
  fin-gndhole-lemma' (FIndet (ICastGroundHole x x₁)) = FIndet x₁

  {- These inductions are valid because the syntactic size decreases every time except in the expand+ground case -}
  useless-cast-cases : ∀{d d1 τ2} →
    d1 =0cr d → ∅ ⊢ τ2 wf → τ2 ≠ ⦇-⦈ →
    ∅ ⊢ d :: ⦇-⦈ →
    ((d' : ihexp) → (τ τ' : htyp) → d ≠ (d' ⟨ τ ⇒ τ' ⟩)) → d final →
    Σ[ d' ∈ ihexp ] ( (d1 =0cr d') × ((d ⟨ ⦇-⦈ ⇒ τ2 ⟩) ⟨ τ2 ⇒ ⦇-⦈ ⟩) ↦* d' × d' final)
  useless-cast-cases {τ2 = τ2} eq0 _ _ () form (FBoxedVal (BVVal VConst))
  useless-cast-cases {τ2 = τ2} eq0 _ _ () form (FBoxedVal (BVVal VLam))
  useless-cast-cases {τ2 = τ2} eq0 _ _ () form (FBoxedVal (BVVal VTLam))
  useless-cast-cases {τ2 = τ2} eq0 _ _ wt form (FBoxedVal (BVHoleCast {τ = τ} {d = d} x x₁)) = abort (form d τ ⦇-⦈ refl)
  useless-cast-cases {τ2 = τ2} eq0 wf ne wt form (FIndet x) with ground-dec τ2
  ... | Inl gnd = _ , Eq0CastR (Eq0CastR eq0) , MSRefl , fin-gndhole-lemma (FIndet (ICastHoleGround (λ d' τ' → form d' τ' ⦇-⦈) x gnd)) gnd
  ... | Inr gnd with ground-match-exists gnd wf ne 
  useless-cast-cases {τ2 = τ2 ==> τ3} eq0 wf ne wt form (FIndet x) | Inr gnd | τ' ==> τ'' , gnd' = _ , Eq0CastR (Eq0CastR (Eq0CastR (Eq0CastR eq0))) , 
    MSStep (Step (FHCast FHOuter) (ITExpand gnd') (FHCast FHOuter)) (MSStep (Step FHOuter (ITGround gnd') FHOuter) MSRefl) ,
    FIndet (ICastGroundHole (ground-match gnd') (ICastArr (ground-match-neq gnd') (ICastArr (flip (ground-match-neq gnd')) (ICastHoleGround (λ d' τ' → form d' τ' ⦇-⦈) x (ground-match gnd')))))
  useless-cast-cases {τ2 = ·∀ τ2} eq0 wf ne wt form (FIndet x) | Inr gnd | ·∀ τ' , gnd' = _ , Eq0CastR (Eq0CastR (Eq0CastR (Eq0CastR eq0))) , 
    MSStep (Step (FHCast FHOuter) (ITExpand gnd') (FHCast FHOuter)) (MSStep (Step FHOuter (ITGround gnd') FHOuter) MSRefl) , 
    FIndet (ICastGroundHole (ground-match gnd') (ICastForall (ground-match-neq gnd') (ICastForall (flip (ground-match-neq gnd')) (ICastHoleGround (λ d' τ' → form d' τ' ⦇-⦈) x (ground-match gnd')))))

  mutual
    parametricity-onesided-lemma-doublecast-case : ∀{d1 τ d2 τ1 τ2 τ3} →
      τ1 ≠ τ2 → τ2 ≠ τ3 → τ2 ≠ ⦇-⦈ →
      ∅ ⊢ d1 :: τ →
      ∅ ⊢ (d2 ⟨ τ1 ⇒ τ2 ⟩) ⟨ τ2 ⇒ τ3 ⟩ :: τ3 →
      d1 =0cr d2 →
      d1 val →
      d2 final →
      Σ[ d2' ∈ ihexp ] (d1 =0cr d2' × ((d2 ⟨ τ1 ⇒ τ2 ⟩) ⟨ τ2 ⇒ τ3 ⟩)↦* d2' × d2' final)
    parametricity-onesided-lemma-doublecast-case {τ1 = τ1} {τ3 = _} neq neq' neq'' wt1 (TACast (TACast wt2 x₂ x₃) x ConsistHole2) eq0 v fin = abort (neq'' refl)
    parametricity-onesided-lemma-doublecast-case {τ1 = τ1} {τ3 = b} neq neq' neq'' wt1 (TACast (TACast wt2 x₂ x₃) x ConsistBase) eq0 v fin = abort (neq' refl)
    parametricity-onesided-lemma-doublecast-case {τ1 = .b} {τ2 = b} {τ3 = ⦇-⦈} neq neq' neq'' wt1 (TACast (TACast wt2 x₂ ConsistBase) x x₁) eq0 v fin = abort (neq refl)
    parametricity-onesided-lemma-doublecast-case {τ1 = τ1} {τ2 = ⦇-⦈} {τ3 = ⦇-⦈} neq neq' neq'' wt1 (TACast (TACast wt2 x₂ x₃) x x₁) eq0 v fin = abort (neq' refl)
    parametricity-onesided-lemma-doublecast-case {τ1 = .⦇-⦈} {τ2 = τ2} {τ3 = ⦇-⦈} neq neq' neq'' wt1 (TACast wt2₀@(TACast (TACast wt2 x₃ x₄) x₂ ConsistHole2) x x₁) (Eq0CastR eq0) v fin 
      with parametricity-onesided-lemma-holecast-case wt1 wt2₀ eq0 v (fin-gndhole-lemma' fin)
    ... | d2' , eq0' , steps , fin with ground-dec τ2
    ...   | Inl gnd = _ , Eq0CastR eq0' , evalctx-compose-ms steps (FHCast FHOuter) (FHCast FHOuter) , fin-gndhole-lemma fin gnd
    ...   | Inr gnd with ground-match-exists gnd x₂ neq''
    parametricity-onesided-lemma-doublecast-case {τ = _} {_} {.⦇-⦈} {τ2 = τ2 ==> τ3} {⦇-⦈} neq neq' neq'' wt1 (TACast (TACast (TACast wt2 x₃ x₄) x₂ ConsistHole2) x x₁) (Eq0CastR eq0) v fin₁
      | d2' , eq0' , steps , fin | Inr gnd | (_ ==> _) , gnd' = _ , Eq0CastR (Eq0CastR eq0') , MSStep (Step FHOuter (ITGround gnd') FHOuter) (evalctx-compose-ms steps (FHCast (FHCast FHOuter)) (FHCast (FHCast FHOuter))) , fin-gndhole-lemma (fin-arr-lemma fin (ground-match-neq gnd')) (ground-match gnd')
    parametricity-onesided-lemma-doublecast-case {τ = _} {_} {.⦇-⦈} {τ2 = ·∀ τ2} {⦇-⦈} neq neq' neq'' wt1 (TACast (TACast (TACast wt2 x₃ x₄) x₂ ConsistHole2) x x₁) (Eq0CastR eq0) v fin₁
      | d2' , eq0' , steps , fin | Inr gnd | (·∀ _) , gnd' = _ , Eq0CastR (Eq0CastR eq0') , MSStep (Step FHOuter (ITGround gnd') FHOuter) (evalctx-compose-ms steps (FHCast (FHCast FHOuter)) (FHCast (FHCast FHOuter))) , fin-gndhole-lemma (fin-forall-lemma fin (ground-match-neq gnd')) (ground-match gnd')
    parametricity-onesided-lemma-doublecast-case {τ1 = .⦇-⦈} {τ2 = τ2} {τ3 = ⦇-⦈} neq neq' neq'' wt1 (TACast (TACast (TAAp wt2 wt3) x₂ ConsistHole2) x x₁) eq0 v (FBoxedVal (BVVal ()))
    parametricity-onesided-lemma-doublecast-case {τ1 = .⦇-⦈} {τ2 = τ2} {τ3 = ⦇-⦈} neq neq' neq'' wt1 (TACast (TACast (TATAp x₃ wt2 x₄) x₂ ConsistHole2) x x₁) eq0 v (FBoxedVal (BVVal ()))
    parametricity-onesided-lemma-doublecast-case {τ1 = .⦇-⦈} {τ2 = τ2} {τ3 = ⦇-⦈} neq neq' neq'' wt1 (TACast (TACast (TAAp wt2 wt3) x₂ ConsistHole2) x x₁) eq0 v (FIndet x₃) with ground-dec τ2
    ... | Inl gnd = _ , Eq0CastR (Eq0CastR eq0) , MSRefl , FIndet (ICastGroundHole gnd (ICastHoleGround (λ d' τ' ()) x₃ gnd))
    ... | Inr gnd with ground-match-exists gnd x₂ neq''
    parametricity-onesided-lemma-doublecast-case {τ = _} {_} {.⦇-⦈} {τ2 = τ2 ==> τ3} {⦇-⦈} neq neq' neq'' wt1 (TACast (TACast (TAAp wt2 wt3) x₂ ConsistHole2) x x₁) eq0 v (FIndet x₃) | Inr gnd | (τ2' ==> τ2'') , gnd' =
      _ , Eq0CastR (Eq0CastR (Eq0CastR (Eq0CastR eq0))) , MSStep (Step (FHCast FHOuter) (ITExpand gnd') (FHCast FHOuter)) (MSStep (Step FHOuter (ITGround gnd') FHOuter) MSRefl) , FIndet (ICastGroundHole (ground-match gnd') (ICastArr (ground-match-neq gnd') (ICastArr (flip (ground-match-neq gnd')) (ICastHoleGround (λ d' τ' ()) x₃ (ground-match gnd')))))
    parametricity-onesided-lemma-doublecast-case {τ = _} {_} {.⦇-⦈} {τ2 = ·∀ τ2} {⦇-⦈} neq neq' neq'' wt1 (TACast (TACast (TAAp wt2 wt3) x₂ ConsistHole2) x x₁) eq0 v (FIndet x₃) | Inr gnd | (·∀ τ2') , gnd' =
      _ , Eq0CastR (Eq0CastR (Eq0CastR (Eq0CastR eq0))) ,  MSStep (Step (FHCast FHOuter) (ITExpand gnd') (FHCast FHOuter)) (MSStep (Step FHOuter (ITGround gnd') FHOuter) MSRefl) , FIndet (ICastGroundHole (ground-match gnd') (ICastForall (ground-match-neq gnd') (ICastForall (flip (ground-match-neq gnd')) (ICastHoleGround (λ d' τ' ()) x₃ (ground-match gnd')))))
    parametricity-onesided-lemma-doublecast-case {τ1 = .⦇-⦈} {τ2 = τ2} {τ3 = ⦇-⦈} neq neq' neq'' wt1 (TACast (TACast (TATAp x₃ wt2 x₄) x₂ ConsistHole2) x x₁) eq0 v (FIndet x₅) = useless-cast-cases eq0 x₂ neq'' (TATAp x₃ wt2 x₄) (λ d' τ τ' ()) (FIndet x₅)
    parametricity-onesided-lemma-doublecast-case {τ1 = .⦇-⦈} {τ2 = τ2} {τ3 = ⦇-⦈} neq neq' neq'' wt1 (TACast (TACast TAEHole x₂ ConsistHole2) x x₁) eq0 v fin = useless-cast-cases eq0 x₂ neq'' TAEHole (λ d' τ τ' ()) fin
    parametricity-onesided-lemma-doublecast-case {τ1 = .⦇-⦈} {τ2 = τ2} {τ3 = ⦇-⦈} neq neq' neq'' wt1 (TACast (TACast (TANEHole wt2) x₂ ConsistHole2) x x₁) eq0 v fin = useless-cast-cases eq0 x₂ neq'' (TANEHole wt2) (λ d' τ τ' ()) fin
    parametricity-onesided-lemma-doublecast-case {τ1 = τ1 ==> τ1'} {τ2 = τ2 ==> τ3} {τ3 = ⦇-⦈} neq neq' neq'' wt1 (TACast (TACast wt2 x₂ (ConsistArr x₃ x₄)) x x₁) eq0 v fin with ground-dec (τ2 ==> τ3)
    ... | Inl gnd = _ , Eq0CastR (Eq0CastR eq0) , MSRefl , fin-gndhole-lemma (fin-arr-lemma fin neq) gnd
    ... | Inr gnd with ground-match-exists gnd x₂ neq''
    ...   | (τ2' ==> τ3') , gnd' = _ , Eq0CastR (Eq0CastR (Eq0CastR eq0)) , MSStep (Step FHOuter (ITGround gnd') FHOuter) MSRefl , fin-gndhole-lemma (fin-arr-lemma (fin-arr-lemma fin neq) (ground-match-neq gnd')) (ground-match gnd')
    parametricity-onesided-lemma-doublecast-case {τ1 = ·∀ τ1} {τ2 = ·∀ τ2} {τ3 = ⦇-⦈} neq neq' neq'' wt1 (TACast (TACast wt2 x₂ (ConsistForall x₃)) x x₁) eq0 v fin with ground-dec (·∀ τ2)
    ... | Inl gnd = _ , Eq0CastR (Eq0CastR eq0) , MSRefl , fin-gndhole-lemma (fin-forall-lemma fin neq) gnd
    ... | Inr gnd with ground-match-exists gnd x₂ neq''
    ...   | (·∀ τ2') , gnd' = _ , Eq0CastR (Eq0CastR (Eq0CastR eq0)) , MSStep (Step FHOuter (ITGround gnd') FHOuter) MSRefl , fin-gndhole-lemma (fin-forall-lemma (fin-forall-lemma fin neq) (ground-match-neq gnd')) (ground-match gnd')
    parametricity-onesided-lemma-doublecast-case {τ1 = .⦇-⦈} {τ2 = τ1 ==> τ2} {τ3 = τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast wt2 x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FBoxedVal x₅) with ground-dec (τ1 ==> τ2)
    parametricity-onesided-lemma-doublecast-case {d2 = _} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast () x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FBoxedVal (BVVal VConst)) | Inl gnd
    parametricity-onesided-lemma-doublecast-case {d2 = _} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast () x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FBoxedVal (BVVal VLam)) | Inl gnd
    parametricity-onesided-lemma-doublecast-case {d2 = _} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast () x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FBoxedVal (BVVal VTLam)) | Inl gnd
    parametricity-onesided-lemma-doublecast-case {d2 = _} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast wt2 x₂ ConsistHole2) x (ConsistArr x₁ x₄)) (Eq0CastR eq0) v 
      (FBoxedVal (BVHoleCast x₃ x₅)) | _ with parametricity-onesided-lemma-holecast-case wt1 ((TACast wt2 x₂ ConsistHole2)) eq0 v (FBoxedVal x₅)
    ... | d2' , eq0' , steps , fin = _ , Eq0CastR eq0' , evalctx-compose-ms steps (FHCast FHOuter) (FHCast FHOuter) , fin-arr-lemma fin neq'
    parametricity-onesided-lemma-doublecast-case {d2 = _} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast () x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FBoxedVal (BVVal VConst)) | Inr gnd
    parametricity-onesided-lemma-doublecast-case {d2 = _} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast () x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FBoxedVal (BVVal VLam)) | Inr gnd
    parametricity-onesided-lemma-doublecast-case {d2 = _} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast () x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FBoxedVal (BVVal VTLam)) | Inr gnd
    parametricity-onesided-lemma-doublecast-case {τ1 = .(_ ==> _)} {τ3 = τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast wt2 x₂ (ConsistArr x₃ x₆)) x (ConsistArr x₁ x₄)) eq0 v (FBoxedVal x₅) = _ , (Eq0CastR (Eq0CastR eq0)) , MSRefl , FBoxedVal (BVArrCast neq' (BVArrCast neq x₅))
    parametricity-onesided-lemma-doublecast-case {τ1 = .⦇-⦈} {τ2 = τ1 ==> τ2} {τ3 = τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast wt2 x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FIndet x₅) with ground-dec (τ1 ==> τ2)
    parametricity-onesided-lemma-doublecast-case {d2 = _} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast (TAAp wt2 wt3) x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FIndet (IAp x₃ x₅ x₆)) | Inl gnd = _ , (Eq0CastR (Eq0CastR eq0)) , MSRefl , FIndet (ICastArr neq' (ICastHoleGround (λ d' τ' ()) (IAp x₃ x₅ x₆) gnd))
    parametricity-onesided-lemma-doublecast-case {d2 = _} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast (TATAp x₃ wt2 x₆) x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FIndet (ITAp x₅ x₇)) | Inl gnd = _ , (Eq0CastR (Eq0CastR eq0)) , MSRefl , FIndet (ICastArr neq' (ICastHoleGround (λ d' τ' ()) (ITAp x₅ x₇) gnd))
    parametricity-onesided-lemma-doublecast-case {d2 = _} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast TAEHole x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FIndet x₅) | Inl gnd = _ , (Eq0CastR (Eq0CastR eq0)) , MSRefl , FIndet (ICastArr neq' (ICastHoleGround (λ d' τ' ()) x₅ gnd))
    parametricity-onesided-lemma-doublecast-case {d2 = _} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast (TANEHole wt2) x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FIndet x₅) | Inl gnd = _ , (Eq0CastR (Eq0CastR eq0)) , MSRefl , FIndet (ICastArr neq' (ICastHoleGround (λ d' τ' ()) x₅ gnd))
    parametricity-onesided-lemma-doublecast-case {d2 = _} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast wt2₀@(TACast (TACast wt2 x₃ x₆) x₂ ConsistHole2) x (ConsistArr x₁ x₄)) (Eq0CastR eq0) v (FIndet (ICastGroundHole x₅ x₇)) 
      | Inl gnd with parametricity-onesided-lemma-holecast-case wt1 wt2₀ eq0 v (FIndet x₇)
    ... | d2' , eq0' , steps , fin = _ , Eq0CastR eq0' , evalctx-compose-ms steps (FHCast FHOuter) (FHCast FHOuter) , fin-arr-lemma fin neq'
    parametricity-onesided-lemma-doublecast-case {τ1 = .⦇-⦈} {τ2 = τ1 ==> τ2} {τ3 = τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast wt2 x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FIndet x₅)
      | Inr gnd with ground-match-exists gnd x₂ neq''
    parametricity-onesided-lemma-doublecast-case {d2 = .(_ ∘ _)} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast (TAAp wt2 wt3) x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FIndet x₅) | Inr gnd | τg ==> τg₁ , gnd' = _ , Eq0CastR (Eq0CastR (Eq0CastR eq0)) , MSStep (Step (FHCast FHOuter) (ITExpand gnd') (FHCast FHOuter)) MSRefl , FIndet (ICastArr neq' (ICastArr (gnd-ngnd-neq (ground-match gnd') gnd) (ICastHoleGround (λ d' τ' ()) x₅ (ground-match gnd'))))
    parametricity-onesided-lemma-doublecast-case {d2 = .(_ < _ >)} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast (TATAp x₃ wt2 x₆) x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FIndet x₅) | Inr gnd | τg ==> τg₁ , gnd' = _ , Eq0CastR (Eq0CastR (Eq0CastR eq0)) , MSStep (Step (FHCast FHOuter) (ITExpand gnd') (FHCast FHOuter)) MSRefl , FIndet (ICastArr neq' (ICastArr (gnd-ngnd-neq (ground-match gnd') gnd) (ICastHoleGround (λ d' τ' ()) x₅ (ground-match gnd'))))
    parametricity-onesided-lemma-doublecast-case {d2 = .⦇-⦈} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast TAEHole x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FIndet x₅) | Inr gnd | τg ==> τg₁ , gnd' = _ , Eq0CastR (Eq0CastR (Eq0CastR eq0)) , MSStep (Step (FHCast FHOuter) (ITExpand gnd') (FHCast FHOuter)) MSRefl , FIndet (ICastArr neq' (ICastArr (gnd-ngnd-neq (ground-match gnd') gnd) (ICastHoleGround (λ d' τ' ()) x₅ (ground-match gnd'))))
    parametricity-onesided-lemma-doublecast-case {d2 = .(⦇⌜ _ ⌟⦈)} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast (TANEHole wt2) x₂ ConsistHole2) x (ConsistArr x₁ x₄)) eq0 v (FIndet x₅) | Inr gnd | τg ==> τg₁ , gnd' = _ , Eq0CastR (Eq0CastR (Eq0CastR eq0)) , MSStep (Step (FHCast FHOuter) (ITExpand gnd') (FHCast FHOuter)) MSRefl , FIndet (ICastArr neq' (ICastArr (gnd-ngnd-neq (ground-match gnd') gnd) (ICastHoleGround (λ d' τ' ()) x₅ (ground-match gnd'))))
    parametricity-onesided-lemma-doublecast-case {d2 = .(_ ⟨ _ ⇒ ⦇-⦈ ⟩)} {.⦇-⦈} {τ1 ==> τ2} {τ3 ==> τ4} neq neq' neq'' wt1 (TACast wt2₀@(TACast (TACast wt2 x₃ x₆) x₂ ConsistHole2) x (ConsistArr x₁ x₄)) (Eq0CastR eq0) v (FIndet (ICastGroundHole x₅ x₇)) 
      | Inr gnd | τg ==> τg₁ , gnd' with parametricity-onesided-lemma-holecast-case wt1 wt2₀ eq0 v (FIndet x₇)
    ... | d2' , eq0' , steps , fin = _ , Eq0CastR eq0' , evalctx-compose-ms steps (FHCast FHOuter) (FHCast FHOuter) , fin-arr-lemma fin neq'
    parametricity-onesided-lemma-doublecast-case {τ1 = .(_ ==> _)} {τ3 = τ3 ==> τ4} neq neq' neq'' wt1 (TACast (TACast wt2 x₂ (ConsistArr x₃ x₆)) x (ConsistArr x₁ x₄)) eq0 v (FIndet x₅) = _ , (Eq0CastR (Eq0CastR eq0)) , MSRefl , FIndet (ICastArr neq' (ICastArr neq x₅))
    parametricity-onesided-lemma-doublecast-case {τ1 = τ1} {τ3 = ·∀ τ3} neq neq' neq'' wt1 (TACast (TACast wt2 x₂ x₃) x x₁) eq0 v fin = {!   !}

    parametricity-onesided-lemma-holecast-case : ∀{d1 τ d2 τ1 τ3} →
      ∅ ⊢ d1 :: τ →
      ∅ ⊢ (d2 ⟨ τ1 ⇒ ⦇-⦈ ⟩) ⟨ ⦇-⦈ ⇒ τ3 ⟩ :: τ3 →
      d1 =0cr d2 →
      d1 val →
      d2 final →
      Σ[ d2' ∈ ihexp ] (d1 =0cr d2' × ((d2 ⟨ τ1 ⇒ ⦇-⦈ ⟩) ⟨ ⦇-⦈ ⇒ τ3 ⟩)↦* d2' × d2' final)
    parametricity-onesided-lemma-holecast-case wt1 wt2 eq0 v fin = {!   !}
    {- with ground-dec τ1 | ground-dec τ3 | ~dec τ1 τ3
  ...   | Inl g1 | Inl g2 | Inl consis rewrite gnd-gnd-consis-eq g1 g2 consis with parametricity-onesided-lemma-valr wt1 wt2 eq0 v
  ... | d2' , eq0' , steps , fin = _ , eq0' , MSStep (Step FHOuter (ITCastSucceed g2) FHOuter) steps , fin
  parametricity-onesided-lemma-valr wt1 (TACast {τ1 = τ2} {τ2 = τ3} (TACast {τ1 = τ1} wt2 x₂ x₃) x x₁) (Eq0CastR (Eq0CastR eq0)) v | Inr neq | Inr neq' | Inl refl
    | Inl g1 | Inr g2 | Inl consis with ground-match-exists g2 x (flip neq)
  ... | τ3' , g2' rewrite gnd-gnd-consis-eq g1 (ground-match g2') (consist-ground-consist consis g2')
                  with parametricity-onesided-lemma-valr wt1 (TACast wt2 x (~sym (consist-ground-consist ~refl g2'))) (Eq0CastR eq0) v
  ... | d2' , eq0' , steps , fin = _ , eq0' , MSStep (Step FHOuter (ITExpand g2') FHOuter)
                    (MSStep (Step (FHCast FHOuter) (ITCastSucceed (ground-match g2')) (FHCast FHOuter)) steps) , fin
  parametricity-onesided-lemma-valr wt1 (TACast {τ1 = τ2} {τ2 = τ3} (TACast {τ1 = τ1} wt2 x₂ x₃) x x₁) (Eq0CastR (Eq0CastR eq0)) v | Inr neq | Inr neq' | Inl refl
    | Inr g1 | Inl g2 | Inl consis with ground-match-exists g1 (wf-ta CtxWFEmpty wt2) neq'
  ... | τ1' , g1' rewrite ! (gnd-gnd-consis-eq (ground-match g1') g2 (~sym (consist-ground-consist (~sym consis) g1')))
                  with parametricity-onesided-lemma-valr wt1 (TACast wt2 x (consist-ground-consist ~refl g1')) (Eq0CastR eq0) v
  ...   | d2' , eq0' , steps , fin = _ , eq0' , MSStep (Step (FHCast FHOuter) (ITGround g1') (FHCast FHOuter))
                    (MSStep (Step FHOuter (ITCastSucceed (ground-match g1')) FHOuter) steps) , fin
  parametricity-onesided-lemma-valr wt1 (wt2₀@(TACast {τ1 = τ2} {τ2 = τ3} (TACast {τ1 = τ1} wt2 x₂ x₃) x x₁)) (Eq0CastR (Eq0CastR eq0)) v | Inr neq | Inr neq' | Inl refl
    | Inr g1 | Inr g2 | Inl consis with ground-match-exists g1 (wf-ta CtxWFEmpty wt2) neq' | ground-match-exists g2 x (flip neq)
  ... | τ1' , g1' | τ3' , g2' with preservation (preservation (preservation wt2₀ step1) step2) step3 
    where
        eq = (gnd-gnd-consis-eq (ground-match g1') (ground-match g2') (consist-ground-consist (~sym (consist-ground-consist (~sym consis) g1')) g2'))
        ITCastSucceed' : ∀{d τ1 τ2} → τ1 == τ2 → τ1 ground → (d ⟨ τ1 ⇒ ⦇-⦈ ⇒ τ2 ⟩) →> d
        ITCastSucceed' eq gnd rewrite eq = ITCastSucceed gnd 
        step1 = (Step (FHCast FHOuter) (ITGround g1') (FHCast FHOuter))
        step2 = (Step FHOuter (ITExpand g2') FHOuter)
        step3 = (Step (FHCast FHOuter) (ITCastSucceed' eq (ground-match g1')) (FHCast FHOuter))
  ... | TACast (TACast wt2' _ consis1) _ consis2 = _ , {!   !} , MSStep step1 (MSStep step2 (MSStep step3 {!   !})) , {! τ1 τ3  !}
    where
          eq = (gnd-gnd-consis-eq (ground-match g1') (ground-match g2') (consist-ground-consist (~sym (consist-ground-consist (~sym consis) g1')) g2'))
          ITCastSucceed' : ∀{d τ1 τ2} → τ1 == τ2 → τ1 ground → (d ⟨ τ1 ⇒ ⦇-⦈ ⇒ τ2 ⟩) →> d
          ITCastSucceed' eq gnd rewrite eq = ITCastSucceed gnd 
          step1 = (Step (FHCast FHOuter) (ITGround g1') (FHCast FHOuter))
          step2 = (Step FHOuter (ITExpand g2') FHOuter)
          step3 = (Step (FHCast FHOuter) (ITCastSucceed' eq (ground-match g1')) (FHCast FHOuter))
  parametricity-onesided-lemma-valr wt1 (TACast {τ1 = τ2} {τ2 = τ3} (TACast {τ1 = τ1} wt2 x₂ x₃) x x₁) (Eq0CastR (Eq0CastR eq0)) v | Inr neq | Inr neq' | Inl refl
    | Inl g1 | Inl g2 | Inr consis with parametricity-onesided-lemma-valr wt1 wt2 eq0 v
  ... | d2' , eq0' , steps , fin = _ , Eq0FailedCastR eq0' , MSStep (Step FHOuter (ITCastFail g1 g2 consis) FHOuter) (evalctx-compose-ms steps (FHFailedCast FHOuter) (FHFailedCast FHOuter)) , FIndet (IFailedCast fin g1 g2 (~̸-≠ consis))
  parametricity-onesided-lemma-valr wt1 (TACast {τ1 = τ2} {τ2 = τ3} (TACast {τ1 = τ1} wt2 x₂ x₃) x x₁) (Eq0CastR (Eq0CastR eq0)) v | Inr neq | Inr neq' | Inl refl
    | Inl g1 | Inr g2 | Inr consis = _ , {!   !} , {!   !} , {!   !}
  parametricity-onesided-lemma-valr wt1 (TACast {τ1 = τ2} {τ2 = τ3} (TACast {τ1 = τ1} wt2 x₂ x₃) x x₁) (Eq0CastR (Eq0CastR eq0)) v | Inr neq | Inr neq' | Inl refl
    | Inr g1 | Inl g2 | Inr consis = _ , {!   !} , {!   !} , {!   !}
  parametricity-onesided-lemma-valr wt1 (TACast {τ1 = τ2} {τ2 = τ3} (TACast {τ1 = τ1} wt2 x₂ x₃) x x₁) (Eq0CastR (Eq0CastR eq0)) v | Inr neq | Inr neq' | Inl refl
    | Inr g1 | Inr g2 | Inr consis = _ , {!   !} , {!   !} , {!   !}
  -}


  parametricity-onesided-lemma-valr :
    ∀{d1 d2 τ1 τ2} →
    ∅ ⊢ d1 :: τ1 →
    ∅ ⊢ d2 :: τ2 →
    d1 =0cr d2 →
    d1 val →
    Σ[ d2' ∈ ihexp ]( d1 =0cr d2' × d2 ↦* d2' × d2' final)
  parametricity-onesided-lemma-valr wt1 (TACast {τ1 = τ1} {τ2 = τ2} wt2 x x₁) (Eq0CastR eq0) v with htyp-eq-dec τ1 τ2
  ... | Inl refl with parametricity-onesided-lemma-valr wt1 wt2 eq0 v
  ...   | d2' , eq0' , steps , fin = _ , eq0' , MSStep (Step FHOuter ITCastID FHOuter) steps , fin
  parametricity-onesided-lemma-valr wt1 (TACast {τ1 = τ2} {τ2 = τ3} (TACast {τ1 = τ1} wt2 x₂ x₃) x x₁) (Eq0CastR (Eq0CastR eq0)) v | Inr neq with htyp-eq-dec τ1 ⦇-⦈ | htyp-eq-dec τ2 ⦇-⦈
  ... | Inl refl | Inl refl with parametricity-onesided-lemma-valr wt1 (TACast wt2 x x₁) (Eq0CastR eq0) v
  ...   | d2' , eq0' , steps , fin = _ , eq0' , MSStep (Step (FHCast FHOuter) ITCastID (FHCast FHOuter)) steps , fin
  parametricity-onesided-lemma-valr wt1 (TACast {τ1 = τ2} {τ2 = τ3} (TACast {τ1 = τ1} wt2 x₂ x₃) x x₁) (Eq0CastR (Eq0CastR eq0)) v | Inr neq
    | Inr neq' | Inl refl with parametricity-onesided-lemma-valr wt1 wt2 eq0 v
  ... | d2' , eq0' , steps , fin with parametricity-onesided-lemma-holecast-case wt1 (TACast (TACast (preservation-trans wt2 steps) x₂ x₃) x x₁) eq0' v fin
  ... | d2'' , eq0'' , steps' , fin' = _ , eq0'' , mstrans (evalctx-compose-ms steps (FHCast (FHCast FHOuter)) (FHCast (FHCast FHOuter))) steps' , fin'
  parametricity-onesided-lemma-valr wt1 (TACast {τ1 = τ2} {τ2 = τ3} (TACast {τ1 = τ1} wt2 x₂ x₃) x x₁) (Eq0CastR (Eq0CastR eq0)) v | Inr neq
    | _ | Inr neq' with htyp-eq-dec τ1 τ2 
  ... | Inl refl with parametricity-onesided-lemma-valr wt1 (TACast wt2 x x₁) (Eq0CastR eq0) v
  ...   | d2' , eq0' , steps , fin = _ , eq0' , MSStep (Step (FHCast FHOuter) ITCastID (FHCast FHOuter)) steps , fin
  parametricity-onesided-lemma-valr wt1 wt2₀@(TACast {τ1 = τ2} {τ2 = τ3} (TACast {τ1 = τ1} wt2 x₂ x₃) x x₁) (Eq0CastR (Eq0CastR eq0)) v | Inr neq | _ | Inr neq' 
    | Inr neq'' with parametricity-onesided-lemma-valr wt1 wt2 eq0 v
  ... | d2' , eq0' , steps , fin with parametricity-onesided-lemma-doublecast-case neq'' neq neq' wt1 (TACast (TACast (preservation-trans wt2 steps) x₂ x₃) x x₁) eq0' v fin
  ... | d2'' , eq0'' , steps' , fin' = _ , eq0'' , mstrans (evalctx-compose-ms steps (FHCast (FHCast FHOuter)) (FHCast (FHCast FHOuter))) steps' , fin'
  parametricity-onesided-lemma-valr wt1 (TACast (TAFailedCast wt2 x₂ x₃ x₄) x x₁) (Eq0CastR (Eq0FailedCastR eq0)) v | Inr neq with parametricity-onesided-lemma-valr wt1 wt2 eq0 v
  parametricity-onesided-lemma-valr wt1 (TACast (TAFailedCast wt2 x₂ x₃ x₄) x ConsistBase) (Eq0CastR (Eq0FailedCastR eq0)) v | Inr neq 
    | d2' , eq0' , steps , fin = _ , Eq0FailedCastR eq0' , MSStep (Step FHOuter ITCastID FHOuter) (evalctx-compose-ms steps (FHFailedCast FHOuter) (FHFailedCast FHOuter)) , FIndet (IFailedCast fin x₂ x₃ (λ _ → neq refl))
  parametricity-onesided-lemma-valr wt1 (TACast (TAFailedCast wt2 x₂ x₃ x₄) x ConsistHole1) (Eq0CastR (Eq0FailedCastR eq0)) v | Inr neq
    | d2' , eq0' , steps , fin = _ , Eq0CastR (Eq0FailedCastR eq0') , (evalctx-compose-ms steps (FHCast (FHFailedCast FHOuter)) (FHCast (FHFailedCast FHOuter))) , FIndet (ICastGroundHole x₃ (IFailedCast fin x₂ x₃ (~̸-≠ x₄)))
  parametricity-onesided-lemma-valr wt1 (TACast (TAFailedCast wt2 x₂ x₃ x₄) x (ConsistArr x₁ x₅)) (Eq0CastR (Eq0FailedCastR eq0)) v | Inr neq
    | d2' , eq0' , steps , fin = _ , Eq0CastR (Eq0FailedCastR eq0') , (evalctx-compose-ms steps (FHCast (FHFailedCast FHOuter)) (FHCast (FHFailedCast FHOuter))) , FIndet (ICastArr neq (IFailedCast fin x₂ x₃ (~̸-≠ x₄)))
  parametricity-onesided-lemma-valr wt1 (TACast (TAFailedCast wt2 x₂ x₃ x₄) x (ConsistForall x₁)) (Eq0CastR (Eq0FailedCastR eq0)) v | Inr neq
    | d2' , eq0' , steps , fin = _ , Eq0CastR (Eq0FailedCastR eq0') , (evalctx-compose-ms steps (FHCast (FHFailedCast FHOuter)) (FHCast (FHFailedCast FHOuter))) , FIndet (ICastForall neq (IFailedCast fin x₂ x₃ (~̸-≠ x₄)))
  parametricity-onesided-lemma-valr wt1 (TACast wt2 x x₁) (Eq0CastR (Eq0NoCasts eq0)) v | Inr neq with val-cast-final (eq0cn-val-val v eq0) wt2 (wf-ta CtxWFEmpty wt2) x neq x₁
  ... | d2' , Eq0CastL eq0' , steps , fin = d2' , eq0cnr-trans eq0 eq0' , steps , fin
  ... | d2' , Eq0NoLeft x₂ , steps , fin = abort (π1 (eq0ccastr-meaning x₂) refl)
  parametricity-onesided-lemma-valr {d2 = d2 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩} wt1 (TAFailedCast wt2 x x₁ x₂) (Eq0FailedCastR eq0) v with parametricity-onesided-lemma-valr wt1 wt2 eq0 v
  ... | d2' , eq0' , steps , fin = d2' ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ , Eq0FailedCastR eq0' , evalctx-compose-ms steps (FHFailedCast FHOuter) (FHFailedCast FHOuter) , FIndet (IFailedCast fin x x₁ (~̸-≠ x₂))
  parametricity-onesided-lemma-valr _ _ (Eq0NoCasts Eq0Const) VConst = _ , Eq0NoCasts Eq0Const , MSRefl , FBoxedVal (BVVal VConst)
  parametricity-onesided-lemma-valr _ _ (Eq0NoCasts (Eq0Lam eq0')) VLam = _ , Eq0NoCasts (Eq0Lam eq0') , MSRefl , FBoxedVal (BVVal VLam)
  parametricity-onesided-lemma-valr _ _ (Eq0NoCasts (Eq0TLam eq0')) VTLam = _ , Eq0NoCasts (Eq0TLam eq0') , MSRefl , FBoxedVal (BVVal VTLam)

  helper : ∀{d1 d2} →
    Σ[ d2' ∈ ihexp ]( d1 =0cr d2' × d2 ↦* d2' × d2' final) →
    Σ[ d2' ∈ ihexp ]( d1 =0c d2' × d2 ↦* d2' × d2' final)
  helper (x0 , x1 , x2 , x3) = (x0 , Eq0NoLeft x1 , x2 , x3)

  parametricity-onesided-lemma-val :
    ∀{d1 d2} →
    d1 =0c d2 →
    d1 val →
    Σ[ d2' ∈ ihexp ]( d1 =0c d2' × d2 ↦* d2' × d2' final)
  parametricity-onesided-lemma-val (Eq0NoLeft x) VConst = helper (parametricity-onesided-lemma-valr {!   !} {!   !} x VConst)
  parametricity-onesided-lemma-val (Eq0NoLeft x) VLam = helper (parametricity-onesided-lemma-valr {!   !} {!   !} x VLam)
  parametricity-onesided-lemma-val (Eq0NoLeft x) VTLam = helper (parametricity-onesided-lemma-valr {!   !} {!   !} x VTLam)

  parametricity-onesided-lemma :
    ∀{d1 d2} →
    d1 =0c d2 →
    d1 boxedval →
    Σ[ d2' ∈ ihexp ]( d1 =0c d2' × d2 ↦* d2' × d2' final)
  parametricity-onesided-lemma eq0 (BVVal x) = parametricity-onesided-lemma-val eq0 x
  parametricity-onesided-lemma (Eq0CastL eq0) (BVArrCast x bv) with parametricity-onesided-lemma eq0 bv
  ...  | (d2' , eq0' , steps , fin) = d2' , Eq0CastL eq0' , steps , fin
  parametricity-onesided-lemma (Eq0NoLeft x₁) (BVArrCast x bv) = abort (π1 (eq0ccastr-meaning x₁) refl)
  parametricity-onesided-lemma (Eq0CastL eq0) (BVForallCast x bv) with parametricity-onesided-lemma eq0 bv
  ...  | (d2' , eq0' , steps , fin) = d2' , Eq0CastL eq0' , steps , fin
  parametricity-onesided-lemma (Eq0NoLeft x₁) (BVForallCast x bv) = abort (π1 (eq0ccastr-meaning x₁) refl)
  parametricity-onesided-lemma (Eq0CastL eq0) (BVHoleCast x bv) with parametricity-onesided-lemma eq0 bv
  ...  | (d2' , eq0' , steps , fin) = d2' , Eq0CastL eq0' , steps , fin
  parametricity-onesided-lemma (Eq0NoLeft x₁) (BVHoleCast x bv) = abort (π1 (eq0ccastr-meaning x₁) refl)

  {-
    Idea bin -- all cast transitions preserve =0c -- ITApCast ITCastID ITCastSucceed ITApCast ITExpand etc.
    We rule out ITCastFail by assumption (d1 terminates successfully, d2 is allowed to indet.

    Use =0c to constrain forms, and find that ignoring cast forms, d2 can match the rule d1 uses.
    Note: Can't use progress since we need the same part of each form to step.

    I think I can phrase it as
    d1 steps and they're equal or
    they both step and they're equal or
    d2 does a cast step and they're equal, and some ordering on casts decreases

    Basically saying that we cannot pick the third option infinitely.

    I would like to show that third part by saying only the cast steps can preserve =0c. I.e. that ITLam and ITTLam do not.
    However a difficulty here is Omega... if d1 -> d1 through ITLam then clearly =0c is preserved...
    So I guess I'll have to argue its termination via some ordering on terms based on lexicographic cast positioning?
    At its core, I just need to show "eventually we take a step that's not a cast" -- though in the current rules formulation that may not be true,
    since we can do ITExpand infinitely???

    Or perhaps I can say 2nd case is d1 steps and d2 steps multiple times to something equal. That way I can do like
    ITExpand -> ITApCast (Though even then that doesn't change the form and I may have to repeat that. Certainly only a finite number of times though?)
  -}
  -- I think I need to remove the third branch. I think the statement of the conclusion should be
  -- d1' =0c d2 + Σ[ d2' ∈ ihexp ] (d2 ↦* d2' × d1' =0c d2')
  parametricity21-lemma-ctx : ∀{d1 d2 d1' τ1 τ2} →
    ∅ ⊢ d1 :: τ1 →
    ∅ ⊢ d2 :: τ2 →
    d1 =0c d2 →
    d1 ↦ d1' →
    d1' =0c d2 + Σ[ d2' ∈ ihexp ] (d2 ↦* d2' × d1' =0c d2')
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin step ctxout) with eq0-ctxinc eq0 ctxin

  -- See note above -- all of these preserve =0c
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITCastID ctxout) | d2in , ε2 , ctxin' , Eq0CastL eq0in , eq0e = Inl (eq0c-ctx ctxin ctxout ctxin' eq0e (Eq0CastL eq0c-refl) eq0)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin (ITCastSucceed x) ctxout) | d2in , ε2 , ctxin' , Eq0CastL eq0in , eq0e = Inl (eq0c-ctx ctxin ctxout ctxin' eq0e (Eq0CastL (Eq0CastL eq0c-refl)) eq0)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin (ITCastFail x x₁ x₂) ctxout) | d2in , ε2 , ctxin' , Eq0CastL eq0in , eq0e = Inl (eq0c-ctx ctxin ctxout ctxin' eq0e (Eq0CastL (Eq0CastL (eq0cr-lemma' eq0c-refl))) eq0)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin (ITGround x) ctxout) | d2in , ε2 , ctxin' , Eq0CastL eq0in , eq0e = Inl (eq0c-ctx ctxin ctxout ctxin' eq0e (Eq0CastL (eq0cr-lemma (eq0cr-lemma eq0c-refl))) eq0)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin (ITExpand x) ctxout) | d2in , ε2 , ctxin' , Eq0CastL eq0in , eq0e = Inl (eq0c-ctx ctxin ctxout ctxin' eq0e (Eq0CastL (eq0cr-lemma (eq0cr-lemma eq0c-refl))) eq0)

  -- Pick a better context. Add as a conclusion to eq0-ctxinc that the ctx we select absorbs all casts from the term.
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin step ctxout) | .(_ ⟨ _ ⇒ _ ⟩) , ε2 , ctxin' , Eq0NoLeft (Eq0CastR x) , eq0e = {!   !}
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin step ctxout) | .(_ ⟨ _ ⇒⦇-⦈⇏ _ ⟩) , ε2 , ctxin' , Eq0NoLeft (Eq0FailedCastR x) , eq0e = {!   !}

  -- Cases where we have an ITLam but the right side has some casts to the left of the application to deal with (we have to find our way to an ITApCast)
  -- The termination checker isn't happy with my use of induction here, but I know it terminates because every time I call it inductively,
  -- I'm reducing the metric of: let n_k be the number of casts to the left of k apps. Let n = the syntactic size of the term.
  -- Lexicographically order these measures n_infinity > ... > n_2 > n_1 > n_0 > n.
  -- Note that only ITExpand and ITGround increase these measures, with other cast steps decreasing them, but
  -- I always provide following sequences of reductions such that
  -- By the time I use the inductive hypothesis, this measure has decreased.
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout) 
    | (.((_ ⟨ _ ⇒ _ ⟩) ∘ _) , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR x)) x₁)) , eq0e) with wt-filling wt2 ctxin'
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout)
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR (Eq0NoCasts ()))) x₁)) , eq0e | (_ , (TAAp (TACast {d = .⦇-⦈} {τ2 = .(_ ==> _)} TAEHole x₃ ConsistHole2) wt2''))
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout)
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR (Eq0NoCasts ()))) x₁)) , eq0e | _ , TAAp (TACast {d = ⦇⌜ _ ⌟⦈} {τ2 = (_ ==> _)} (TANEHole wt2') x₃ ConsistHole2) wt2''
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout)
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR (Eq0NoCasts ()))) x₁)) , eq0e | _ , TAAp (TACast {d = .(_ ∘ _)} {τ2 = .(_ ==> _)} (TAAp wt2' wt2c) x₃ ConsistHole2) wt2''
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout)
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR (Eq0NoCasts ()))) x₁)) , eq0e | _ , TAAp (TACast {d = .(_ < _ >)} {τ2 = .(_ ==> _)} (TATAp x₄ wt2' x₆) x₃ ConsistHole2) wt2''
  ... | _ , TAAp (TACast {d = .(_ ⟨ _ ⇒⦇-⦈⇏ _ ⟩)} {τ2 = .(_ ==> _)} (TAFailedCast wt2' x₄ x₆ x₇) x₃ ConsistHole2) wt2'' = {!   !} -- lemma for indet
  -- TODO: Panic at the above. It's the case we can't show.
  -- Consider, evaluation of the argument diverges. We can get a terminating execution by substituting it in (which can throw it away). But
  -- By having a failed cast we force evaluation of the argument, which can be non-terminating (think Ω).
  -- This can be fixed with call-by-value semantics.
  -- Supposing d4 is a value, then we know we have to reduce the left hand side of the ap. But since we have =0c, it must be a Lam.
  -- But then, we get that d2 is indet, exactly what we want to show.
  ... | _ , TAAp {d2 = d22} (TACast {d = d21} {τ1 = τ1 ==> τ2} {τ2 = (τ3 ==> τ4)} wt2' x₃ (ConsistArr x₄ x₆)) wt2'' with evalctx-out (((d21 ∘ (d22 ⟨ τ3 ⇒ τ1 ⟩)) ⟨ τ2 ⇒ τ4 ⟩)) ctxin'
  ...   | _ , ctxout' with parametricity21-lemma-ctx wt1 (preservation wt2 (Step ctxin' ITApCast ctxout')) (eq0c-sym (eq0c-ctx ctxin' ctxout' ctxin (eq0ε''-sym eq0e) (Eq0NoLeft (Eq0CastR (Eq0NoCasts (Eq0Ap (Eq0CastL eq0c-refl) (eq0cr-lemma eq0c-refl))))) (eq0c-sym eq0))) ((Step ctxin ITLam ctxout))
  ...     | Inl res = Inr (_ , MSStep (Step ctxin' ITApCast ctxout') MSRefl , res)
  ...     | Inr (d2' , steps' , eq0final) = Inr (d2' , MSStep (Step ctxin' ITApCast ctxout') steps' , eq0final)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout) 
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR x)) x₁)) , eq0e | _ , TAAp {d2 = d4} (TACast {d = (d3 ⟨ τ1 ⇒ ⦇-⦈ ⟩)} {τ2 = (τ2 ==> τ3)} (TACast wt2' x₄ x₆) x₃ ConsistHole2) wt2'' with ground-dec τ1 | ground-dec (τ2 ==> τ3) | ~dec τ1 (τ2 ==> τ3)
  ... | Inl gndl | Inl gndr | Inl consis with evalctx-out (d3 ∘ d4) ctxin'
  ...   | _ , ctxout' rewrite gnd-gnd-consis-eq gndl gndr consis with parametricity21-lemma-ctx wt1 (preservation wt2 (Step (evalctx-compose ctxin' (FHAp1 FHOuter)) (ITCastSucceed gndr) (evalctx-compose ctxout' (FHAp1 FHOuter)))) ((eq0c-sym (eq0c-ctx ctxin' ctxout' ctxin (eq0ε''-sym eq0e) (Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0CastL (Eq0CastL eq0c-refl)) eq0c-refl))) (eq0c-sym eq0)))) (Step ctxin ITLam ctxout)
  ...       | Inl res = Inr (_ , MSStep (Step (evalctx-compose ctxin' (FHAp1 FHOuter)) (ITCastSucceed gndr) (evalctx-compose ctxout' (FHAp1 FHOuter))) MSRefl , res)
  ...       | Inr (d2' , steps' , eq0final) = Inr (d2' , MSStep (Step (evalctx-compose ctxin' (FHAp1 FHOuter)) (ITCastSucceed gndr) (evalctx-compose ctxout' (FHAp1 FHOuter))) steps' , eq0final)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout) 
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR x)) x₁)) , eq0e | _ , TAAp {d2 = d4} (TACast {d = (d3 ⟨ τ1 ⇒ ⦇-⦈ ⟩)} {τ2 = (τ2 ==> τ3)} (TACast wt2' x₄ x₆) x₃ ConsistHole2) wt2''
    | Inl gndl | Inl gndr | Inr consis with evalctx-out ((d3 ⟨ τ1 ⇒⦇-⦈⇏ (τ2 ==> τ3) ⟩) ∘ d4) ctxin'
  ... | _ , ctxout' with parametricity21-lemma-ctx wt1 (preservation wt2 (Step (evalctx-compose ctxin' (FHAp1 FHOuter)) (ITCastFail gndl gndr consis) (evalctx-compose ctxout' (FHAp1 FHOuter)))) ((eq0c-sym (eq0c-ctx ctxin' ctxout' ctxin (eq0ε''-sym eq0e) (Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0CastL (Eq0CastL (eq0cr-lemma' eq0c-refl))) eq0c-refl))) (eq0c-sym eq0)))) (Step ctxin ITLam ctxout)
  ...       | Inl res = Inr (_ , MSStep (Step (evalctx-compose ctxin' (FHAp1 FHOuter)) (ITCastFail gndl gndr consis) (evalctx-compose ctxout' (FHAp1 FHOuter))) MSRefl , res)
  ...       | Inr (d2' , steps' , eq0final) = Inr (d2' , MSStep (Step (evalctx-compose ctxin' (FHAp1 FHOuter)) (ITCastFail gndl gndr consis) (evalctx-compose ctxout' (FHAp1 FHOuter))) steps' , eq0final)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout) 
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR x)) x₁)) , eq0e | _ , TAAp {d2 = d4} (TACast {d = (d3 ⟨ τ1 ⇒ ⦇-⦈ ⟩)} {τ2 = (τ2 ==> τ3)} (TACast wt2' x₄ x₆) x₃ ConsistHole2) wt2''
    | Inl gndl | Inr gndr | _ = {!   !}
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout) 
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR x)) x₁)) , eq0e | _ , TAAp {d2 = d4} (TACast {d = (d3 ⟨ τ1 ⇒ ⦇-⦈ ⟩)} {τ2 = (τ2 ==> τ3)} (TACast wt2' x₄ x₆) x₃ ConsistHole2) wt2''
    | Inr gndl | Inl gndr | _ = {!   !}
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout) 
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR x)) x₁)) , eq0e | _ , TAAp {d2 = d4} (TACast {d = (d3 ⟨ τ1 ⇒ ⦇-⦈ ⟩)} {τ2 = (τ2 ==> τ3)} (TACast wt2' x₄ x₆) x₃ ConsistHole2) wt2''
    | Inr gndl | Inr gndr | _ = {!   !}
{-
  ~dec τ1 (τ2 ==> τ3) 
  ... | Inl consis = {!   !}
  ... | Inr notconsis with evalctx-out ((d3 ⟨ τ1 ⇒ τ2 ==> τ3 ⟩) ∘ d4) ctxin'
  ...   | _ , ctxout' with parametricity21-lemma-ctx wt1 (wt-different-fill ctxin' wt2 {!   !} {!   !} ctxout') (eq0c-sym (eq0c-ctx ctxin' ctxout' ctxin (eq0ε''-sym eq0e) (Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0CastL (Eq0CastL (eq0cr-lemma eq0c-refl))) eq0c-refl))) (eq0c-sym eq0))) (Step ctxin ITLam ctxout)
  ...     | Inl res = {!   !}
  ...     | Inr (d2' , steps' , eq0final) with evalctx-compose ctxin' (FHAp1 FHOuter) | evalctx-compose ctxout' (FHAp1 FHOuter)
  ...       | (_ , ctxin'') | (_ , ctxout'') = Inr (d2' , MSStep (Step ctxin'' (ITCastSucceed {!   !} {!   !} {!   !}) {!   !}) steps' , eq0final) 
-}
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout) 
    | .((_ ⟨ _ ⇒⦇-⦈⇏ _ ⟩) ∘ _) , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0FailedCastR x)) x₁)) , eq0e = 
      {!   !} -- d2 contains a failed cast so it will be indet (must show it doesn't diverge?)
      -- Need lemma: d2 has a failed cast and eq0 d1, d2 will eval to indet
      -- lemma -- if d1 o d2 -> final then d2 -> final, then use the fact that d2 =0c d4
      -- and parametricity to show d4 -> final, but d4 has failed cast that never goes away so it's indet
      -- Alternatively, if just showing parametricity22, we have d4 -> final and d4 has a failedcast
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITApCast ctxout) 
    | .(_ ∘ _) , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap x x₁)) , eq0e = 
      Inl (eq0c-ctx ctxin ctxout ctxin' eq0e (Eq0NoLeft (Eq0CastR (Eq0NoCasts (Eq0Ap (Eq0CastL eq0c-refl) (eq0cr-lemma eq0c-refl))))) eq0) -- Using ITApCast doesn't change =0 status

-- These are the actual interesting cases.
  parametricity21-lemma-ctx {d1 = d1} {d2 = d2} wt1 wt2 eq0 (Step ctxin (ITLam {d1 = d3} {d2 = d4}) ctxout) 
    | ((·λ[ _ ] _) ∘ _) , ε2 , ctxin' , 
    Eq0NoLeft (Eq0NoCasts (Eq0Ap {d4 = d6} (Eq0NoLeft (Eq0NoCasts (Eq0Lam {d2 = d5} x))) x₁)) , eq0e with eq0c-ctxout (eq0-substc d3 d5 x₁ x) eq0e ctxout
  ... | (d2out , eqeout , eq0out) = Inr (_ , MSStep (Step ctxin' ITLam eqeout) MSRefl , eq0out)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin step ctxout) | .(_ < _ >) , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0TAp x)) , eq0e = {!   !}
 
  parametricity21 :
    ∀{d1 d2 v1} →
    d1 =0c d2 →
    d1 ↦* v1 →
    v1 boxedval →
    Σ[ v2 ∈ ihexp ]( d2 ↦* v2 × ((v2 boxedval × v1 =0c v2) + v2 indet ))
  parametricity21 eq0 step bv = {!   !}
          