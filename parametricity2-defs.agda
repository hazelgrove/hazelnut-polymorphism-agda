{-# OPTIONS --allow-unsolved-metas #-}

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

module parametricity2-defs where
    
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
  mstrans MSRefl ms2 = ms2
  mstrans (MSStep x ms1) ms2 = MSStep x (mstrans ms1 ms2)

  preservation-trans : ∀ { d d' τ } →
    ∅ ⊢ d :: τ →
    d ↦* d' →
    ∅ ⊢ d' :: τ
  preservation-trans wt MSRefl = wt
  preservation-trans wt (MSStep x ms) = preservation-trans (preservation wt x) ms

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
