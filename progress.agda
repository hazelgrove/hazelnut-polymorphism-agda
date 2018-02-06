open import Nat
open import Prelude
open import List
open import core
open import contexts
open import lemmas-consistency

open import canonical-boxed-forms
open import canonical-indeterminate-forms

module progress where
  -- this is a little bit of syntactic sugar to avoid many layer nested Inl
  -- and Inrs that you would get from the more literal transcription of the
  -- consequent of progress as:
  --
  -- d boxedval + d indet + d casterr[ Δ ] + Σ[ d' ∈ dhexp ] (d ↦ d')
  data ok : (d : dhexp) (Δ : hctx) → Set where
    S : ∀{d Δ} → Σ[ d' ∈ dhexp ] (d ↦ d') → ok d Δ
    E : ∀{d Δ} → d casterr → ok d Δ
    I : ∀{d Δ} → d indet → ok d Δ
    V : ∀{d Δ} → d boxedval → ok d Δ

  progress : {Δ : hctx} {d : dhexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ →
             ok d Δ
    -- constants
  progress TAConst = V (BVVal VConst)

    -- variables
  progress (TAVar x₁) = abort (somenotnone (! x₁))

    -- lambdas
  progress (TALam wt) = V (BVVal VLam)

    -- applications
  progress (TAAp wt1 wt2)
    with progress wt1 | progress wt2
    -- if the left steps, the whole thing steps
  progress (TAAp wt1 wt2) | S (_ , Step x y z) | _ = S (_ , Step (FHAp1 x) y (FHAp1 z))
    -- if the left is an error, the whole thing is an error
  progress (TAAp wt1 wt2) | E x | _ = E (CECong (FHAp1 FHOuter) x)
    -- if the left is indeterminate, inspect the right
  progress (TAAp wt1 wt2) | I i | S (_ , Step x y z) = S (_ , Step (FHAp2 x) y (FHAp2  z))
  progress (TAAp wt1 wt2) | I x | E x₁ = E (CECong (FHAp2 FHOuter) x₁)
  progress (TAAp wt1 wt2) | I x | I x₁ = I (IAp {!!} x (FIndet x₁)) -- todo: check that it's not that form, otherwise the cast can progress maybe
  progress (TAAp wt1 wt2) | I x | V x₁ = I (IAp {!!} x (FBoxed x₁)) --
    -- if the left is a boxed value, inspect the right
  progress (TAAp wt1 wt2) | V v | S (_ , Step x y z) = S (_ , Step (FHAp2  x) y (FHAp2  z))
  progress (TAAp wt1 wt2) | V v | E e = E (CECong (FHAp2 FHOuter) e)
  progress (TAAp wt1 wt2) | V v | I i
    with canonical-boxed-forms-arr wt1 v
  ... | Inl (x , d' , refl , qq) = S (_ , Step FHOuter ITLam FHOuter)
  ... | Inr (d' , τ1' , τ2' , refl , neq , qq) = I (IAp {!!} (ICastArr neq {!!}) (FIndet i)) --cyrus, as below
  progress (TAAp wt1 wt2) | V v | V v₂
    with canonical-boxed-forms-arr wt1 v
  ... | Inl (x , d' , refl , qq) = S (_ , Step FHOuter ITLam FHOuter)
  ... | Inr (d' , τ1' , τ2' , refl , neq , qq) = I (IAp {!!} (ICastArr neq {!!}) (FBoxed v₂)) --cyrus

    -- empty holes
  progress (TAEHole x x₁) = I IEHole

    -- nonempty holes
  progress (TANEHole xin wt x₁)
    with progress wt
  ... | S (_ , Step x y z) = S (_ , Step (FHNEHole x) y (FHNEHole z))
  ... | E x = E (CECong (FHNEHole FHOuter) x)
  ... | I x = I (INEHole (FIndet x))
  ... | V x = I (INEHole (FBoxed x))

    -- casts
  progress (TACast wt con)
    with progress wt
  ... | S (_ , Step x y z) = S (_ , Step (FHCast x) y (FHCast z))
  ... | E x = E (CECong (FHCast FHOuter) x)
  -- indet cases, inspect how the casts are realted by consistency
  progress (TACast wt TCRefl)  | I x = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt TCHole1) | I x = I (ICastGroundHole {!!} x) -- cyrus
  progress (TACast wt TCHole2) | I x = I (ICastHoleGround {!!} x {!!}) -- cyrus
  progress (TACast wt (TCArr c1 c2)) | I x = I (ICastArr {!!} x) -- cyrus
  -- boxed value cases, inspect how the casts are realted by consistency
  progress (TACast wt TCRefl)  | V x = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt TCHole1) | V x = V (BVHoleCast {!!} x) -- cyrus
  progress (TACast wt TCHole2) | V x = V {!!} -- cyrus: missing rule for boxed values?
  progress (TACast wt (TCArr c1 c2)) | V x = V (BVArrCast {!!} x) -- cyrus
