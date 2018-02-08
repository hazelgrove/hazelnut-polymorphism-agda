open import Nat
open import Prelude
open import List
open import core

module lemmas-progress-checks where
  boxedval-not-trans : ∀{d d'} → d boxedval → d →> d' → ⊥
  boxedval-not-trans (BVVal VConst) ()
  boxedval-not-trans (BVVal VLam) ()
  boxedval-not-trans (BVArrCast x bv) (ITCastID) = x refl
  boxedval-not-trans (BVHoleCast () bv) (ITCastID)
  boxedval-not-trans (BVHoleCast () bv) (ITCastSucceed x₁)
  boxedval-not-trans (BVHoleCast GHole bv) (ITGround (MGArr x)) = x refl
  boxedval-not-trans (BVHoleCast x a) (ITExpand ())
  boxedval-not-trans (BVHoleCast x x₁) (ITCastFail x₂ () x₄)

  indet-not-trans : ∀{d d'} → d indet → d →> d' → ⊥
  indet-not-trans IEHole ()
  indet-not-trans (INEHole x) ()
  indet-not-trans (IAp x₁ () x₂) (ITLam)
  indet-not-trans (IAp x (ICastArr x₁ ind) x₂) (ITApCast ) = x _ _ _ _ _ refl
  indet-not-trans (ICastArr x ind) (ITCastID) = x refl
  indet-not-trans (ICastGroundHole () ind) (ITCastID)
  indet-not-trans (ICastGroundHole x ind) (ITCastSucceed ())
  indet-not-trans (ICastGroundHole GHole ind) (ITGround (MGArr x)) = x refl
  indet-not-trans (ICastHoleGround x ind ()) (ITCastID)
  indet-not-trans (ICastHoleGround x ind x₁) (ITCastSucceed x₂) = x _ _ refl
  indet-not-trans (ICastHoleGround x ind GHole) (ITExpand (MGArr x₂)) = x₂ refl
  indet-not-trans (ICastGroundHole x a) (ITExpand ())
  indet-not-trans (ICastHoleGround x a x₁) (ITGround ())
  indet-not-trans (ICastGroundHole x x₁) (ITCastFail x₂ () x₄)
  indet-not-trans (ICastHoleGround x x₁ x₂) (ITCastFail x₃ x₄ x₅) = x _ _ refl
  indet-not-trans (IFailedCast x x₁ x₂ x₃) ()

  final-not-trans : ∀{d d'} → d final → d →> d' → ⊥
  final-not-trans (FBoxed x) = boxedval-not-trans x
  final-not-trans (FIndet x) = indet-not-trans x

  final-gnd-cast : ∀{ d τ } → d final → τ ground → (d ⟨ τ ⇒ ⦇⦈ ⟩) final
  final-gnd-cast (FBoxed x) gnd = FBoxed (BVHoleCast gnd x)
  final-gnd-cast (FIndet x) gnd = FIndet (ICastGroundHole gnd x)

  final-sub-final : ∀{d ε x} → d final → d == ε ⟦ x ⟧ → x final
  final-sub-final x FHOuter = x
  final-sub-final (FBoxed (BVVal ())) (FHAp1 eps)
  final-sub-final (FBoxed (BVVal ())) (FHAp2 eps)
  final-sub-final (FBoxed (BVVal ())) (FHNEHole eps)
  final-sub-final (FBoxed (BVVal ())) (FHCast eps)
  final-sub-final (FBoxed (BVVal ())) (FHFailedCast y)
  final-sub-final (FBoxed (BVArrCast x₁ x₂)) (FHCast eps) = final-sub-final (FBoxed x₂) eps
  final-sub-final (FBoxed (BVHoleCast x₁ x₂)) (FHCast eps) = final-sub-final (FBoxed x₂) eps
  final-sub-final (FIndet (IAp x₁ x₂ x₃)) (FHAp1 eps) = final-sub-final (FIndet x₂) eps
  final-sub-final (FIndet (IAp x₁ x₂ x₃)) (FHAp2 eps) = final-sub-final x₃ eps
  final-sub-final (FIndet (INEHole x₁)) (FHNEHole eps) = final-sub-final x₁ eps
  final-sub-final (FIndet (ICastArr x₁ x₂)) (FHCast eps) = final-sub-final (FIndet x₂) eps
  final-sub-final (FIndet (ICastGroundHole x₁ x₂)) (FHCast eps) = final-sub-final (FIndet x₂) eps
  final-sub-final (FIndet (ICastHoleGround x₁ x₂ x₃)) (FHCast eps) = final-sub-final (FIndet x₂) eps
  final-sub-final (FIndet (IFailedCast x₁ x₂ x₃ x₄)) (FHFailedCast FHOuter) = final-gnd-cast x₁ x₂
  final-sub-final (FIndet (IFailedCast x₁ x₂ x₃ x₄)) (FHFailedCast (FHCast y)) = final-sub-final x₁ y

  final-sub-not-trans : ∀{d d' d'' ε} →  d final → d == ε ⟦ d' ⟧ → d' →> d'' → ⊥
  final-sub-not-trans f sub step = final-not-trans (final-sub-final f sub) step
