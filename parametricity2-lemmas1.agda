{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import core
open import core-type
open import core-exp
open import core-subst

open import parametricity2-defs

open import preservation
open import ground-dec
open import lemmas-consistency
open import lemmas-wf
open import eq-dec
open import lemmas-ground

module parametricity2-lemmas1 where

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
