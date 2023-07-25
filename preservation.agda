open import Nat
open import Prelude
open import core
open import contexts

open import lemmas-consistency
open import type-assignment-unicity
open import binders-disjoint-checks

open import lemmas-subst-ta

open import lemmas-free-tvars
open import lemmas-well-formed

module preservation where
  open typctx

  -- if d and d' both result from filling the hole in ε with terms of the
  -- same type, they too have the same type.
  wt-different-fill : ∀{ Δ Γ Θ d ε d1 d2 d' τ τ1 } →
            d == ε ⟦ d1 ⟧ →
            Δ , Γ , Θ ⊢ d :: τ →
            Δ , Γ , Θ ⊢ d1 :: τ1 →
            Δ , Γ , Θ ⊢ d2 :: τ1 →
            d' == ε ⟦ d2 ⟧ →
            Δ , Γ , Θ ⊢ d' :: τ
  wt-different-fill FHOuter D1 D2 D3 FHOuter
    with type-assignment-unicity D1 D2
  ... | refl = D3
  wt-different-fill (FHAp1 eps) (TAAp D1 D2) D3 D4 (FHAp1 D5) = TAAp (wt-different-fill eps D1 D3 D4 D5) D2
  wt-different-fill (FHAp2 eps) (TAAp D1 D2) D3 D4 (FHAp2 D5) = TAAp D1 (wt-different-fill eps D2 D3 D4 D5)
  wt-different-fill (FHTAp eps) (TATAp wf D1 eq) D2 D3 (FHTAp D4) = TATAp wf (wt-different-fill eps D1 D2 D3 D4) eq
  wt-different-fill (FHNEHole eps) (TANEHole x D1 x₁) D2 D3 (FHNEHole D4) = TANEHole x (wt-different-fill eps D1 D2 D3 D4) x₁
  wt-different-fill (FHCast eps) (TACast D1 wf x) D2 D3 (FHCast D4) = TACast (wt-different-fill eps D1 D2 D3 D4) wf x
  wt-different-fill (FHFailedCast x) (TAFailedCast y x₁ x₂ x₃) D3 D4 (FHFailedCast eps) = TAFailedCast (wt-different-fill x y D3 D4 eps) x₁ x₂ x₃

  -- if a well typed term results from filling the hole in ε, then the term
  -- that filled the hole is also well typed
  wt-filling : ∀{ ε Δ Γ Θ d τ d' } →
             Δ , Γ , Θ ⊢ d :: τ →
             d == ε ⟦ d' ⟧ →
             Σ[ τ' ∈ htyp ] (Δ , Γ , Θ ⊢ d' :: τ')
  wt-filling TAConst FHOuter = _ , TAConst
  wt-filling (TAVar x₁) FHOuter = _ , TAVar x₁
  wt-filling (TALam f wf ta) FHOuter = _ , TALam f wf ta
  wt-filling (TATLam ta) FHOuter = _ , TATLam ta

  wt-filling (TAAp ta ta₁) FHOuter = _ , TAAp ta ta₁
  wt-filling (TAAp ta ta₁) (FHAp1 eps) = wt-filling ta eps
  wt-filling (TAAp ta ta₁) (FHAp2 eps) = wt-filling ta₁ eps

  wt-filling (TATAp wf ta eq) FHOuter = _ , TATAp wf ta eq
  wt-filling (TATAp wf ta eq) (FHTAp eps) = wt-filling ta eps

  wt-filling (TAEHole x x₁) FHOuter = _ , TAEHole x x₁
  wt-filling (TANEHole x ta x₁) FHOuter = _ , TANEHole x ta x₁
  wt-filling (TANEHole x ta x₁) (FHNEHole eps) = wt-filling ta eps
  wt-filling (TACast ta wf x) FHOuter = _ , TACast ta wf x
  wt-filling (TACast ta wf x) (FHCast eps) = wt-filling ta eps
  wt-filling (TAFailedCast x y z w) FHOuter = _ , TAFailedCast x y z w
  wt-filling (TAFailedCast x x₁ x₂ x₃) (FHFailedCast y) = wt-filling x y

  lemma-tysubst : ∀{ Δ Γ Θ d τ t n } -> (n == typctx.n Θ) -> Θ ⊢ t wf -> [ Θ newtyp] ⊢ Γ tctxwf -> Δ , [ Θ newtyp] , Γ ⊢ d :: τ -> Δ , Θ , Tctx[ t / n ] Γ ⊢ (TTyp[ t / n ] d) :: Typ[ t / n ] τ
  lemma-tysubst _ _ _ TAConst = TAConst
  lemma-tysubst {Γ = Γ} {d = X var} {t = t} {n = n} nbound twf tcwf (TAVar x) = TAVar (lemma-subst-elem {Γ} {var} x)
{-  ...  | None rewrite x = {!!}
  ...  | Some a = {!!} -}
  
  -- let x' = foo {var} {Γ} (wf-no-subst (cwf x) nbound) x {- (wf-no-subst {! (cwf x) !}) x -} in TAVar {!x'!} -- TAVar ((foo {!x!} {!(wf-no-subst (nfv x))!}))
    where
      foo : ∀{x Γ} {t1 t2 : htyp} -> t1 == t2 -> (x , t1) ∈ Γ -> (x , t2) ∈ Γ
      foo eq p rewrite eq = p
  lemma-tysubst {Δ} {Γ} {Θ} {d = ·λ _ [ _ ] d} {t = t} {n = n} nbound twf tcwf (TALam {x = x} {τ1 = τ1} {τ2 = τ2} ap wf y) rewrite nbound -- (lemma-extend-subst-comm {Γ} {x} {τ1} {t} {Z})
    = TALam (lemma-subst-apart {Γ} ap) (wf-sub twf wf lt-1+) (foo (lemma-tysubst refl twf (merge-tctx-wf tcwf wf ap) y))
    where
      foo : ∀{t n} -> Δ , Θ , Tctx[ t / n ] (Γ ,, (x , τ1)) ⊢ TTyp[ t / n ] d :: (Typ[ t / n ] τ2) -> 
        Δ , Θ , (Tctx[ t / n ] Γ) ,, (x , Typ[ t / n ] τ1) ⊢ TTyp[ t / n ] d :: (Typ[ t / n ] τ2)
      foo {t} {n} p rewrite lemma-extend-subst-comm {Γ} {x} {τ1} {t} {n} = p
  -- TALam x (wf-sub twf wf LTZ) (lemma-tysubst {τ = Typ[ t / Z ] τ2} (merge-tctx-wf tcwf (wf-sub twf wf LTZ) x) {!  !}) -- TALam (lemma-tysubst x) (lemma-tysubst y) 
  -- TALam x (wf-sub twf wf LTZ) {!   !}
  lemma-tysubst {d = d} _ twf tcwf (TATLam x) = TATLam {! lemma-tysubst  !}
  lemma-tysubst _ _ _ _ = {!!}
{-
  lemma-tysubst (TAAp x cong) = {!!}
  lemma-tysubst (TATAp wf x eq) = {!!}
  lemma-tysubst (TAEHole x x₁) = {!!}
  lemma-tysubst (TANEHole x x₁ x₂) = {!!}
  lemma-tysubst (TACast x wf x₁) = {!!}
  lemma-tysubst (TAFailedCast x x₁ x₂ x₃) = {!!}
-}

  -- instruction transitions preserve type
  preserve-trans : ∀{ Δ Γ d τ d' } →
            binders-unique d →
            ~∅ ⊢ Γ tctxwf →
            ~∅ ⊢ Δ hctxwf →
            Δ , ~∅ , Γ ⊢ d :: τ →
            d →> d' →
            Δ , ~∅ , Γ ⊢ d' :: τ
  preserve-trans _ _ _ TAConst ()
  preserve-trans _ _ _ (TAVar x₁) ()
  preserve-trans _ _ _ (TALam _ _ ta) ()
  preserve-trans (BUAp (BULam bd x₁) bd₁ (BDLam x₂ x₃)) _ _ (TAAp (TALam apt wf ta) ta₁) ITLam = lem-subst apt x₂ bd₁ ta ta₁
  preserve-trans _ _ _ (TATLam ta) ()
  preserve-trans _ tcwf hcwf(TAAp (TACast ta (WFArr wf1 wf2) (TCArr x x₁)) ta₁) ITApCast = TACast (TAAp ta (TACast ta₁ {! hctxwf  !} (~sym x))) wf2 x₁ {- with wf-ta tcwf hcwf ta
  ... | WFArr wf1' _ = TACast (TAAp ta (TACast ta₁ wf1' (~sym x))) wf2 x₁ -}
  preserve-trans {d = ·Λ d < τ >} _ tcwf hcwf (TATAp wf (TATLam x) eq) ITTLam with eq 
  ... | refl rewrite (wf-tctx-no-subst tcwf λ ()) = lemma-tysubst refl wf {!tcwf!} x -- lemma-tysubst {!!} {!!} x
  preserve-trans _ _ _ (TATAp wf (TACast ta (WFForall wf2) (TCForall x)) eq) ITTApCast with eq
  ... | refl = TACast (TATAp wf ta refl) (wf-sub wf wf2 LTZ) (~Typ[] x)
  preserve-trans _ _ _ (TACast ta wf x) (ITCastID) = ta
  preserve-trans _ _ _ (TACast (TACast ta _ x) _ x₁) (ITCastSucceed x₂) = ta
  preserve-trans _ _ _ (TACast ta wf x) (ITGround (MGArr x₁)) = TACast (TACast ta (WFArr wf wf) (TCArr TCHole1 TCHole1)) wf TCHole1
  preserve-trans _ _ _ (TACast ta wf x) (ITGround (MGForall x₁)) = TACast (TACast ta (WFForall WFHole) (TCForall TCHole1)) wf TCHole1
  preserve-trans _ _ _ (TACast ta wf TCHole2) (ITExpand (MGArr x₁)) = TACast (TACast ta (WFArr WFHole WFHole) TCHole2) wf (TCArr TCHole2 TCHole2)
  preserve-trans _ _ _ (TACast ta wf TCHole2) (ITExpand (MGForall x₁)) = TACast (TACast ta (WFForall WFHole) TCHole2) wf (TCForall TCHole2)
  preserve-trans _ _ _ (TACast (TACast ta _ x) _ x₁) (ITCastFail w y z) = TAFailedCast ta w y z
  preserve-trans _ _ _ (TAFailedCast x y z q) ()

  lem-bd-ε1 : ∀{ d ε d0} → d == ε ⟦ d0 ⟧ → binders-unique d → binders-unique d0
  lem-bd-ε1 FHOuter bd = bd
  lem-bd-ε1 (FHAp1 eps) (BUAp bd bd₁ x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHAp2 eps) (BUAp bd bd₁ x) = lem-bd-ε1 eps bd₁
  lem-bd-ε1 (FHTAp eps) (BUTAp bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHNEHole eps) (BUNEHole bd x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHCast eps) (BUCast bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHFailedCast eps) (BUFailedCast bd) = lem-bd-ε1 eps bd

  -- this is the main preservation theorem, gluing together the above
  preservation : {Δ : hctx} {d d' : ihexp} {τ : htyp} {Γ : tctx} →
             binders-unique d →
             ~∅ ⊢ Γ tctxwf →
             ~∅ ⊢ Δ hctxwf →
             Δ , ~∅ , Γ ⊢ d :: τ →
             d ↦ d' →
             Δ , ~∅ , Γ ⊢ d' :: τ
  preservation bd tcwf hcwf D (Step x x₁ x₂)
    with wt-filling D x
  ... | (_ , wt) = wt-different-fill x D wt (preserve-trans (lem-bd-ε1 x bd) tcwf hcwf wt x₁) x₂

  -- note that the exact statement of preservation in the paper, where Γ is
  -- empty indicating that the terms are closed, is an immediate corrolary
  -- of the slightly more general statement above.
  preservation' : {Δ : hctx} {d d' : ihexp} {τ : htyp} →
             binders-unique d →
             ~∅ ⊢ Δ hctxwf →
             Δ , ~∅ , ∅ ⊢ d :: τ →
             d ↦ d' →
             Δ , ~∅ , ∅ ⊢ d' :: τ
  preservation' bu hcwf = preservation bu wf-empty-tctx hcwf
    