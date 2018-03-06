open import Nat
open import Prelude
open import List
open import core
open import contexts

open import lemmas-consistency
open import type-assignment-unicity

module preservation where
  -- if d and d' both result from filling the hole in ε with terms of the
  -- same type, they too have the same type.
  wt-different-fill : ∀{ Δ Γ d ε d1 d2 d' τ τ1 } →
            d == ε ⟦ d1 ⟧ →
            Δ , Γ ⊢ d :: τ →
            Δ , Γ ⊢ d1 :: τ1 →
            Δ , Γ ⊢ d2 :: τ1 →
            d' == ε ⟦ d2 ⟧ →
            Δ , Γ ⊢ d' :: τ
  wt-different-fill FHOuter D1 D2 D3 FHOuter
    with type-assignment-unicity D1 D2
  ... | refl = D3
  wt-different-fill (FHAp1 eps) (TAAp D1 D2) D3 D4 (FHAp1 D5) = TAAp (wt-different-fill eps D1 D3 D4 D5) D2
  wt-different-fill (FHAp2 eps) (TAAp D1 D2) D3 D4 (FHAp2 D5) = TAAp D1 (wt-different-fill eps D2 D3 D4 D5)
  wt-different-fill (FHNEHole eps) (TANEHole x D1 x₁) D2 D3 (FHNEHole D4) = TANEHole x (wt-different-fill eps D1 D2 D3 D4) x₁
  wt-different-fill (FHCast eps) (TACast D1 x) D2 D3 (FHCast D4) = TACast (wt-different-fill eps D1 D2 D3 D4) x
  wt-different-fill (FHFailedCast x) (TAFailedCast y x₁ x₂ x₃) D3 D4 (FHFailedCast eps) = TAFailedCast (wt-different-fill x y D3 D4 eps) x₁ x₂ x₃

  -- if a well typed term results from filling the hole in ε, then the term
  -- that filled the hole is also well typed
  wt-filling : ∀{ ε Δ Γ d τ d' } →
             Δ , Γ ⊢ d :: τ →
             d == ε ⟦ d' ⟧ →
             Σ[ τ' ∈ htyp ] (Δ , Γ ⊢ d' :: τ')
  wt-filling TAConst FHOuter = _ , TAConst
  wt-filling (TAVar x₁) FHOuter = _ , TAVar x₁
  wt-filling (TALam ta) FHOuter = _ , TALam ta

  wt-filling (TAAp ta ta₁) FHOuter = _ , TAAp ta ta₁
  wt-filling (TAAp ta ta₁) (FHAp1 eps) = wt-filling ta eps
  wt-filling (TAAp ta ta₁) (FHAp2 eps) = wt-filling ta₁ eps

  wt-filling (TAEHole x x₁) FHOuter = _ , TAEHole x x₁
  wt-filling (TANEHole x ta x₁) FHOuter = _ , TANEHole x ta x₁
  wt-filling (TANEHole x ta x₁) (FHNEHole eps) = wt-filling ta eps
  wt-filling (TACast ta x) FHOuter = _ , TACast ta x
  wt-filling (TACast ta x) (FHCast eps) = wt-filling ta eps
  wt-filling (TAFailedCast x y z w) FHOuter = _ , TAFailedCast x y z w
  wt-filling (TAFailedCast x x₁ x₂ x₃) (FHFailedCast y) = wt-filling x y

  -- replacing a variable in a term with contents of the appropriate type
  -- preserves type and contracts the context
  lem-subst : ∀{Δ Γ x τ1 d1 τ d2 } →
              Δ , Γ ,, (x , τ1) ⊢ d1 :: τ →
              Δ , Γ ⊢ d2 :: τ1 →
              Δ , Γ ⊢ [ d2 / x ] d1 :: τ
  lem-subst TAConst D2 = TAConst
  lem-subst {Γ = Γ} {x = x'} (TAVar {x = x} x₂) D2 with natEQ x x'
  lem-subst {Γ = Γ} {x = x} {τ1 = τ1} (TAVar x₃) D2 | Inl refl = {!!}
  lem-subst {Γ = Γ} {x = x} {τ1 = τ1} (TAVar {x = x'} x₃) D2 | Inr x₂ = {!x∈sing!}
  -- ... | qq = TAVar {!!}
  --   with Γ x
  -- lem-subst {x = x} (TAVar {x = x'} x₃) D2 | Some x₁ = {!!}
  --   with natEQ x' x
  -- lem-subst (TAVar xin) D2 | Some x₃ | Inl refl = {!!}
  -- lem-subst (TAVar refl) D2 | Some x₃ | Inr x₂ = {!!}
  -- lem-subst {x = x} (TAVar {x = x'} x₂) D2 | None with natEQ x' x
  --lem-subst {x = x} (TAVar x₃) D2 | None | Inl refl with natEQ x x
  -- lem-subst (TAVar refl) D2 | None | Inl refl | Inl refl = D2
  -- lem-subst (TAVar x₃) D2 | None | Inl refl | Inr x₁ = abort (somenotnone (! x₃))
  --lem-subst {x = x} (TAVar {x = x'} x₃) D2 | None | Inr x₂ with natEQ x x'
  -- lem-subst (TAVar x₄) D2 | None | Inr x₃ | Inl x₂ = abort ((flip x₃) x₂)
  -- lem-subst (TAVar x₄) D2 | None | Inr x₃ | Inr x₂ = abort (somenotnone (! x₄))
  lem-subst {Γ = Γ} {x = x} (TALam {x = x'} D1) D2 = {!!}
  lem-subst (TAAp D1 D2) D3 = TAAp (lem-subst D1 D3) (lem-subst D2 D3)
  lem-subst (TAEHole x₁ x₂) D2 = TAEHole x₁ {!!}
  lem-subst (TANEHole x₁ D1 x₂) D2 = TANEHole x₁ (lem-subst D1 D2) {!!}
  lem-subst (TACast D1 x₁) D2 = TACast (lem-subst D1 D2) x₁
  lem-subst (TAFailedCast D1 x₁ x₂ x₃) D2 = TAFailedCast (lem-subst D1 D2) x₁ x₂ x₃

  -- instruction transitions preserve type
  preserve-trans : ∀{ Δ Γ d τ d' } →
            Δ , Γ ⊢ d :: τ →
            d →> d' →
            Δ , Γ ⊢ d' :: τ
  preserve-trans TAConst ()
  preserve-trans (TAVar x₁) ()
  preserve-trans (TALam ta) ()
  preserve-trans (TAAp (TALam ta) ta₁) ITLam = lem-subst ta ta₁
  preserve-trans (TAAp (TACast ta TCRefl) ta₁) ITApCast = TACast (TAAp ta (TACast ta₁ TCRefl)) TCRefl
  preserve-trans (TAAp (TACast ta (TCArr x x₁)) ta₁) ITApCast = TACast (TAAp ta (TACast ta₁ (~sym x))) x₁
  preserve-trans (TAEHole x x₁) ()
  preserve-trans (TANEHole x ta x₁) ()
  preserve-trans (TACast ta x) (ITCastID) = ta
  preserve-trans (TACast (TACast ta x) x₁) (ITCastSucceed x₂) = ta
  preserve-trans (TACast ta x) (ITGround (MGArr x₁)) = TACast (TACast ta (TCArr TCHole1 TCHole1)) TCHole1
  preserve-trans (TACast ta TCHole2) (ITExpand (MGArr x₁)) = TACast (TACast ta TCHole2) (TCArr TCHole2 TCHole2)
  preserve-trans (TACast (TACast ta x) x₁) (ITCastFail w y z) = TAFailedCast ta w y z
  preserve-trans (TAFailedCast x y z q) ()

  -- this is the main preservation theorem, gluing together the above
  preservation : {Δ : hctx} {d d' : dhexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ →
             d ↦ d' →
             Δ , ∅ ⊢ d' :: τ
  preservation D (Step x x₁ x₂)
    with wt-filling D x
  ... | (_ , wt) = wt-different-fill x D wt (preserve-trans wt x₁) x₂
