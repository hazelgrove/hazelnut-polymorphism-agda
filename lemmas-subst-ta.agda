open import Prelude
open import Nat
open import List
open import core
open import contexts
open import weakening
open import exchange
open import lemmas-disjointness
open import binders-disjoint-checks

module lemmas-subst-ta where
  mutual
    binders-envfresh : ∀{Δ Γ Γ' y σ} → Δ , Γ ⊢ σ :s: Γ' → y # Γ → unbound-in-σ y σ → binders-unique-σ σ → envfresh y σ
    binders-envfresh {Γ' = Γ'} {y = y} (STAId x) apt unbound unique with ctxindirect Γ' y
    binders-envfresh {Γ' = Γ'} {y = y} (STAId x₁) apt unbound unique | Inl x = abort (somenotnone (! (x₁ y (π1 x) (π2 x)) · apt))
    binders-envfresh (STAId x₁) apt unbound unique | Inr x = EFId x
    binders-envfresh {Γ = Γ} {y = y} (STASubst  {y = z} subst x₁) apt (UBσSubst x₂ unbound) (BUσSubst x₃ x₄) =
                                                                                    EFSubst (binders-fresh x₁ {!!} x₃ {!!} x₂ apt)
                                                                                            (binders-envfresh subst (apart-extend1 Γ {!!} apt) {!!} {!!})
                                                                                            {!!}

    binders-fresh : ∀{ Δ Γ d1 d2 τ y} → Δ , Γ ⊢ d2 :: τ
                                      → binders-unique d1 -- todo: ditch?
                                      → binders-unique d2
                                      → binders-disjoint d1 d2
                                      → unbound-in y d2
                                      → Γ y == None
                                      → fresh y d2
    binders-fresh TAConst bu1 BUHole bd UBConst apt = FConst
    binders-fresh {y = y}  (TAVar {x = x} x₁) bu1 BUVar bd UBVar apt with natEQ y x
    binders-fresh (TAVar x₂) bu1 BUVar bd UBVar apt | Inl refl = abort (somenotnone (! x₂ · apt))
    binders-fresh (TAVar x₂) bu1 BUVar bd UBVar apt | Inr x₁ = FVar x₁
    binders-fresh {y = y} (TALam {x = x} x₁ wt) bu1 bu2 bd ub apt  with natEQ y x
    binders-fresh (TALam x₂ wt) bu1 bu2 bd (UBLam2 x₁ ub) apt | Inl refl = abort (x₁ refl)
    binders-fresh {Γ = Γ} (TALam {x = x} x₂ wt) bu1 (BULam bu2 x₃) bd (UBLam2 x₄ ub) apt | Inr x₁ =  FLam x₁ (binders-fresh wt bu1 bu2 (lem-bd-lam bd) ub (apart-extend1 Γ x₄ apt))
    binders-fresh (TAAp wt wt₁) bu1 (BUAp bu2 bu3 x) bd (UBAp ub ub₁) apt = FAp (binders-fresh wt BUHole bu2 BDConst ub apt)
                                                                                (binders-fresh wt₁ bu2 bu3 x ub₁ apt)
    binders-fresh (TAEHole x₁ x₂) bu1 (BUEHole x) bd (UBHole x₃) apt = FHole {!!} -- FHole {!binders-envfresh x₂ apt x₃ x !}
    binders-fresh (TANEHole x₁ wt x₂) bu1 (BUNEHole bu2 x) bd (UBNEHole x₃ ub) apt = FNEHole {!binders-envfresh x₂ apt x₃!} (binders-fresh wt bu1 bu2 (lem-bd-hole bd) ub apt)
    binders-fresh (TACast wt x₁) bu1 (BUCast bu2) bd (UBCast ub) apt = FCast (binders-fresh wt bu1 bu2 (lem-bd-cast bd) ub apt)
    binders-fresh (TAFailedCast wt x x₁ x₂) bu1 (BUFailedCast bu2) bd (UBFailedCast ub) apt = FFailedCast (binders-fresh wt bu1 bu2 (lem-bd-failedcast bd) ub apt)


  lem-subst : ∀{Δ Γ x τ1 d1 τ d2 } →
                  x # Γ →
                  binders-disjoint d1 d2 →
                  binders-unique d1 → -- todo: do i need both of these?
                  binders-unique d2 →
                  Δ , Γ ,, (x , τ1) ⊢ d1 :: τ →
                  Δ , Γ ⊢ d2 :: τ1 →
                  Δ , Γ ⊢ [ d2 / x ] d1 :: τ
  lem-subst apt bd bu1 bu2  TAConst wt2 = TAConst
  lem-subst {x = x} apt bd bu1 bu2  (TAVar {x = x'} x₂) wt2 with natEQ x' x
  lem-subst {Γ = Γ} apt bd bu1 bu2 (TAVar x₃) wt2 | Inl refl with lem-apart-union-eq {Γ = Γ} apt x₃
  lem-subst apt bd bu1 bu2  (TAVar x₃) wt2 | Inl refl | refl = wt2
  lem-subst {Γ = Γ} apt bd bu1 bu2  (TAVar x₃) wt2 | Inr x₂ = TAVar (lem-neq-union-eq {Γ = Γ} x₂ x₃)
  lem-subst {Δ = Δ} {Γ = Γ} {x = x} {d2 = d2} x#Γ (BDLam bd bd') (BULam bu1' ub) bu2 (TALam {x = y} {τ1 = τ1} {d = d} {τ2 = τ2} x₂ wt1) wt2
    with lem-union-none {Γ = Γ} x₂
  ... |  x≠y , y#Γ with natEQ y x
  ... | Inl eq = abort (x≠y (! eq))
  ... | Inr _  = TALam y#Γ (lem-subst {Δ = Δ} {Γ = Γ ,, (y , τ1)} {x = x} {d1 = d} (apart-extend1 Γ x≠y x#Γ) bd bu1' bu2 (exchange-ta-Γ {Γ = Γ} x≠y wt1)
                                         (weaken-ta (binders-fresh wt2 (BULam {τ = τ2} bu1' ub) bu2 (BDLam bd bd') bd' y#Γ) wt2))
  lem-subst apt (BDAp bd bd₁) (BUAp bu1 bu2 x₁) bu3 (TAAp wt1 wt2) wt3 = TAAp (lem-subst apt bd bu1 bu3 wt1 wt3) (lem-subst apt bd₁ bu2 bu3 wt2 wt3)
  lem-subst apt bd bu1 bu2 (TAEHole inΔ sub) wt2 = TAEHole inΔ (STASubst sub wt2)
  lem-subst apt (BDNEHole x₁ bd) (BUNEHole bu1 x₂) bu2 (TANEHole x₃ wt1 x₄) wt2 = TANEHole x₃ (lem-subst apt bd bu1 bu2 wt1 wt2) (STASubst x₄ wt2)
  lem-subst apt (BDCast bd) (BUCast bu1) bu2 (TACast wt1 x₁) wt2 = TACast (lem-subst apt bd bu1 bu2 wt1 wt2) x₁
  lem-subst apt (BDFailedCast bd) (BUFailedCast bu1) bu2 (TAFailedCast wt1 x₁ x₂ x₃) wt2 = TAFailedCast (lem-subst apt bd bu1 bu2 wt1 wt2) x₁ x₂ x₃
