{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import core
open import core-type
open import core-exp
open import core-subst

open import parametricity2-defs
open import parametricity2-lemmas1

open import preservation
open import ground-dec
open import lemmas-consistency
open import lemmas-wf
open import eq-dec
open import lemmas-ground

module parametricity2-lemmas2 where

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
    d1' =0c d2 + Σ[ d2' ∈ ihexp ] (d2 ↦* d2' × (d1' =0c d2' + d2' indet))
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin step ctxout) with eq0-ctxinc eq0 ctxin

  -- See note above -- all of these preserve =0c
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITCastID ctxout) | d2in , ε2 , ctxin' , Eq0CastL eq0in , eq0e , form = Inl (eq0c-ctx ctxin ctxout (Eq0CastL eq0c-refl) eq0)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin (ITCastSucceed x) ctxout) | d2in , ε2 , ctxin' , Eq0CastL eq0in , eq0e , form = Inl (eq0c-ctx ctxin ctxout (Eq0CastL (Eq0CastL eq0c-refl)) eq0)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin (ITCastFail x x₁ x₂) ctxout) | d2in , ε2 , ctxin' , Eq0CastL eq0in , eq0e , form = Inl (eq0c-ctx ctxin ctxout (Eq0CastL (Eq0CastL (eq0cr-lemma' eq0c-refl))) eq0)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin (ITGround x) ctxout) | d2in , ε2 , ctxin' , Eq0CastL eq0in , eq0e , form = Inl (eq0c-ctx ctxin ctxout (Eq0CastL (eq0cr-lemma (eq0cr-lemma eq0c-refl))) eq0)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin (ITExpand x) ctxout) | d2in , ε2 , ctxin' , Eq0CastL eq0in , eq0e , form = Inl (eq0c-ctx ctxin ctxout (Eq0CastL (eq0cr-lemma (eq0cr-lemma eq0c-refl))) eq0)

  -- Pick a better context. Add as a conclusion to eq0-ctxinc that the ctx we select absorbs all casts from the term.
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin step ctxout) | .(_ ⟨ _ ⇒ _ ⟩) , ε2 , ctxin' , Eq0NoLeft (Eq0CastR x) , eq0e , form
    = abort (π1 (form _ _ _) refl)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin step ctxout) | .(_ ⟨ _ ⇒⦇-⦈⇏ _ ⟩) , ε2 , ctxin' , Eq0NoLeft (Eq0FailedCastR x) , eq0e , form
    = abort (π2 (form _ _ _) refl)

  -- Cases where we have an ITLam but the right side has some casts to the left of the application to deal with (we have to find our way to an ITApCast)
  -- The termination checker isn't happy with my use of induction here, but I know it terminates because every time I call it inductively,
  -- I'm reducing the metric of: let n_k be the number of casts to the left of k apps. Let n = the syntactic size of the term.
  -- Lexicographically order these measures n_infinity > ... > n_2 > n_1 > n_0 > n.
  -- Note that only ITExpand and ITGround increase these measures, with other cast steps decreasing them, but
  -- I always provide following sequences of reductions such that
  -- By the time I use the inductive hypothesis, this measure has decreased.
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout) 
    | (.((_ ⟨ _ ⇒ _ ⟩) ∘ _) , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR x)) x₁)) , eq0e , form) with wt-filling wt2 ctxin'
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout)
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR (Eq0NoCasts ()))) x₁)) , eq0e , form | (_ , (TAAp (TACast {d = .⦇-⦈} {τ2 = .(_ ==> _)} TAEHole x₃ ConsistHole2) wt2''))
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout)
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR (Eq0NoCasts ()))) x₁)) , eq0e , form | _ , TAAp (TACast {d = ⦇⌜ _ ⌟⦈} {τ2 = (_ ==> _)} (TANEHole wt2') x₃ ConsistHole2) wt2''
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout)
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR (Eq0NoCasts ()))) x₁)) , eq0e , form | _ , TAAp (TACast {d = .(_ ∘ _)} {τ2 = .(_ ==> _)} (TAAp wt2' wt2c) x₃ ConsistHole2) wt2''
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout)
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR (Eq0NoCasts ()))) x₁)) , eq0e , form | _ , TAAp (TACast {d = .(_ < _ >)} {τ2 = .(_ ==> _)} (TATAp x₄ wt2' x₆) x₃ ConsistHole2) wt2''
  ... | _ , TAAp (TACast {d = .(_ ⟨ _ ⇒⦇-⦈⇏ _ ⟩)} {τ2 = .(_ ==> _)} (TAFailedCast wt2' x₄ x₆ x₇) x₃ ConsistHole2) wt2'' = {!   !} -- lemma for indet
  -- TODO: Panic at the above. It's the case we can't show.
  -- Consider, evaluation of the argument diverges. We can get a terminating execution by substituting it in (which can throw it away). But
  -- By having a failed cast we force evaluation of the argument, which can be non-terminating (think Ω).
  -- This can be fixed with call-by-value semantics.
  -- Supposing d4 is a value, then we know we have to reduce the left hand side of the ap. But since we have =0c, it must be a Lam.
  -- But then, we get that d2 is indet, exactly what we want to show.
  ... | _ , TAAp {d2 = d22} (TACast {d = d21} {τ1 = τ1 ==> τ2} {τ2 = (τ3 ==> τ4)} wt2' x₃ (ConsistArr x₄ x₆)) wt2'' with evalctx-out (((d21 ∘ (d22 ⟨ τ3 ⇒ τ1 ⟩)) ⟨ τ2 ⇒ τ4 ⟩)) ctxin'
  ...   | _ , ctxout' with parametricity21-lemma-ctx wt1 (preservation wt2 (Step ctxin' ITApCast ctxout')) (eq0c-sym (eq0c-ctx ctxin' ctxout' (Eq0NoLeft (Eq0CastR (Eq0NoCasts (Eq0Ap (Eq0CastL eq0c-refl) (eq0cr-lemma eq0c-refl))))) (eq0c-sym eq0))) ((Step ctxin ITLam ctxout))
  ...     | Inl res = Inr (_ , MSStep (Step ctxin' ITApCast ctxout') MSRefl , Inl res)
  ...     | Inr (d2' , steps' , eq0final) = Inr (d2' , MSStep (Step ctxin' ITApCast ctxout') steps' , eq0final)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout) 
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR x)) x₁)) , eq0e , form | _ , TAAp {d2 = d4} (TACast {d = (d3 ⟨ τ1 ⇒ ⦇-⦈ ⟩)} {τ2 = (τ2 ==> τ3)} (TACast wt2' x₄ x₆) x₃ ConsistHole2) wt2'' with ground-dec τ1 | ground-dec (τ2 ==> τ3) | ~dec τ1 (τ2 ==> τ3)
  ... | Inl gndl | Inl gndr | Inl consis with evalctx-out (d3 ∘ d4) ctxin'
  ...   | _ , ctxout' rewrite gnd-gnd-consis-eq gndl gndr consis with parametricity21-lemma-ctx wt1 (preservation wt2 (Step (evalctx-compose ctxin' (FHAp1 FHOuter)) (ITCastSucceed gndr) (evalctx-compose ctxout' (FHAp1 FHOuter)))) ((eq0c-sym (eq0c-ctx ctxin' ctxout' (Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0CastL (Eq0CastL eq0c-refl)) eq0c-refl))) (eq0c-sym eq0)))) (Step ctxin ITLam ctxout)
  ...       | Inl res = Inr (_ , MSStep (Step (evalctx-compose ctxin' (FHAp1 FHOuter)) (ITCastSucceed gndr) (evalctx-compose ctxout' (FHAp1 FHOuter))) MSRefl , Inl res)
  ...       | Inr (d2' , steps' , eq0final) = Inr (d2' , MSStep (Step (evalctx-compose ctxin' (FHAp1 FHOuter)) (ITCastSucceed gndr) (evalctx-compose ctxout' (FHAp1 FHOuter))) steps' , eq0final)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout) 
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR x)) x₁)) , eq0e , form | _ , TAAp {d2 = d4} (TACast {d = (d3 ⟨ τ1 ⇒ ⦇-⦈ ⟩)} {τ2 = (τ2 ==> τ3)} (TACast wt2' x₄ x₆) x₃ ConsistHole2) wt2''
    | Inl gndl | Inl gndr | Inr consis with evalctx-out ((d3 ⟨ τ1 ⇒⦇-⦈⇏ (τ2 ==> τ3) ⟩) ∘ d4) ctxin'
  ... | _ , ctxout' with parametricity21-lemma-ctx wt1 (preservation wt2 (Step (evalctx-compose ctxin' (FHAp1 FHOuter)) (ITCastFail gndl gndr consis) (evalctx-compose ctxout' (FHAp1 FHOuter)))) ((eq0c-sym (eq0c-ctx ctxin' ctxout' (Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0CastL (Eq0CastL (eq0cr-lemma' eq0c-refl))) eq0c-refl))) (eq0c-sym eq0)))) (Step ctxin ITLam ctxout)
  ...       | Inl res = Inr (_ , MSStep (Step (evalctx-compose ctxin' (FHAp1 FHOuter)) (ITCastFail gndl gndr consis) (evalctx-compose ctxout' (FHAp1 FHOuter))) MSRefl , Inl res)
  ...       | Inr (d2' , steps' , eq0final) = Inr (d2' , MSStep (Step (evalctx-compose ctxin' (FHAp1 FHOuter)) (ITCastFail gndl gndr consis) (evalctx-compose ctxout' (FHAp1 FHOuter))) steps' , eq0final)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout) 
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR x)) x₁)) , eq0e , form | _ , TAAp {d2 = d4} (TACast {d = (d3 ⟨ τ1 ⇒ ⦇-⦈ ⟩)} {τ2 = (τ2 ==> τ3)} (TACast wt2' x₄ x₆) x₃ ConsistHole2) wt2''
    | Inl gndl | Inr gndr | _ = {!   !}
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout) 
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR x)) x₁)) , eq0e , form | _ , TAAp {d2 = d4} (TACast {d = (d3 ⟨ τ1 ⇒ ⦇-⦈ ⟩)} {τ2 = (τ2 ==> τ3)} (TACast wt2' x₄ x₆) x₃ ConsistHole2) wt2''
    | Inr gndl | Inl gndr | _ = {!   !}
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITLam ctxout) 
    | _ , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0CastR x)) x₁)) , eq0e , form | _ , TAAp {d2 = d4} (TACast {d = (d3 ⟨ τ1 ⇒ ⦇-⦈ ⟩)} {τ2 = (τ2 ==> τ3)} (TACast wt2' x₄ x₆) x₃ ConsistHole2) wt2''
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
    | .((_ ⟨ _ ⇒⦇-⦈⇏ _ ⟩) ∘ _) , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap (Eq0NoLeft (Eq0FailedCastR x)) x₁)) , eq0e , form = 
      {!   !} -- d2 contains a failed cast so it will be indet (must show it doesn't diverge?)
      -- Need lemma: d2 has a failed cast and eq0 d1, d2 will eval to indet
      -- lemma -- if d1 o d2 -> final then d2 -> final, then use the fact that d2 =0c d4
      -- and parametricity to show d4 -> final, but d4 has failed cast that never goes away so it's indet
      -- Alternatively, if just showing parametricity22, we have d4 -> final and d4 has a failedcast
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin ITApCast ctxout) 
    | .(_ ∘ _) , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0Ap x x₁)) , eq0e , form = 
      Inl (eq0c-ctx ctxin ctxout (Eq0NoLeft (Eq0CastR (Eq0NoCasts (Eq0Ap (Eq0CastL eq0c-refl) (eq0cr-lemma eq0c-refl))))) eq0) -- Using ITApCast doesn't change =0 status

-- These are the actual interesting cases.
  parametricity21-lemma-ctx {d1 = d1} {d2 = d2} wt1 wt2 eq0 (Step ctxin (ITLam {d1 = d3} {d2 = d4}) ctxout) 
    | ((·λ[ _ ] _) ∘ _) , ε2 , ctxin' , 
    Eq0NoLeft (Eq0NoCasts (Eq0Ap {d4 = d6} (Eq0NoLeft (Eq0NoCasts (Eq0Lam {d2 = d5} x))) x₁)) , eq0e , form with eq0c-ctxout (eq0-substc d3 d5 x₁ x) eq0e ctxout
  ... | (d2out , eqeout , eq0out) = Inr (_ , MSStep (Step ctxin' ITLam eqeout) MSRefl , Inl eq0out)
  parametricity21-lemma-ctx {d2 = d2} wt1 wt2 eq0 (Step ctxin step ctxout) | .(_ < _ >) , ε2 , ctxin' , Eq0NoLeft (Eq0NoCasts (Eq0TAp x)) , eq0e = {!   !}
 
