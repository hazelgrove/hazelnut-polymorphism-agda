open import Prelude
open import core
open import Nat
open import contexts

module rewrite-util where

  rewrite-gamma : ∀{Δ Θ Γ Γ' d t} → Γ == Γ' → Δ , Θ , Γ ⊢ d :: t → Δ , Θ , Γ' ⊢ d :: t
  rewrite-gamma eq ta rewrite eq = ta

  rewrite-typ : ∀{Δ Θ Γ d t t'} → t == t' → Δ , Θ , Γ ⊢ d :: t → Δ , Θ , Γ ⊢ d :: t'
  rewrite-typ eq ta rewrite eq = ta
