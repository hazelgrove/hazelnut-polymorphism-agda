open import Nat
open import Prelude
open import core-type
open import core-exp
open import core
open import progress

open import lemmas-complete

module complete-progress where

  data okc : (d : ihexp) → Set where
    V : ∀{d} → d val → okc d
    S : ∀{d} → Σ[ d' ∈ ihexp ] (d ↦ d') → okc d

  complete-progress : {d : ihexp} {τ : htyp} →
    ∅ ⊢ d :: τ →
    d dcomplete →
    okc d
  complete-progress wt comp with progress wt
  complete-progress wt comp | I ind = abort (complete-indet comp ind)
  complete-progress wt comp | S step = S step
  complete-progress wt comp | BV (BVVal v) = V v
  complete-progress wt (DCCast _ _ ()) | BV (BVHoleCast _ _)
  complete-progress (TACast _ _ con) (DCCast _ tc1 tc2) | BV (BVArrCast neq _) = abort (neq (complete-consistency con tc1 tc2))
  complete-progress (TACast _ _ con) (DCCast _ tc1 tc2) | BV (BVForallCast neq _) = abort (neq (complete-consistency con tc1 tc2))