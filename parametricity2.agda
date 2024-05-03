{-# OPTIONS --no-termination-check #-}

open import Nat
open import Prelude
open import core
open import core-type
open import core-exp
open import core-subst

open import parametricity2-defs
open import parametricity2-lemmas1
open import parametricity2-lemmas2

open import preservation
open import ground-dec
open import lemmas-consistency
open import lemmas-wf
open import eq-dec
open import lemmas-ground

module parametricity2 where

  parametricity21 :
    ∀{d1 d2 v1} →
    d1 =0c d2 →
    d1 ↦* v1 →
    v1 boxedval →
    Σ[ v2 ∈ ihexp ]( d2 ↦* v2 × ((v2 boxedval × v1 =0c v2) + v2 indet ))
  parametricity21 eq0 step bv = {!   !}
          
