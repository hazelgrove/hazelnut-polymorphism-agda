open import Nat
open import Prelude

open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core

open import debruijn.debruijn-weakening
open import debruijn.debruijn-eq-dec
open import debruijn.debruijn-ground-dec


open import debruijn.debruijn-lemmas-index
open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-prec
open import debruijn.debruijn-lemmas-meet
open import debruijn.debruijn-lemmas-ground
open import debruijn.debruijn-lemmas-wf
open import debruijn.debruijn-lemmas-subst
open import debruijn.debruijn-lemmas-complete

open import debruijn.debruijn-typing-subst
open import debruijn.debruijn-typed-elaboration
open import debruijn.debruijn-type-assignment-unicity
open import debruijn.debruijn-complete-elaboration
open import debruijn.debruijn-complete-preservation

open import debruijn.debruijn-preservation

open import debruijn.debruijn-progress 

open import debruijn.debruijn-parametricity

open import debruijn.debruijn-graduality

module debruijn.debruijn-all where
