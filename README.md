# hazelnut-polymorphism-agda
This repository is the De Bruijn version of the mechanization of the work described in our TFP24 paper.

# Where To Find Each Theorm

The main syntctic categories and judgements are found in [core-type.agda](core-type.agda), [core-exp.agda](core-exp.agda), and [core.agda](core.agda). De Bruijn index operations and substitutions are defined in [core-subst.agda](core-subst.agda).

The proofs of each part of Theorem 3 can be found in:

- [elaborability.agda](elaborability.agda)
- [elaboration-generality.agda](elaboration-generality.agda)
- [elaboration-unicity.agda](elaboration-unicity.agda)
- [typed-elaboration.agda](typed-elaboration.agda)
- [type-assignment-unicity.agda](type-assignment-unicity.agda)

The proofs of each part of Theorem 4 can be found in:

- [preservation.agda](preservation.agda)
- [progress.agda](progress.agda)

The proofs of each part of Theorem 5 can be found in:

- [complete-elaboration.agda](complete-elaboration.agda)
- [complete-preservation.agda](complete-preservation.agda)
- [complete-progress.agda](complete-progress.agda)

Our work on parametricity and graduality can be found in:

- [parametricity.agda](parametricity.agda)
- [graduality.agda](graduality.agda)
