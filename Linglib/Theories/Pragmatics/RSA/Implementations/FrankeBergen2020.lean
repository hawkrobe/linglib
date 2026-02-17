/-
# Global Intentions: RSA with Exhaustification Ambiguity

Implementation of Franke & Bergen (2020) "Theory-driven statistical modeling
for semantics and pragmatics" - the Global Intentions (GI) model.

## Insight

This IS an exhaustification phenomenon: the speaker chooses where to insert
EXH (matrix, outer, inner positions). This is different from scope ambiguity,
which is just about quantifier scope configurations.

## Model

GI treats EXH parse as speaker OUTPUT. The speaker jointly optimizes
(utterance, parse) pairs. Uses the unified `Exhaustifiable` typeclass
which invokes `applyExhAtParse` from the NeoGricean exhaustivity machinery.

## References

- Franke, M. & Bergen, L. (2020). "Theory-driven statistical modeling"
- Phenomena data in: Linglib.Phenomena.FrankeBergen2020.Data
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Core.Parse
import Linglib.Theories.Pragmatics.NeoGricean.Exhaustivity.Interface

namespace RSA.Implementations.FrankeBergen2020

/-!
This file previously contained the full Franke & Bergen (2020) RSA implementation.
All definitions and theorems depend on Phenomena types (AristQuant, NestedAristotelian,
allSentences, exhParses, getPosterior, etc.) and have been moved to
`Linglib.Phenomena.Quantification.RSA_FrankeBergen2020Bridge`.
-/

end RSA.Implementations.FrankeBergen2020
