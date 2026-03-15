import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Semantics.Alternatives.Lexical
import Mathlib.Data.Rat.Defs
import Linglib.Core.Interface

/-!
# RSA Scalar Implicatures
@cite{bergen-levy-goodman-2016} @cite{frank-goodman-2012} @cite{goodman-frank-2016}

RSA scalar implicature infrastructure. Scale positions are looked up
from word forms via `Alternatives.scaleOf`.

## Status

The ℚ-based RSA evaluation infrastructure (RSA.Eval, boolToRat, RSAScenario) has been
removed. The scalar implicature results and RSA ImplicatureTheory instance need to be
re-implemented using the new RSAConfig framework.
-/

namespace RSA.ScalarImplicatures

open Alternatives

/-- World states for scalar implicature reasoning (coarser partition) -/
inductive ScalarWorld where
  | none  -- No one (0)
  | some  -- Some but not all (1 or 2 out of 3)
  | all   -- All (3 out of 3)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- RSA scalar implicature result. -/
structure RSAScalarResult where
  utterance : String
  probSomeNotAll : ℚ
  probAll : ℚ
  implicatureHolds : Bool
  deriving Repr

/-- Check if any word in the list is a "some" quantifier. -/
def hasSomeQuantifier (words : List String) : Bool :=
  words.any λ w => scaleOf w == some (.quantifier .some_)

/-- Check if any word in the list is an "all/every" quantifier. -/
def hasAllQuantifier (words : List String) : Bool :=
  words.any λ w => scaleOf w == some (.quantifier .all)

end RSA.ScalarImplicatures
