import Linglib.Theories.Semantics.Presupposition.OntologicalPreconditions
import Linglib.Phenomena.Presupposition.Diagnostics

/-!
# Bridge: Ontological Preconditions -> Presupposition Diagnostics

Connects the ontological preconditions theory (Roberts & Simons 2024) to the
empirical diagnostic data in `Phenomena.Presupposition.Diagnostics`.

The theory predicts that preconditions (which project) pass "allows for"
and consequences (which don't project) pass "results in".
-/

namespace Phenomena.Presupposition.OntologicalPreconditionsBridge

open Phenomena.Presupposition.Diagnostics

/--
The theory predicts the empirical pattern: preconditions ↔ projection.

Content that is a precondition (passes "allows for") should project.
Content that is a consequence (passes "results in") should not project.
-/
def theoryPredictsPattern : Bool :=
  -- Prior state: is precondition, passes "allows for", projects
  stopPattern.priorPassesAllowsFor == true &&
  priorStateProjection.projectsThroughNegation == true &&
  -- Result state: is consequence, fails "allows for", doesn't project
  stopPattern.resultFailsAllowsFor == true &&
  resultStateProjection.projectsThroughNegation == false

end Phenomena.Presupposition.OntologicalPreconditionsBridge
