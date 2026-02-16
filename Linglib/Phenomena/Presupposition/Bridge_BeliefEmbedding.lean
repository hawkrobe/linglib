import Linglib.Theories.Semantics.Presupposition.BeliefEmbedding
import Linglib.Phenomena.Presupposition.ProjectiveContent

/-!
# Bridge: Belief Embedding -> Projective Content Taxonomy

Connects the Schlenker local context machinery for belief embedding
to the Tonhauser et al. (2013) projective content taxonomy.

Proves that OLE (Obligatory Local Effect) status matches shift behavior
under belief predicates, and verifies trigger-specific predictions.

## References

- Schlenker (2009). Local Contexts. Semantics & Pragmatics 2:3.
- Tonhauser, Beaver, Roberts & Simons (2013). Toward a Taxonomy of
  Projective Content. Language 89(1).
-/

namespace Phenomena.Presupposition.Bridge_BeliefEmbedding

open Semantics.Presupposition.BeliefEmbedding
open Phenomena.Presupposition.ProjectiveContent

/--
Determines whether a projective trigger's content shifts to the attitude
holder's perspective under belief embedding.

OLE = yes: Content shifts to attitude holder (computed from their beliefs)
OLE = no: Content remains attributed to speaker (no perspective shift)
-/
def shiftsUnderBelief : ProjectiveClass → Bool
  | .classA => true   -- OLE = yes
  | .classB => false  -- OLE = no
  | .classC => true   -- OLE = yes
  | .classD => false  -- OLE = no

/--
OLE status matches shift behavior.
-/
theorem ole_matches_shift (c : ProjectiveClass) :
    shiftsUnderBelief c = true ↔ c.ole = .obligatory := by
  cases c <;> simp [shiftsUnderBelief, ProjectiveClass.ole]

/--
The Schlenker local context machinery derives the OLE
predictions from Tonhauser et al. (2013).

For any trigger:
- If OLE=yes (Class A, C): Local context under belief = attitude holder's beliefs
- If OLE=no (Class B, D): Local context under belief = global context (speaker)

This explains why "stop" presuppositions shift to attitude holders but
"damn" expressives don't.
-/
theorem ole_from_local_contexts (trigger : ProjectiveTrigger) :
    shiftsUnderBelief trigger.toClass = true ↔
    trigger.toClass.ole = .obligatory := by
  exact ole_matches_shift trigger.toClass

/--
Class C triggers (stop, know, only) have OLE=yes.
-/
example : ProjectiveTrigger.stop_prestate.toClass.ole = .obligatory := rfl
example : ProjectiveTrigger.know_complement.toClass.ole = .obligatory := rfl

/--
Class B triggers (expressives, appositives) have OLE=no.
-/
example : ProjectiveTrigger.expressive.toClass.ole = .notObligatory := rfl
example : ProjectiveTrigger.appositive.toClass.ole = .notObligatory := rfl

end Phenomena.Presupposition.Bridge_BeliefEmbedding
