import Linglib.Theories.Discourse.Coherence.Centering.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Nat

/-!
# Centering — Thematic Role Cf Ranking (Sidner 1979)
@cite{sidner-1979} @cite{grosz-joshi-weinstein-1995}

The original Centering ranking, due to @cite{sidner-1979}: by thematic
role rather than grammatical function. Subsequent work
(@cite{kameyama-1986}, @cite{gordon-grosz-gilliom-1993}) argued for
grammatical role over thematic role for English; this instance
preserves the original proposal as an alternative ranker for
applications where thematic role is the relevant dimension (e.g.,
languages with non-canonical alignment, psych verbs whose experiencer
outranks their stimulus).

The ranking used here:
EXPERIENCER > AGENT > GOAL > THEME > OTHER

The exact Sidner ranking is debated; the qualitative split is
experiencer-and-agent first (sentient subjects), then arguments
defined by their relation to the verb (goal, theme), with everything
else last. This is the ordering invoked when, e.g., a psych verb's
object outranks its subject.
-/

set_option autoImplicit false

namespace Discourse.Coherence.Centering

-- ════════════════════════════════════════════════════
-- § Thematic Role (Sidner 1979 ranker)
-- ════════════════════════════════════════════════════

/-- Coarse thematic role used as an alternative Cf ranker
    (@cite{sidner-1979}). -/
inductive ThematicRole where
  | experiencer
  | agent
  | goal
  | theme
  | other
  deriving DecidableEq, Repr

@[simp] def ThematicRole.rank : ThematicRole → Nat
  | .experiencer => 4
  | .agent       => 3
  | .goal        => 2
  | .theme       => 1
  | .other       => 0

instance : LinearOrder ThematicRole :=
  LinearOrder.lift' ThematicRole.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [ThematicRole.rank])

/-- The Sidner-style Cf-ranker instance. -/
instance : CfRanker ThematicRole where
  rank := ThematicRole.rank

theorem experiencer_gt_agent :
    (ThematicRole.experiencer : ThematicRole) > .agent := by decide

theorem agent_gt_theme :
    (ThematicRole.agent : ThematicRole) > .theme := by decide

end Discourse.Coherence.Centering
