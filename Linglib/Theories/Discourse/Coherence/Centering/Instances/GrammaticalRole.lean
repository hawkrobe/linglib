import Linglib.Theories.Discourse.Coherence.Centering.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Nat

/-!
# Centering — Grammatical Role Cf Ranking
@cite{kameyama-1986} @cite{gordon-grosz-gilliom-1993} @cite{grosz-joshi-weinstein-1995}

The English-default Cf ranking, by grammatical role:
SUBJECT > OBJECT > OTHER.

@cite{grosz-joshi-weinstein-1995} §5 surveys the evidence (their
examples 11–14) that grammatical role is the major determinant of Cf
ranking in English. @cite{kameyama-1986} argued for grammatical role
over @cite{sidner-1979}'s thematic-role proposal; the
@cite{gordon-grosz-gilliom-1993} repeated-name penalty experiments
provide independent empirical support.

This file provides the `Realization E GrammaticalRole` /
`Utterance E GrammaticalRole` instantiation of the Centering framework.
The thematic-role variant lives in the sibling `ThematicRole.lean`.
-/

set_option autoImplicit false

namespace Discourse.Coherence.Centering

-- ════════════════════════════════════════════════════
-- § Grammatical Role
-- ════════════════════════════════════════════════════

/-- Grammatical role used to rank Cf elements (@cite{kameyama-1986},
    @cite{gordon-grosz-gilliom-1993}): SUBJECT > OBJECT > OTHER. -/
inductive GrammaticalRole where
  | subject
  | object
  | other
  deriving DecidableEq, Repr

@[simp] def GrammaticalRole.rank : GrammaticalRole → Nat
  | .subject => 2
  | .object  => 1
  | .other   => 0

instance : LinearOrder GrammaticalRole :=
  LinearOrder.lift' GrammaticalRole.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [GrammaticalRole.rank])

/-- The Cf-ranker instance: the standard English assumption. -/
instance : CfRanker GrammaticalRole where
  rank := GrammaticalRole.rank

theorem subject_gt_object : (GrammaticalRole.subject : GrammaticalRole) > .object := by decide

theorem object_gt_other : (GrammaticalRole.object : GrammaticalRole) > .other := by decide

end Discourse.Coherence.Centering
