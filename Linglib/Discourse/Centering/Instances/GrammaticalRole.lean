import Linglib.Discourse.Centering.Defs
import Mathlib.Order.Basic

/-!
# Centering — Grammatical Role Cf Ranking
[kameyama-1986] [gordon-grosz-gilliom-1993] [grosz-joshi-weinstein-1995]

The English-default Cf ranking, by grammatical role:
SUBJECT > OBJECT > OTHER.

[grosz-joshi-weinstein-1995] §5 surveys the evidence (their
examples 11–14) that grammatical role is the major determinant of Cf
ranking in English. [kameyama-1986] argued for grammatical role
over [sidner-1979]'s focus-based proposal; the
[gordon-grosz-gilliom-1993] repeated-name penalty experiments
provide independent empirical support.
-/

namespace Discourse.Centering

/-- Grammatical role used to rank Cf elements ([kameyama-1986],
    [gordon-grosz-gilliom-1993]): SUBJECT > OBJECT > OTHER. -/
inductive GrammaticalRole where
  | subject
  | object
  | other
  deriving DecidableEq, Repr, Fintype

def GrammaticalRole.rank : GrammaticalRole → Nat
  | .subject => 2
  | .object  => 1
  | .other   => 0

/-- The Cf-ranker instance: the standard English assumption. -/
instance : CfRanker GrammaticalRole where
  rank := GrammaticalRole.rank

instance : LinearOrder GrammaticalRole := CfRanker.toLinearOrder _

end Discourse.Centering
