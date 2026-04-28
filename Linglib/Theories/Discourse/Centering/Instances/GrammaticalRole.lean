import Linglib.Theories.Discourse.Centering.Defs
import Mathlib.Order.Basic

/-!
# Centering — Grammatical Role Cf Ranking
@cite{kameyama-1986} @cite{gordon-grosz-gilliom-1993} @cite{grosz-joshi-weinstein-1995}

The English-default Cf ranking, by grammatical role:
SUBJECT > OBJECT > OTHER.

@cite{grosz-joshi-weinstein-1995} §5 surveys the evidence (their
examples 11–14) that grammatical role is the major determinant of Cf
ranking in English. @cite{kameyama-1986} argued for grammatical role
over @cite{sidner-1979}'s focus-based proposal; the
@cite{gordon-grosz-gilliom-1993} repeated-name penalty experiments
provide independent empirical support.
-/

set_option autoImplicit false

namespace Discourse.Centering

/-- Grammatical role used to rank Cf elements (@cite{kameyama-1986},
    @cite{gordon-grosz-gilliom-1993}): SUBJECT > OBJECT > OTHER. -/
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
