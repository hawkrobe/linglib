import Linglib.Semantics.Verb.Root.Kinds
import Linglib.Semantics.Verb.Root.Arity

/-!
# Salience classes

[lucy-1994]'s classification of verbal roots by required transitiviser —
"salience" is his term for the default semantic values in a root that
influence overt case marking, which is why the classifier lives in the
argument-realization layer. Stated over the (kind signature × arity)
coordinates: agent salient (intransitive manner roots), agent-patient
salient (root transitives), patient salient (intransitive change-of-state
roots). The positional diagnostic (`IsPositional`) is deliberately
separate and arity-free — positional roots cross-cut the transitiviser
classes rather than forming a fourth case.

Originates with [lucy-1994] (Yucatec `=t`, `=∅`, `=s`); the Yucatec
instantiation with attested derivations is `Studies/Lucy1994.lean`, and
`Studies/Coon2019.lean` consumes the annotation-level hom
(`Classification.salienceClass` in `Verb/Root/Classification.lean`) for
the Chuj root classes.

## Main declarations

* `SalienceClass`
* `IsAgentSalient`, `IsPatientSalient`, `IsPositional`
* `SalienceClass.ofKinds` — the pair-level classifier
* `SalienceClass.ofKinds_close` — closure invariance on cause-free
  signatures
-/

namespace ArgumentStructure

open Verb

/-- Lucy's "three large predicate root classes", named for the
    argument(s) the underived root makes salient. Positional roots are
    deliberately not a case: they fall outside the transitiviser cut
    (`IsPositional`). -/
inductive SalienceClass where
  | agent
  | agentPatient
  | patient
  deriving DecidableEq, Repr

variable (s : Root.Kinds) (ar : Root.Arity)

/-- Agent salient: intransitive manner-of-action root ("actions or
    activities that some entity undertakes"). -/
abbrev IsAgentSalient : Prop :=
  ar = .noTheme ∧ .manner ∈ s ∧ .result ∉ s

/-- Patient salient: intransitive change-of-state root ("state changes
    that some entity undergoes more or less spontaneously"). -/
abbrev IsPatientSalient : Prop :=
  ar = .noTheme ∧ .manner ∉ s ∧ .result ∈ s

/-- Positional: pure stative configurational signature. Deliberately
    arity-free — a positional root may also zero-derive a transitive
    ([lucy-1994]'s *čin* 'bend'), so the positional class cross-cuts
    the transitiviser cut. -/
abbrev IsPositional : Prop := s = {.state}

/-- The transitiviser cut. Agent-patient salience is root transitivity
    (`selectsTheme`), not a feature configuration; the two intransitive
    classes split by signature; intransitive signatures with neither
    manner nor result — pure statives included — are outside the cut. -/
def SalienceClass.ofKinds : Option SalienceClass :=
  if ar = .selectsTheme then some .agentPatient
  else if IsAgentSalient s ar then some .agent
  else if IsPatientSalient s ar then some .patient
  else none

/-- Collocational closure does not move the transitiviser cut on
    cause-free signatures: the only available closure edge is
    result→state, which no arm of the classifier consults. -/
theorem SalienceClass.ofKinds_close (h : LexKind.cause ∉ s) :
    ofKinds s.close ar = ofKinds s ar := by
  revert s ar; decide

/-- The cause-free hypothesis of `ofKinds_close` is necessary: a lone
    `cause` atom is outside the cut at base but patient salient after
    closure. -/
theorem SalienceClass.ofKinds_close_cause :
    ofKinds {.cause} .noTheme = none ∧
    ofKinds (Root.Kinds.close {.cause}) .noTheme = some .patient := by
  decide

end ArgumentStructure
