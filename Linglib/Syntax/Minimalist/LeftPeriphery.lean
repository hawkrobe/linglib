module

public import Linglib.Semantics.Questions.QParticleLayer
public import Linglib.Semantics.Presupposition.Verb

/-!
# The interrogative left periphery

[dayal-2025] builds question meaning at three points of the left periphery,
`[SAP SA_ASK [PerspP PRO Persp_CQ [CP C_WH [TP …]]]]`: clause-typing at C,
where a proposition becomes a set of propositions (`WHFeature`); centering at
PerspP, which introduces a perspectival center who may not know the answer
(`Question.PossiblyIgnorant`); and the illocutionary act at SAP. Embedding
predicates select up to one of the layers (`SelectionClass`, read off a
lexical entry by `deriveSelectionClass`): rogatives take CP only, PerspP, or
SAP, responsives take CP and, where their meaning leaves the center's
ignorance open, PerspP.

## References

* [dayal-2025]
* [mccloskey-2006]
-/

@[expose] public section

namespace Minimalist

/-- The WH-feature on C: interrogative, declarative, or unspecified with typing
delayed to a higher layer (Hindi-Urdu polar clauses, [dayal-2025] §4.4). -/
inductive WHFeature where
  | plusWH
  | minusWH
  | alphaWH
  deriving DecidableEq, Repr, Fintype

/-- Embedding predicates by the largest left-peripheral structure they select
([dayal-2025] §1.2): uninterrogatives take no interrogative; rogatives take CP
only (*depend on*, *investigate*), PerspP (*wonder*, *want to know*) or SAP
(*ask*); responsives (*know*, *remember*, *forget*) take CP and, where their
meaning leaves the center's ignorance open, PerspP. -/
inductive SelectionClass where
  | uninterrogative
  | rogativeCP
  | rogativePerspP
  | rogativeSAP
  | responsive
  deriving DecidableEq, Repr, Fintype

/-- The largest layer a class selects. -/
def SelectionClass.layer : SelectionClass → Option Question.QParticleLayer
  | .uninterrogative => none
  | .rogativeCP => some .cp
  | .rogativePerspP => some .perspP
  | .rogativeSAP => some .sap
  | .responsive => some .perspP

/-- The selection class of a lexical entry. Question-taking factives are responsive,
non-veridical doxastic attitudes uninterrogative, question-taking speech-act verbs select SAP,
opaque question-taking verbs PerspP, and other question-taking verbs CP. -/
def deriveSelectionClass (v : Verb) : SelectionClass :=
  if ¬ v.TakesQuestion then .uninterrogative
  else if v.IsFactive then .responsive
  else match v.attitude with
  | some (.doxastic .nonVeridical) => .uninterrogative
  | _ =>
    if v.speechActVerb && citationQuestion v then .rogativeSAP
    else if v.opaqueContext && citationQuestion v then .rogativePerspP
    else if citationQuestion v then .rogativeCP
    else .uninterrogative
where
  /-- The citation frame is an embedded question. -/
  citationQuestion (v : Verb) : Bool :=
    decide (∃ fr ∈ v.citationFrame?, ∃ t, t.IsInterrogative ∧ fr.hasType t)

end Minimalist
