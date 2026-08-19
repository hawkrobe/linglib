import Linglib.Syntax.Category.Verb.Defs
import Linglib.Syntax.Reciprocal

/-!
# Reciprocal verb entries

A reciprocal verb expresses mutual action without a reciprocal anaphor —
intransitive *kiss*, Hebrew *hitnašek*, French *s'embrasser*. An entry
records the verb, the locus where reciprocalization formed it
([reinhart-siloni-2005]'s lex-syn parameter; [siloni-2008], [siloni-2012]),
and its transitive alternate when the vocabulary has one — frozen entries
(Hebrew *hitgošeš* 'wrestle') lack one. The subject profile bundled from
the base's grid is the join of the base's two entailment profiles,
[reinhart-siloni-2005]'s `[θᵢ · θⱼ]` role bundling.
-/

open ArgumentStructure

/-- A reciprocal verb entry: the intransitive verb, its formation locus,
    and its transitive alternate when one exists in the vocabulary. -/
structure Verb.Reciprocal where
  verb : Verb
  /-- Where reciprocalization applied (the lex-syn parameter). -/
  formation : _root_.Reciprocal.Formation
  /-- The transitive alternate; `none` for frozen entries. -/
  base : Option Verb := none
  deriving Repr, BEq

namespace Verb.Reciprocal

/-- A frozen entry has no transitive alternate in the vocabulary. -/
def IsFrozen (v : Verb.Reciprocal) : Prop := v.base = none

instance : DecidablePred IsFrozen := fun v =>
  decidable_of_iff (v.base.isNone = true) Option.isNone_iff_eq_none

/-- The subject profile bundled from the base's grid: the join of the
    base's subject and object entailments; `none` when the entry is frozen
    or the base's grid is unannotated. -/
def bundledSubjectProfile (v : Verb.Reciprocal) : Option EntailmentProfile := do
  let b ← v.base
  return (← b.subjectEntailments) ⊔ (← b.objectEntailments)

theorem bundledSubjectProfile_eq {v : Verb.Reciprocal} {b : Verb}
    {ps po : EntailmentProfile} (hb : v.base = some b)
    (hs : b.subjectEntailments = some ps)
    (ho : b.objectEntailments = some po) :
    v.bundledSubjectProfile = some (ps ⊔ po) := by
  simp [bundledSubjectProfile, hb, hs, ho]

/-- The bundled subject role of an entry whose base has an agentive
    subject and an affected object is a complex role. -/
theorem bundledSubjectProfile_isComplexRole {v : Verb.Reciprocal} {b : Verb}
    {ps po : EntailmentProfile} (hb : v.base = some b)
    (hs : b.subjectEntailments = some ps)
    (ho : b.objectEntailments = some po)
    (ha : 0 < ps.pAgentScore) (hp : 0 < po.pPatientScore) :
    ∃ prof, v.bundledSubjectProfile = some prof ∧
      EntailmentProfile.IsComplexRole prof :=
  ⟨ps ⊔ po, bundledSubjectProfile_eq hb hs ho,
    EntailmentProfile.isComplexRole_sup ha hp⟩

end Verb.Reciprocal
