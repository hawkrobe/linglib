import Linglib.Syntax.Clause.Chaining
import Linglib.Fragments.Nungon.Clause
import Linglib.Fragments.Manambu.Clause
import Linglib.Fragments.Korean.Clause
import Linglib.Fragments.Turkish.Clause

/-!
# Sarvasy & Aikhenvald (2025): Clause Chaining in the Languages of the World

This file formalizes the typological generalizations of the volume's introduction over the
clause-chaining systems of four of its languages. A clause chain is a sequence of medial
clauses, formally dependent and underspecified for inflectional categories, closed by one
independent clause, and the introduction surveys the parameters along which chaining varies:
the switch-reference marking of many medial-final languages, the categories medial verbs
retain, the relations medial forms encode, the two bridging constructions and the
non-canonical uses of medial clauses. The systems are those of Nungon and Manambu, whose
chapters describe switch-reference systems, and of Korean and Turkish, which chain without
switch-reference; each is read off its fragment's inventory of medial forms (`nungon`,
`manambu`, `korean`, `turkish`, `sample`). The generalizations proved are that same-subject
medial forms leave the subject unindexed while different-subject forms index it
(`ss_forms_lack_subject_marking`), that Manambu's switch-reference markers each encode a
temporal or logical relation whereas Nungon's mark subject continuity alone, the temporal
relation coming from a switch-reference-neutral construction (`relations_fused_with_sr`),
that the chain's tense comes from the final verb in the two Papuan languages while Korean
admits tense before some medial suffixes (`tense_from_final_verb`), that Korean and Turkish
negate medial clauses individually (`negated_individually`), and that their medial verbs are
converbs (`converb_form`).

## Implementation notes

The Korean and Turkish inventories come from reference grammars rather than the volume,
whose introduction discusses both languages; the volume's Turkish suffix list overlaps but
does not coincide with the grammar's. The switch-reference system, its obligatoriness and
markedness, the agreement, aspect and polarity profiles and the marked relations are derived
from the inventories; tense, mood, the bridging constructions and the stand-alone use are the
chapters' reports about medial clauses as a class, and Nungon's polarity is the earlier file's
value. Ku Waru and Korowai, formerly in the sample, are dropped: the former has no chapter
in the volume and the latter's switch-reference system was misrecorded as tracking several
arguments.

## References

* [sarvasy-aikhenvald-2025]
* [sarvasy-2017]
* [aikhenvald-2025]
* [aikhenvald-2008]
* [sohn-1999]
* [goksel-kerslake-2005]
-/

namespace SarvasyAikhenvald2025

open Clause.Chaining

/-! ### The systems, read off the fragments -/

/-- Whether an inventory of medial forms has switch-reference marking. -/
def srSystemOf {ι : Type*} [Fintype ι] (sr : ι → Option SwitchReference) : SRSystem :=
  if ∃ m, sr m ≠ none then .ssDs else .none

/-- Switch-reference is unmarked on the same-subject side when the same-subject forms leave
the subject unindexed and the different-subject forms index it. -/
def srMarkednessOf {ι : Type*} [Fintype ι] (sr : ι → Option SwitchReference)
    (indexes : ι → Prop) [DecidablePred indexes] : Option SRMarkedness :=
  if (∀ m, sr m = some .ss → ¬ indexes m) ∧ ∀ m, sr m = some .ds → indexes m then
    some .ssUnmarked
  else none

open Nungon.Medial in
/-- Nungon chains medial-final, its medial verbs carrying a switch-reference suffix, the
different-subject forms indexing the subject, and the perfect construction neutral to
switch-reference; tense, mood and aspect come from the final verb. -/
def nungon : System where
  direction := .medialFinal
  srSystem := srSystemOf sr
  srTarget := some .subjectOnly
  srObligatory := decide (∀ m : Nungon.Medial, m.sr ≠ none)
  srMarkedness := srMarkednessOf sr IndexesSubject
  medialMorph :=
    { tense := .absent
      agreement := .ofPred IndexesSubject
      mood := .absent
      polarity := .full
      aspect := .absent }
  relationsMarked := Finset.univ.biUnion relations
  hasRecapLinkage := true
  hasSummaryLinkage := true
  medialCanStandAlone := true

open Manambu.MedialMarker in
/-- Manambu chains medial-final with a same-subject versus different-subject system that two
markers escape, its different-subject markers following subject cross-referencing, relative
tense fused with the marking, no mood, aspect only before the causal marker, and the
unlikely condition clause alone not negatable. -/
def manambu : System where
  direction := .medialFinal
  srSystem := srSystemOf sr
  srTarget := some .subjectOnly
  srObligatory := decide (∀ m : Manambu.MedialMarker, m.sr ≠ none)
  srMarkedness := srMarkednessOf sr IndexesSubject
  medialMorph :=
    { tense := .restricted
      agreement := .ofPred IndexesSubject
      mood := .absent
      polarity := .ofPred Negatable
      aspect := .ofPred fun m : Manambu.MedialMarker ↦ m.inflection = .tensedSubject }
  relationsMarked := Finset.univ.biUnion relations
  hasRecapLinkage := true
  hasSummaryLinkage := true
  medialCanStandAlone := decide (∃ m : Manambu.MedialMarker, m.StandsAlone)

open Korean.Converb in
/-- Korean chains medial-final without switch-reference, tense and polarity retained as the
converbs admit them, no agreement, and medial clauses able to stand alone. -/
def korean : System where
  direction := .medialFinal
  srSystem := .none
  srTarget := none
  srObligatory := false
  srMarkedness := none
  medialMorph :=
    { tense := .ofPred AllowsTense
      agreement := .absent
      mood := .restricted
      polarity := .ofPred AllowsNegation
      aspect := .restricted }
  relationsMarked := Finset.univ.biUnion relations
  hasRecapLinkage := false
  hasSummaryLinkage := false
  medialCanStandAlone := true

open Turkish.Converb in
/-- Turkish chains medial-final without switch-reference, each converb encoding its own
relations, no agreement on the converb, tense and aspect on some converbs, and every converb
negatable. -/
def turkish : System where
  direction := .medialFinal
  srSystem := .none
  srTarget := none
  srObligatory := false
  srMarkedness := none
  medialMorph :=
    { tense := .restricted
      agreement := .absent
      mood := .restricted
      polarity := .ofPred Negatable
      aspect := .restricted }
  relationsMarked := Finset.univ.biUnion relations
  hasRecapLinkage := false
  hasSummaryLinkage := false
  medialCanStandAlone := false

/-- The four systems. -/
def sample : List System := [nungon, manambu, korean, turkish]

/-! ### The generalizations -/

/-- Every sampled language chains medial-final, as verb-final languages do. -/
theorem medial_final : ∀ s ∈ sample, s.direction = .medialFinal := by decide

/-- Same-subject medial forms leave the subject unindexed and different-subject forms index
it: Nungon's same-subject verb is the bare dependent stem with the medial suffix while its
different-subject verb carries a subject desinence, and no Manambu same-subject marker
follows subject cross-referencing while both different-subject markers do, so agreement on
medial verbs is restricted in both. -/
theorem ss_forms_lack_subject_marking :
    nungon.medialMorph.agreement = .restricted ∧ manambu.medialMorph.agreement = .restricted ∧
      (∀ m : Nungon.Medial,
        (m.sr = some .ss → ¬ m.IndexesSubject) ∧ (m.sr = some .ds → m.IndexesSubject)) ∧
      ∀ m : Manambu.MedialMarker,
        (m.sr = some .ss → ¬ m.IndexesSubject) ∧ (m.sr = some .ds → m.IndexesSubject) := by
  decide

/-- Manambu's switch-reference markers each encode a temporal or logical relation, and some
of the relations lie beyond the temporal ones; Nungon's switch-reference forms encode no
relation, and completion before the next event is marked by the perfect, which is neutral to
switch-reference. -/
theorem relations_fused_with_sr :
    (∀ m : Manambu.MedialMarker, m.sr ≠ none → m.relations.Nonempty) ∧
      (∃ r ∈ manambu.relationsMarked, ¬ r.Temporal) ∧
      (∀ m : Nungon.Medial, m.sr ≠ none → m.relations = ∅) ∧
      ∃ m : Nungon.Medial, m.sr = none ∧ m.relations.Nonempty := by
  decide

/-- The chain's tense comes from the final verb in Nungon, whose medial verbs bear no tense,
and Manambu's medial tense is relative; Korean admits tense before some but not all of its
medial suffixes. -/
theorem tense_from_final_verb :
    nungon.tenseFromFinalVerb = true ∧ manambu.medialMorph.tense = .restricted ∧
      korean.medialMorph.tense = .restricted := by
  decide

/-- Korean and Turkish negate medial clauses individually, since every Korean suffix admits
negation and every Turkish converb has a negative form or is negative itself. -/
theorem negated_individually :
    korean.medialMorph.polarity = .full ∧ turkish.medialMorph.polarity = .full := by
  decide

/-- The medial verbs of the languages without switch-reference are converbs, as their
fragments record them. -/
theorem converb_form :
    korean.medialVerbForm = .Conv ∧ turkish.medialVerbForm = .Conv ∧
      (∀ c : Korean.Converb, c.verbForm = korean.medialVerbForm) ∧
      ∀ c : Turkish.Converb, c.verbForm = turkish.medialVerbForm := by
  decide

/-- Switch-reference goes with the Papuan systems of the sample and its absence with the
converbal ones, and the systems with switch-reference are the ones whose medial verbs lose
tense or reduce it to relative tense. -/
theorem sr_and_tense :
    ∀ s ∈ sample, s.hasSR = true → s.medialMorph.tense ≠ .full := by
  decide

end SarvasyAikhenvald2025
