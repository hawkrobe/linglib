import Linglib.Syntax.Clause.Chaining
import Linglib.Fragments.Nungon.MedialVerbs
import Linglib.Fragments.Manambu.MedialVerbs
import Linglib.Fragments.Korean.MedialVerbs
import Linglib.Fragments.Turkish.MedialVerbs

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
switch-reference; each is read off its fragment's inventory of medial forms
(`Clause.Chaining.System`, `sample`). The generalizations proved are that same-subject
medial forms leave the subject unindexed while different-subject forms index it
(`ss_forms_lack_subject_marking`), that Nungon's switch-reference morphology itself encodes the
temporal relations whereas Manambu's markers add relations beyond them
(`temporal_via_sr`), that the chain's tense comes from the final verb in the two Papuan
languages while Korean admits tense before some medial suffixes (`tense_from_final_verb`),
that Korean and Turkish negate medial clauses individually (`negated_individually`), and
that their medial verbs are converbs (`converb_form`).

## Implementation notes

The Korean and Turkish inventories come from reference grammars rather than the volume,
whose introduction discusses both languages; the volume's Turkish suffix list overlaps but
does not coincide with the grammar's. Ku Waru and Korowai, formerly in the sample, are
dropped: the former has no chapter in the volume and the latter's switch-reference system was
misrecorded as tracking several arguments. The bridging and stand-alone fields are the
chapters' reports and are not derived from the inventories.

## References

* [sarvasy-aikhenvald-2025]
* [sarvasy-2017]
* [aikhenvald-2008]
* [sohn-1999]
* [goksel-kerslake-2005]
-/

namespace SarvasyAikhenvald2025

open Clause.Chaining

/-- The four systems, from the fragments. -/
def sample : List System :=
  [Nungon.MedialVerbs.chaining, Manambu.MedialVerbs.chaining, Korean.MedialVerbs.chaining,
    Turkish.MedialVerbs.chaining]

/-- Every sampled language chains medial-final, as verb-final languages do. -/
theorem medial_final : ∀ s ∈ sample, s.direction = .medialFinal := by decide

/-- Same-subject medial forms leave the subject unindexed and different-subject forms index
it: Nungon's two same-subject suffixes are invariant while its different-subject paradigm
indexes person and number, and no Manambu same-subject marker carries subject marking while
every different-subject marker does, so agreement on medial verbs is restricted in both. -/
theorem ss_forms_lack_subject_marking :
    Nungon.MedialVerbs.chaining.medialMorph.agreement = .restricted ∧
      Manambu.MedialVerbs.chaining.medialMorph.agreement = .restricted ∧
      ∀ m ∈ Manambu.MedialVerbs.allMarkers,
        (m.sr = .ss → m.hasSubjectMarking = false) ∧ (m.sr = .ds → m.hasSubjectMarking = true) := by
  decide

/-- Nungon's switch-reference suffixes encode the temporal relations themselves, so the
relations it marks are exactly sequence and simultaneity; Manambu's markers encode relations
beyond the temporal ones. -/
theorem temporal_via_sr :
    Nungon.MedialVerbs.chaining.temporalViaSR = true ∧
      (∀ r ∈ Nungon.MedialVerbs.chaining.relationsMarked, r.Temporal) ∧
      ∃ r ∈ Manambu.MedialVerbs.chaining.relationsMarked, ¬ r.Temporal := by
  decide

/-- The chain's tense comes from the final verb in Nungon, whose medial verbs bear no tense,
and Manambu's medial tense is relative; Korean admits tense before some but not all of its
medial suffixes. -/
theorem tense_from_final_verb :
    Nungon.MedialVerbs.chaining.tenseFromFinalVerb = true ∧
      Manambu.MedialVerbs.chaining.medialMorph.tense = .restricted ∧
      Korean.MedialVerbs.chaining.medialMorph.tense = .restricted := by
  decide

/-- Korean and Turkish negate medial clauses individually: every Korean suffix admits negation
and every Turkish converb has a negative form or is negative itself. -/
theorem negated_individually :
    Korean.MedialVerbs.chaining.medialMorph.polarity = .full ∧
      Turkish.MedialVerbs.chaining.medialMorph.polarity = .full := by
  decide

/-- The medial verbs of the languages without switch-reference are converbs. -/
theorem converb_form :
    Korean.MedialVerbs.chaining.medialVerbForm = .Conv ∧
      Turkish.MedialVerbs.chaining.medialVerbForm = .Conv := by
  decide

/-- Switch-reference goes with the Papuan systems of the sample and its absence with the
converbal ones, and the systems with switch-reference are the ones whose medial verbs lose
tense or reduce it to relative tense. -/
theorem sr_and_tense :
    ∀ s ∈ sample, s.hasSR = true → s.medialMorph.tense ≠ .full := by
  decide

end SarvasyAikhenvald2025
