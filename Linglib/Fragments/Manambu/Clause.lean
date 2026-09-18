import Mathlib.Data.Finset.Union
import Linglib.Morphology.Morph
import Linglib.Syntax.Clause.Chaining

/-!
# Manambu medial clauses

Manambu (Ndu, East Sepik Province, Papua New Guinea) chains medial clauses before a single
main clause and marks the medial predicate with one of nine suffixes. Six are sensitive to
switch-reference: the completive pair *-ku* (same subject) and *-k* (different subject)
'after', *-ta:y* 'while' and *-taka* 'as soon as' with same-subject forms only, and *-kǝb*
(different subject) and *-ta:y-kǝb* (same subject) for a brief temporal overlap; *-ga:y* 'if'
marks an unlikely condition with the same subject, and *-lǝk* 'because' and the versatile *-n*
are neutral. The verb is bare before the same-subject markers and *-n*, carries subject
cross-referencing before *-k* and *-kǝb*, and the tensed cross-referencing of a main clause
before *-lǝk*. Medial clauses are negated with *-ma:r-*, except after *-ga:y*, and the
same-subject completive and *-n* clauses occur on their own.

## Implementation notes

* The clause-chaining typology over the markers is in `Studies/SarvasyAikhenvald2025.lean`.

## References

* [aikhenvald-2008]
* [aikhenvald-2025]
-/

namespace Manambu

open Clause.Chaining (InterclauseRelation SwitchReference)
open Morphology (Morph)

/-- The inflection a medial verb carries before its marker. -/
inductive MedialInflection where
  /-- The bare stem. -/
  | uninflected
  /-- The non-tensed subject cross-referencing markers of a dependent verb. -/
  | subject
  /-- The tensed subject cross-referencing of a main-clause verb. -/
  | tensedSubject
  deriving DecidableEq, Repr, Fintype

/-- The markers of medial clauses, suffixes on the medial predicate. -/
inductive MedialMarker where
  /-- *-ku*, the same-subject completive 'after', also read as reason. -/
  | ku
  /-- *-k*, the different-subject completive 'after', also read as reason or real condition. -/
  | k
  /-- *-ta:y* 'while', cotemporaneous 'before, during and after', same subject only. -/
  | tay
  /-- *-taka* 'as soon as', immediate sequence, same subject only; *-tataka* after a light
  root. -/
  | taka
  /-- *-kǝb* 'as soon as', immediate sequence with a possible short overlap, different subject;
  *-kǝkǝb* after a light root. -/
  | keb
  /-- *-ta:y-kǝb*, an action started before the following clause's and overlapping with it,
  same subject. -/
  | taykeb
  /-- *-lǝk* 'because', not sensitive to switch-reference. -/
  | lek
  /-- *-ga:y* 'if', an unlikely condition, same subject. -/
  | gay
  /-- *-n*, simultaneous, preceding or concomitant action or manner, not sensitive to
  switch-reference. -/
  | n
  deriving DecidableEq, Repr, Fintype

namespace MedialMarker

/-- The morphs of a marker. -/
def morphs : MedialMarker → List Morph
  | ku => [.suff "ku"]
  | k => [.suff "k"]
  | tay => [.suff "ta:y"]
  | taka => [.suff "taka"]
  | keb => [.suff "kǝb"]
  | taykeb => [.suff "ta:y", .suff "kǝb"]
  | lek => [.suff "lǝk"]
  | gay => [.suff "ga:y"]
  | n => [.suff "n"]

/-- The form of a marker in boundary notation. -/
def form (m : MedialMarker) : String := Morph.surface m.morphs

/-- The switch-reference value a marker carries; `none` for *-lǝk* and *-n*. -/
def sr : MedialMarker → Option SwitchReference
  | ku | tay | taka | taykeb | gay => some .ss
  | k | keb => some .ds
  | lek | n => none

/-- The interclausal relations a marker encodes. -/
def relations : MedialMarker → Finset InterclauseRelation
  | ku => {.sequential, .causal}
  | k => {.sequential, .causal, .conditional}
  | tay | taykeb => {.simultaneous}
  | taka => {.sequential}
  | keb => {.sequential, .simultaneous}
  | lek => {.causal}
  | gay => {.conditional}
  | n => {.sequential, .simultaneous, .manner}

/-- The inflection of the verb before the marker. -/
def inflection : MedialMarker → MedialInflection
  | ku | tay | taka | taykeb | gay | n => .uninflected
  | k | keb => .subject
  | lek => .tensedSubject

/-- The verb before the marker cross-references its subject. -/
def IndexesSubject (m : MedialMarker) : Prop := m.inflection ≠ .uninflected

instance : DecidablePred IndexesSubject := fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- The marked verb can head the predicate of a verbless clause. -/
def HeadsPredicate (m : MedialMarker) : Prop := m = n ∨ m = tay ∨ m = keb

instance : DecidablePred HeadsPredicate := fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The medial clause can be negated. -/
def Negatable (m : MedialMarker) : Prop := m ≠ gay

instance : DecidablePred Negatable := fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- The marker combines with the completive auxiliary *napa-*. -/
def WithCompletive (m : MedialMarker) : Prop := m ≠ taykeb ∧ m ≠ lek ∧ m ≠ gay

instance : DecidablePred WithCompletive := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A medial clause with the marker occurs on its own, as a command or with a resultative
sense. -/
def StandsAlone (m : MedialMarker) : Prop := m = ku ∨ m = n

instance : DecidablePred StandsAlone := fun _ => inferInstanceAs (Decidable (_ ∨ _))

instance : Clause.Chaining.MedialForm MedialMarker where
  sr := sr
  relations := relations
  IndexesSubject := IndexesSubject

end MedialMarker

/-- *-ma:r-*, the negator of dependent clauses. -/
def dependentNegator : Morph := .suff "ma:r"

/-- *napa-*, the completive auxiliary of medial clauses. -/
def completive : Morph := .root "napa"

end Manambu
