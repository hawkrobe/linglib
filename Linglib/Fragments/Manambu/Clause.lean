import Mathlib.Data.Finset.Union
import Linglib.Morphology.Morph
import Linglib.Syntax.Clause.Chaining

/-!
# Manambu medial clauses

Manambu (Ndu family, East Sepik Province, Papua New Guinea) chains dependent medial clauses
before a single main clause and marks the predicate of each medial clause with one of nine
suffixes, most of them sensitive to switch-reference. The completive pair *-ku* (same
subject) and *-k* (different subject) means 'after' and is read as reason as well, and a *-k*
clause also as a real condition; *-ta:y* 'while' is cotemporaneous and *-taka* marks immediate
sequence, both with a same-subject form only; *-kǝb* 'as soon as', with a possible short
temporal overlap, takes a different subject, and *-ta:y-kǝb*, the one bimorphemic marker,
the same subject, its action starting before that of the following clause and overlapping with
it; *-ga:y* 'if' marks an unlikely condition with a same-subject form. Two markers are not
sensitive to switch-reference: *-lǝk* 'because', which grammaticalized from the dative of the
distal demonstrative, and the versatile *-n*, read as simultaneous, preceding or concomitant
action or manner and offered by speakers as the citation form of a verb. The verb before
*-ku*, *-ta:y*, *-taka*, *-ta:y-kǝb*, *-ga:y* and *-n* is uninflected; before *-k* and *-kǝb*
it carries the non-tensed subject cross-referencing markers, and before *-lǝk* the tensed ones
of a main clause, so that a causal clause alone may carry habitual aspect and action focus.
After a light CV root *-taka* and *-kǝb* appear as *-tataka* and *-kǝkǝb*. Medial clauses
express relative tense through their markers and neither mood nor imperative, and are
negated with the dependent-clause negator *-ma:r-*, except that a *-ga:y* clause cannot be
negated and instead repeats its verb in the next clause. The *-n*, *-ta:y* and *-kǝb* forms
can head the predicate of a verbless clause, and all markers but *-ta:y-kǝb*, *-lǝk* and
*-ga:y* combine with the completive auxiliary *napa-*. The same-subject completive clause
and the *-n* clause occur on their own, as stern commands and, in conversation, with a
resultative sense. Chains are bridged by recapitulative linkage, which repeats the last verb of
the preceding chain, and by summary linkage, a same-subject completive clause of *tǝ-*
'stay' summing up the preceding clauses.

## Main definitions

* `Manambu.MedialInflection` — the inflection the medial verb carries before its marker:
  none, non-tensed subject cross-referencing, or the tensed cross-referencing of a main
  clause
* `Manambu.MedialMarker` — the nine markers, with their morphs (`morphs`, `form`), the
  switch-reference value they carry (`sr`), the relations they encode (`relations`), the
  inflection of the verb (`inflection`, `IndexesSubject`), which make them an instance of
  `Clause.Chaining.MedialForm`, and whether they head a predicate
  (`HeadsPredicate`), are negated (`Negatable`), combine with the completive auxiliary
  (`WithCompletive`) and occur on their own (`StandsAlone`)
* `Manambu.dependentNegator`, `Manambu.completive` — the negator of dependent clauses
  and the completive auxiliary

## Implementation notes

The clause-chaining typology over these forms is in `Studies/SarvasyAikhenvald2025.lean`.

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
