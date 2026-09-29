module

public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
public import Linglib.Data.Examples.Sorace2000

/-!
# Sorace (2000): Gradients in auxiliary selection with intransitive verbs

[sorace-2000] argues that the perfect auxiliary of a monadic intransitive verb in Italian, French,
Dutch and German depends on the verb's place on the Auxiliary Selection Hierarchy
(`AuxiliarySelectionHierarchy`, Table 1): the transitions and states, ordered by decreasing
telicity, followed by the processes, ordered by increasing control. Verbs of telic change of
location take *be* and verbs of controlled nonmotional process take *have*, categorically, in every
language and whatever the rest of the sentence contributes; these core types are the two ends of
the hierarchy. The types between them allow both auxiliaries, to a degree that depends on their
position, and respond to the telicity of the predicate and the agentivity of the subject. Each
language draws a cutoff point on the hierarchy between the verbs that take *be* and those that
take *have*, and the cutoff moves from language to language without reaching the core (§6).

The data are the paper's examples, one row per sentence with the judgment of each auxiliary it
prints. The theorems are the generalizations the paper draws from them: the rigid core
(`changeOfLocation_selects_be`, `nonmotionalProcess_selects_have`), variation confined to the
types between (`free_alternation_iff`), the cutoff point of each language (`italian_cutoff`,
`french_cutoff`, `dutch_cutoff`, `cutoff_varies`), and the sensitivity of verbs of motion to a
directional phrase (`directional_motionalProcess`, `italian_directional_split`). Italian cuts at
the seam of the two halves of the hierarchy, where the states end and the processes begin.

The German examples cross (`german_crossing`): *halten* 'last', a verb of continuation of a
state, takes *haben* and rejects *sein* (17a), while *rennen*, *laufen* and *schwimmen*,
controlled motional processes further down the hierarchy, take *sein* and reject *haben* under a
durative adverbial (38). So no cutoff point separates the German verbs at the granularity of
Table 1 (`german_no_cutoff`). The paper reports the German motion verbs (§4.3) and allows a
language to merge types or to divide them more finely (fn. 17, §6); a German cutoff needs the
types from continuation of a state to motional process merged into one.

## Implementation notes

* A row's verb type is the type of the section its example illustrates; (36), from §4.2's
  controlled affecting processes, a subclass of the controlled processes, is a nonmotional
  process.
* The diacritics are read on the `Judgment` scale: unmarked is acceptable, `?` marginal, `??`
  questionable, `?*` and `*?` unacceptable, `*` ungrammatical. The paper's `?*` lies between `??`
  and `*`, which is where `unacceptable` sits, although the scale glosses that value as a
  pragmatic failure.
* A sentence prefers one auxiliary when the paper prints it with both and judges one better;
  fn. 3 measures the strength of a preference by the distance between the two. The cutoffs of
  French and Dutch rest on this: counting a sentence printed with one auxiliary as a choice would
  add crossings, French *rougir* 'blush' with *avoir* (13) below *rester* 'remain' with *être*
  (19a), Dutch *duren* 'last' with *hebben* (18b) below *blijken* 'seem' with *zijn* (24c).
* A row records the departures from the default of its type that the paper points to: a
  directional or bounding phrase that makes the predicate telic ((35), (39b), (40b), (41b), (41d),
  (42b), (49), (51)), a durative adverbial that makes it atelic ((4), (11)), an agentive subject
  ((5a), (15c), (45b), (46b)), or a nonagentive one ((34), (36b), (43), (44b)). The cutoff point is
  tested on the rows without one.
* Omitted examples: (2) and (3), frozen *be* in Romanian and English, which have no choice of
  auxiliary; §3.5's anticausatives, dyadic and off the hierarchy, except (30a), the one
  change-of-location verb printed with *have*; and (14b), the sense 'be elusive' of *échapper*,
  which the paper places on no type.
* §5's discussion of the projectionist and constructional models of the lexicon-syntax interface
  is argument, not formalized here.

## References

* [sorace-2000]
-/

@[expose] public section

namespace Sorace2000

open ArgumentStructure Data.Examples

/-- The four languages of the paper. -/
inductive Language
  | italian | french | dutch | german
  deriving DecidableEq, Repr

/-- A phrase that changes the telicity of the predicate: a directional or bounding phrase makes it
telic, a durative adverbial atelic. -/
inductive PredicateShift
  | telicized | detelicized
  deriving DecidableEq, Repr

/-- A subject whose agentivity departs from the default of the verb's type. -/
inductive SubjectShift
  | agentive | nonagentive
  deriving DecidableEq, Repr

/-- An example sentence: its language, the type of its verb, the departures from the default of
the type, and the judgment of the sentence with each auxiliary the paper prints. -/
structure Row where
  language : Language
  position : AuxiliarySelectionHierarchy
  predicate : Option PredicateShift
  subject : Option SubjectShift
  judgment : PerfectAux → Option Judgment

/-- The row of an example, from its language, its `position`, `aux`, `predicate` and `subject`
features, and its alternative with the other auxiliary. -/
def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let language ← [("ital1282", Language.italian), ("stan1290", .french), ("dutc1256", .dutch),
    ("stan1295", .german)].lookup ex.language
  let position ← ex.parse? "position"
    [("changeOfLocation", AuxiliarySelectionHierarchy.changeOfLocation),
    ("changeOfState", .changeOfState), ("continuationOfState", .continuationOfState),
    ("existenceOfState", .existenceOfState), ("uncontrolledProcess", .uncontrolledProcess),
    ("motionalProcess", .motionalProcess), ("nonmotionalProcess", .nonmotionalProcess)]
  let aux ← ex.parse? "aux" [("be", PerfectAux.be), ("have", .have)]
  pure
    { language, position
      predicate := ex.parse? "predicate"
        [("telicized", PredicateShift.telicized), ("detelicized", .detelicized)]
      subject := ex.parse? "subject" [("agentive", SubjectShift.agentive),
        ("nonagentive", .nonagentive)]
      judgment := fun a ↦
        if a = aux then some ex.judgment else ex.alternatives.head?.map (·.2) }

/-- The paper's examples. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

example : rows.length = Examples.all.length := by decide

/-- The sentence of a row is judged better with auxiliary `a` than with `b`. -/
def Row.Prefers (r : Row) (a b : PerfectAux) : Prop :=
  ∃ j k, r.judgment a = some j ∧ r.judgment b = some k ∧ k < j

instance (r : Row) (a b : PerfectAux) : Decidable (r.Prefers a b) :=
  inferInstanceAs (Decidable (∃ _ _, _))

/-! ### The core -/

/-- §3.1, (1), (4), (5), (30a): a verb of change of location takes *be* and rejects *have* in all
four languages, with an atelic predicate (4) and with an agentive or a nonagentive subject (5). -/
theorem changeOfLocation_selects_be : ∀ r ∈ rows, r.position = .changeOfLocation →
    (∀ j ∈ r.judgment .be, j = .acceptable) ∧ ∀ j ∈ r.judgment .have, j = .ungrammatical := by
  decide

/-- §4.1, (33)–(36): a verb of controlled nonmotional process takes *have* in all four languages,
also when an adverbial bounds the event (35); *be* is at best marginal, with a nonagentive
subject ((34), (36b)). -/
theorem nonmotionalProcess_selects_have : ∀ r ∈ rows, r.position = .nonmotionalProcess →
    (∀ j ∈ r.judgment .have, j = .acceptable) ∧ ∀ j ∈ r.judgment .be, j ≤ .marginal := by
  decide

/-- §§2, 6: some verb of a type takes both auxiliaries acceptably exactly when the type is not at
either end of the hierarchy. -/
theorem free_alternation_iff (t : AuxiliarySelectionHierarchy) :
    (∃ r ∈ rows, r.position = t ∧ r.judgment .be = some .acceptable ∧
      r.judgment .have = some .acceptable) ↔ t ≠ ⊥ ∧ t ≠ ⊤ := by
  revert t; decide

/-! ### The cutoff point -/

section Cutoff

variable {l : Language} {k : AuxiliarySelectionHierarchy}

/-- The rows of a language without a departure from the default of their type. -/
def baseRows (l : Language) : List Row :=
  rows.filter fun r ↦ r.language = l ∧ r.predicate = none ∧ r.subject = none

/-- A cutoff point for a language at type `k` (§6): each of its sentences that prefers *be* has a
verb of type at most `k`, and each that prefers *have* a verb of type at least `k`. Verbs of type
`k` itself may go either way, as when a language divides a type more finely. -/
def Cutoff (l : Language) (k : AuxiliarySelectionHierarchy) : Prop :=
  ∀ r ∈ baseRows l, (r.Prefers .be .have → r.position ≤ k) ∧ (r.Prefers .have .be → k ≤ r.position)

instance : Decidable (Cutoff l k) := inferInstanceAs (Decidable (∀ r ∈ baseRows l, _))

/-- Under a cutoff point, a sentence preferring *be* has a verb no lower on the hierarchy than a
sentence preferring *have*. -/
theorem Cutoff.le_of_prefers (h : Cutoff l k) {r s : Row} (hr : r ∈ baseRows l)
    (hs : s ∈ baseRows l) (hbe : r.Prefers .be .have) (hhave : s.Prefers .have .be) :
    r.position ≤ s.position :=
  ((h r hr).1 hbe).trans ((h s hs).2 hhave)

/-- (7), (15), (20) against (37), (41), (44)–(47), (50): Italian cuts at the seam of the
hierarchy, after the last of the states or before the first of the processes. -/
theorem italian_cutoff : Cutoff .italian k ↔ k = .existenceOfState ∨ k = .uncontrolledProcess := by
  revert k; decide

/-- (12), (16), (19a), (22), (37c), (42a): French cuts within the continuation of a state, where
*rester* 'remain' takes *être* (19a) and *survivre* 'survive' *avoir* (16). -/
theorem french_cutoff : Cutoff .french k ↔ k = .continuationOfState := by
  revert k; decide

/-- (10a), (18b), (19b), (37b), (39a): Dutch also cuts within the continuation of a state, where
*blijven* 'remain' takes *zijn* (19b) and *duren* 'last' *hebben* (18b). -/
theorem dutch_cutoff : Cutoff .dutch k ↔ k = .continuationOfState := by
  revert k; decide

/-- §6: "The cutoff point cannot be identical in all languages." -/
theorem cutoff_varies : Cutoff .italian k → ¬ Cutoff .french k := by
  rw [italian_cutoff, french_cutoff]
  rintro (rfl | rfl) <;> decide

/-- (17a), (38): a German verb of motion that prefers *sein* sits below a verb of continuation of
a state that prefers *haben*. -/
theorem german_crossing : ∃ r ∈ baseRows .german, ∃ s ∈ baseRows .german,
    r.Prefers .be .have ∧ s.Prefers .have .be ∧ s.position < r.position := by
  decide

/-- No cutoff point separates the German verbs at the granularity of Table 1. -/
theorem german_no_cutoff : ¬ Cutoff .german k := fun h ↦
  let ⟨_, hr, _, hs, hbe, hhave, hlt⟩ := german_crossing
  (h.le_of_prefers hr hs hbe hhave).not_gt hlt

end Cutoff

/-! ### Directional phrases -/

/-- §4.3, (39)–(42): a directional phrase makes Dutch and German verbs of motion prefer *be*
((39b), (40b)), where without one they prefer *have* ((39a), (40a)); in French the auxiliary
stays *avoir* (42b). -/
theorem directional_motionalProcess : ∀ r ∈ rows, r.position = .motionalProcess →
    r.predicate = some .telicized →
    (r.language = .dutch ∨ r.language = .german → r.Prefers .be .have) ∧
      (r.language = .french → r.Prefers .have .be) := by
  decide

/-- §4.3, (41b), (41d): in Italian a directional phrase moves *correre* 'run' to *essere* but leaves
*nuotare* 'swim' with *avere*. -/
theorem italian_directional_split :
    (∃ r ∈ rows, r.language = .italian ∧ r.position = .motionalProcess ∧
      r.predicate = some .telicized ∧ r.Prefers .be .have) ∧
    ∃ r ∈ rows, r.language = .italian ∧ r.position = .motionalProcess ∧
      r.predicate = some .telicized ∧ r.Prefers .have .be := by
  decide

end Sorace2000
