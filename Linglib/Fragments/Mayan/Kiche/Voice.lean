import Linglib.Syntax.Voice.Basic

/-!
# K'iche' voice

K'iche' (K'ichean Mayan) conjugates a transitive verb in five voices, which Mondloch's grammar
presents lesson by lesson: the active, with subject, verb and object; the simple passive, which
makes the object the subject of an intransitive conjugation and admits the agent only in the
third person, in a phrase with the relational noun *-umaal* 'by'; the completed passive, which
presents the state of the object resulting from the action; the absolutive antipassive, which
drops the object or expresses it indirectly with *ch-ee* 'to', the verb conjugating as an
intransitive; and the agent-focus antipassive, which keeps subject, verb and object and
emphasizes the agent, and is the form the extraction of a transitive subject takes
(`Extraction.lean`). The markers depend on the class of the verb. A derived transitive verb,
with a polysyllabic vowel-final root, takes *-j*, *-x*, *-taj*, *-n* and *-n*, its two
antipassives syncretic. A radical transitive verb, with a monosyllabic root ending in a
consonant or a glottal stop, takes no suffix in the active and none in the simple passive,
where a root ending in a consonant lengthens its vowel, and *-Vtaj*, *-Vn* and *-Vw*, with a
copy or epenthetic vowel, in the other three. Can Pixabaj's sketch calls the completed passive
the lexical passive and reports the same markers. A sixth voice, the instrumental, survives in
remnants and is not covered.

## Main definitions

* `Kiche.VerbClass` — derived and radical transitive verbs
* `Kiche.active`, `simplePassive`, `completedPassive`, `absolutiveAntipassive`,
  `agentFocus` — the five voices of a verb of either class
* `Kiche.voices` — the inventory of a class

## Main results

* `Kiche.isSymmetrical_iff` — agent focus alone beside the active keeps both core terms core
* `Kiche.not_isTransitive_iff` — the passives and the absolutive antipassive derive an
  intransitive construction
* `Kiche.marker_agentFocus_eq_iff` — the two antipassives share a marker exactly on derived
  verbs

## References

* [can-pixabaj-2017]
* [mondloch-2017]
-/

namespace Kiche

/-- The transitive verb classes: derived, with a polysyllabic vowel-final root, and radical,
with a monosyllabic root ending in a consonant or a glottal stop. -/
inductive VerbClass where
  | derived
  | radical
  deriving DecidableEq, Repr, Fintype

/-- The active: *-j* on a derived verb, no suffix on a radical one. -/
def active : VerbClass → Voice
  | .derived => Voice.active.marked [.suff "j"]
  | .radical => Voice.active

/-- The simple passive: *-x* on a derived verb; a radical verb takes no suffix and conjugates
as an intransitive, a consonant-final root lengthening its vowel. -/
def simplePassive : VerbClass → Voice
  | .derived => Voice.passive.marked [.suff "x"]
  | .radical => Voice.passive

/-- The completed passive, the state of the object: *-taj* on a derived verb, *-Vtaj* on a
radical one. -/
def completedPassive : VerbClass → Voice
  | .derived => Voice.passive.marked [.suff "taj"]
  | .radical => Voice.passive.marked [.suff "Vtaj"]

/-- The absolutive antipassive, the object dropped or indirect with *ch-ee*: *-n* on a derived
verb, *-Vn* on a radical one. -/
def absolutiveAntipassive : VerbClass → Voice
  | .derived => Voice.antipassive.marked [.suff "n"]
  | .radical => Voice.antipassive.marked [.suff "Vn"]

/-- The agent-focus antipassive, subject, verb and object present and the agent emphasized:
*-n* on a derived verb, *-Vw* on a radical one. -/
def agentFocus : VerbClass → Voice
  | .derived => Voice.agentVoice.marked [.suff "n"]
  | .radical => Voice.agentVoice.marked [.suff "Vw"]

/-- The five voices of a verb of a class. -/
def voices (c : VerbClass) : Finset Voice :=
  {active c, simplePassive c, completedPassive c, absolutiveAntipassive c, agentFocus c}

/-- Agent focus is the one voice beside the active that keeps both core terms core
([mondloch-2017]). -/
theorem isSymmetrical_iff (c : VerbClass) :
    ∀ v ∈ voices c, v.IsSymmetrical ↔ v = active c ∨ v = agentFocus c := by
  cases c <;> decide

/-- The passives and the absolutive antipassive derive an intransitive construction, and the
verb conjugates as a simple intransitive ([mondloch-2017]). -/
theorem not_isTransitive_iff (c : VerbClass) :
    ∀ v ∈ voices c, ¬ v.target.IsTransitive ↔
      v = simplePassive c ∨ v = completedPassive c ∨ v = absolutiveAntipassive c := by
  cases c <;> decide

/-- The two antipassives are syncretic on derived verbs, both *-n*, and distinct on radical
ones, *-Vn* against *-Vw* ([mondloch-2017]). -/
theorem marker_agentFocus_eq_iff (c : VerbClass) :
    (agentFocus c).marker = (absolutiveAntipassive c).marker ↔ c = .derived := by
  cases c <;> decide

end Kiche
