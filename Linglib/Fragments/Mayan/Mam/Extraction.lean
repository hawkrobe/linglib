import Linglib.Syntax.Reflex
import Linglib.Fragments.Mayan.Extraction

/-!
# Mam extraction marking

Mam (Mamean Mayan) has no Agent Focus form. In every dialect but possibly two, a transitive
subject is extracted by putting the verb in the antipassive *-n*, so that the argument extracted
is an absolutive one; the antipassive is the Mam response to the Mayan ban on extracting an
ergative argument. San Juan Ostuncalco Mam further marks the extraction of a non-core argument
or adjunct with the movement enclitic =(y)a', which may attach to the verbal complex and to a
directional auxiliary when the clause has one, each optionally. Instruments, benefactives,
datives, locatives, reasons, purposes and manners license the enclitic; temporals do not, and
absolutive extraction is unmarked. England describes the enclitic and the dialects' voices, and
Elkins, Brown and Torrence the distribution of the enclitic within and across clauses.

## Main declarations

* `Mam.Extraction.realize`: the reflexes extraction from each `Mayan.ExtractionSite` licenses.

## Main results

* `Mam.Extraction.morpheme_verb_mem_realize_iff`: the antipassive is the reflex of
  transitive-subject extraction alone.
* `Mam.Extraction.morpheme_verbalComplex_notMem_realize_core`: no core-argument extraction
  licenses the enclitic.
* `Mam.Extraction.morpheme_directional_mem_realize_iff`: the directional hosts the enclitic at
  exactly the sites the verbal complex does.

## Implementation notes

The antipassive is `Mam.antipassive` of `Voice.lean`; the enclitic's distribution across clause
sizes and movement paths is formalized in `Studies/ElkinsTorrenceBrown2026.lean`.

## References

* [aissen-2017b]
* [elkins-torrence-brown-2026]
* [england-1989]
* [england-2017]
-/

namespace Mam.Extraction

/-- The hosts of Mam extraction reflexes: the verb stem, which the antipassive suffix alters;
the verbal complex, the word the enclitic =(y)a' closes after the stem's suffixes; and a
directional auxiliary. -/
inductive Host where
  | verb
  | verbalComplex
  | directional
  deriving DecidableEq, Repr

/-- Transitive-subject extraction antipassivizes the verb; extraction of an adjunct of any class
but the temporals licenses =(y)a' on the verbal complex and on a directional, each optional and
independent of the other; absolutive and temporal extraction are unmarked. -/
def realize : Mayan.ExtractionSite → Finset (Reflex Host)
  | .core .A => {.morpheme .verb}
  | .adjunct .temporal => ∅
  | .adjunct _ => {.morpheme .verbalComplex, .morpheme .directional}
  | _ => ∅

@[simp] theorem realize_core_A : realize (.core .A) = {.morpheme .verb} := rfl

@[simp] theorem realize_adjunct_temporal : realize (.adjunct .temporal) = ∅ := rfl

/-- Absolutive extraction is unmarked. -/
theorem realize_core_of_ne_A {r : ArgumentRole} (h : r ≠ .A) : realize (.core r) = ∅ := by
  cases r <;> first | exact absurd rfl h | rfl

theorem realize_adjunct_of_ne_temporal {a : Mayan.Adjunct} (h : a ≠ .temporal) :
    realize (.adjunct a) = {.morpheme .verbalComplex, .morpheme .directional} := by
  cases a <;> first | exact absurd rfl h | rfl

/-- The temporals are the one adjunct class whose extraction licenses no reflex. -/
theorem realize_adjunct_nonempty_iff (a : Mayan.Adjunct) :
    (realize (.adjunct a)).Nonempty ↔ a ≠ .temporal := by
  cases a <;> decide

/-- The antipassive is the reflex of transitive-subject extraction alone. -/
theorem morpheme_verb_mem_realize_iff (s : Mayan.ExtractionSite) :
    Reflex.morpheme Host.verb ∈ realize s ↔ s = .core .A := by
  cases s with
  | core r => cases r <;> decide
  | adjunct a => cases a <;> decide

/-- No core-argument extraction licenses the enclitic. -/
theorem morpheme_verbalComplex_notMem_realize_core (r : ArgumentRole) :
    Reflex.morpheme Host.verbalComplex ∉ realize (.core r) := by
  cases r <;> decide

/-- Multiple exponence: the directional hosts the enclitic at exactly the sites the verbal
complex does. -/
theorem morpheme_directional_mem_realize_iff (s : Mayan.ExtractionSite) :
    Reflex.morpheme Host.directional ∈ realize s ↔
      Reflex.morpheme Host.verbalComplex ∈ realize s := by
  cases s with
  | core r => cases r <;> decide
  | adjunct a => cases a <;> decide

end Mam.Extraction
