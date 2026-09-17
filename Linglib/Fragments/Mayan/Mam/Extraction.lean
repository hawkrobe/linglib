import Linglib.Syntax.Reflex
import Linglib.Fragments.Mayan.Params

/-!
# Mam extraction marking

The extraction marking of San Juan Ostuncalco Mam (Mayan, Western Highlands of Guatemala) as
reflex cells, after [elkins-torrence-brown-2026]: transitive-subject (ergative) extraction
switches the verb to an antipassive, the Mam repair for the Ergative Extraction Constraint
([aissen-2017b]); extraction of a non-core argument or adjunct of every class but the temporals
licenses the movement enclitic =(y)a' ([england-1989]), optionally, on the verbal complex and
on a directional auxiliary when one is present; absolutive extraction is unmarked. The
distribution of the enclitic across clause sizes and movement paths is the matter of
`Studies/ElkinsTorrenceBrown2026.lean`.

## References

* [aissen-2017b]
* [elkins-torrence-brown-2026]
* [england-1989]
-/

namespace Mam.Extraction

/-- The hosts of Mam extraction reflexes: the verb stem, whose antipassive suffix is a stem
alternation; the verbal complex, the word the enclitic =(y)a' attaches to after the stem's
suffixes; and a directional auxiliary. -/
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

/-- The temporals are the one adjunct class whose extraction licenses no reflex. -/
theorem realize_adjunct_nonempty_iff (a : Mayan.Adjunct) :
    (realize (.adjunct a)).Nonempty ↔ a ≠ .temporal := by
  cases a <;> decide

/-- =(y)a' tracks adjuncts, not subjects: no enclitic under transitive-subject extraction. -/
theorem eqya_not_on_subject : Reflex.morpheme Host.verbalComplex ∉ realize (.core .A) := by
  decide

end Mam.Extraction
