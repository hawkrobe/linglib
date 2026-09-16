import Linglib.Syntax.Reflex
import Linglib.Fragments.Mayan.Params

/-!
# K'iche' extraction marking

The extraction marking of K'iche' (K'ichean Mayan) as reflex cells: transitive-subject
extraction switches the verb to Agent Focus, the voice marker *-n* ([mondloch-2017]), and the
extraction of a low adjunct (locatives, instruments, datives and benefactives, comitatives)
obligatorily adds the fronting particle *wi* to the verbal complex, while clausal adjuncts such
as reasons and temporals never do ([mendes-ranero-2021]); core-object extraction is unmarked.
The distribution of *wi* across clause sizes, and its contrast with Mam =(y)a', is the matter of
`Studies/ElkinsTorrenceBrown2026.lean`.

## References

* [mendes-ranero-2021]
* [mondloch-2017]
* [elkins-torrence-brown-2026]
-/

namespace Kiche.Extraction

/-- The hosts of K'iche' extraction reflexes: the verb stem, and the verbal complex the enclitic
*wi* attaches to. -/
inductive Host where
  | verb
  | verbalComplex
  deriving DecidableEq, Repr

/-- Transitive-subject extraction takes Agent Focus on the verb; low-adjunct extraction adds
*wi* to the verbal complex; everything else is unmarked. -/
def realize : Mayan.ExtractionSite → Finset (Reflex Host)
  | .core .A => {.morpheme .verb}
  | .adjunct .instrument | .adjunct .benefactive | .adjunct .dative | .adjunct .locative =>
      {.morpheme .verbalComplex}
  | _ => ∅

/-- *wi* is licensed by exactly the low adjunct classes. -/
theorem realize_adjunct_nonempty_iff (a : Mayan.Adjunct) :
    (realize (.adjunct a)).Nonempty ↔
      a = .instrument ∨ a = .benefactive ∨ a = .dative ∨ a = .locative := by
  cases a <;> decide

end Kiche.Extraction
