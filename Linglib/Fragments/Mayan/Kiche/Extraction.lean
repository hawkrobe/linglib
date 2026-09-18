import Linglib.Syntax.Reflex
import Linglib.Fragments.Mayan.Extraction

/-!
# K'iche' extraction marking

The extraction marking of K'iche' (K'ichean Mayan) as reflex cells: transitive-subject
extraction switches the verb to its Agent Focus form ([mondloch-2017]), and the extraction of a
locative, instrument, dative or benefactive phrase (comitatives too) adds the fronting particle
*wi* to the verbal complex, obligatorily in the varieties [mendes-ranero-2021] describe and
absent or optional in others; reasons, purposes, manners and temporals never license it.
Absolutive extraction is unmarked ([coon-mateo-pedro-preminger-2014]). The benefactive cell
records [elkins-torrence-brown-2026]'s summary of the K'ichean pattern, which they note varies
by variety between datives and benefactives. The distribution of *wi* across clause sizes, and
its contrast with Mam =(y)a', is the matter of `Studies/ElkinsTorrenceBrown2026.lean`.

## References

* [coon-mateo-pedro-preminger-2014]
* [elkins-torrence-brown-2026]
* [mendes-ranero-2021]
* [mondloch-2017]
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
  decide +revert

end Kiche.Extraction
