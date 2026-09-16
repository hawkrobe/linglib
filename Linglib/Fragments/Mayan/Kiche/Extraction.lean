import Linglib.Syntax.Reflex
import Linglib.Syntax.Clause.Relative

/-!
# K'iche' extraction marking

The extraction marking of K'iche' (K'ichean Mayan) as reflex cells: subject extraction switches
the verb to Agent Focus, the voice marker *-n* ([mondloch-2017]), and the extraction of a low
adjunct adds the fronting particle *wi* to the verbal complex ([mendes-ranero-2021]); core-object
extraction is unmarked. The distribution of *wi* across adjunct types and clause sizes, and its
contrast with Mam =(y)a', is the matter of `Studies/ElkinsTorrenceBrown2026.lean`.

## References

* [mendes-ranero-2021]
* [mondloch-2017]
* [elkins-torrence-brown-2026]
-/

namespace Kiche.Extraction

/-- Reflex host of K'iche' extraction marking: the verbal complex. -/
inductive Site
  | verb
  deriving DecidableEq, Repr

/-- The two marked cells: subject extraction takes Agent Focus, oblique extraction adds *wi*;
core-object extraction is unmarked. -/
def realize : RelativeClause.Position → Finset (Reflex Site)
  | .subject => {.morpheme .verb}
  | .oblique => {.morpheme .verb}
  | _ => ∅

theorem marks_oblique : (realize .oblique).Nonempty := Finset.singleton_nonempty _

end Kiche.Extraction
