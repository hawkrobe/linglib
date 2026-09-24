module

public import Linglib.Syntax.Case.Basic

/-!
# Japanese case markers

Japanese marks the relations of a noun phrase with particles after it. Tsujimura separates the
case particles, the nominative *ga*, the accusative *o*, the dative *ni* and the genitive *no*,
from the postpositions, the counterparts of English prepositions, which cannot stand on their
own: *de* 'at', *e* 'to', *to* 'with', *made* 'until' and *kara* 'from'. The nominative and the
accusative, unlike case endings, may be dropped in casual speech, *Tomodati(-ga) kita?* 'Has my
friend come?', and replaced by *mo* 'also' and *sae* 'even'. Two markers are polysemous: *ni*
marks recipients, goals, times and the location of existence, and *de* the location of an
action and its instrument, so *ni* and *de* share the locative and *ni* and *e* the allative.
*Ga* is recorded as the nominative, setting aside the exhaustive-listing reading of Kuroda and
Kuno; *no* is also a nominalizer, *to* a quotative complementizer and *kara* a reason
conjunction, uses outside case marking. Sadakane and Koizumi's four *ni* lexemes refine the
single *ni* entry, the matter of `Studies/SadakaneKoizumi1995.lean`.

## Main definitions

* `Japanese.Case.caseParticles`, `Japanese.Case.postpositions` — Tsujimura's two classes
* `Japanese.Case.droppable` — the markers casual speech drops
* `Japanese.Case.inventory` — the cases the markers realize

## References

* [kuno-1987]
* [kuroda-1972]
* [sadakane-koizumi-1995]
* [tsujimura-2014]
-/

@[expose] public section

namespace Japanese.Case

/-! ### Case particles -/

/-- *ga* が, the nominative. -/
def ga : Case.Marker := { form := "ga", cases := {.nom} }

/-- *o* を, the accusative. -/
def o : Case.Marker := { form := "o", cases := {.acc} }

/-- *no* の, the genitive. -/
def no_ : Case.Marker := { form := "no", cases := {.gen} }

/-- *ni* に: the dative of recipients, the allative of goals, the temporal of times and the
locative of existence. -/
def ni : Case.Marker := { form := "ni", cases := {.dat, .loc, .all, .tem} }

/-! ### Postpositions -/

/-- *de* で: the locative of an action's place and the instrumental. -/
def de : Case.Marker := { form := "de", cases := {.loc, .inst} }

/-- *e* へ, the allative of motion toward. -/
def e : Case.Marker := { form := "e", cases := {.all} }

/-- *to* と, the comitative. -/
def to_ : Case.Marker := { form := "to", cases := {.com} }

/-- *kara* から, the ablative of spatial and temporal sources. -/
def kara : Case.Marker := { form := "kara", cases := {.abl} }

/-- *made* まで, the terminative of spatial and temporal endpoints. -/
def made : Case.Marker := { form := "made", cases := {.ter} }

/-- *yori* より 'than', the standard marker of the comparative, recorded as an ablative with the
separative comparative (`Japanese.Comparison.yori`). -/
def yori : Case.Marker := { form := "yori", cases := {.abl} }

/-! ### Tsujimura's classes and the inventory -/

/-- The case particles. -/
def caseParticles : Finset Case.Marker := {ga, o, no_, ni}

/-- The postpositions. -/
def postpositions : Finset Case.Marker := {de, e, to_, kara, made, yori}

/-- The markers casual speech drops, the nominative and the accusative. -/
def droppable : Finset Case.Marker := {ga, o}

/-- All the case markers. -/
def caseMarkers : Finset Case.Marker := caseParticles ∪ postpositions

/-- The cases the markers realize. -/
def inventory : Finset Case := Case.Marker.inventory caseMarkers

end Japanese.Case
