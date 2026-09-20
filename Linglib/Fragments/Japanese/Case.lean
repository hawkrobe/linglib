import Linglib.Syntax.Case.Basic

/-!
# Japanese case markers

Japanese marks the relations of a noun phrase with postpositional particles. Tsujimura divides
them into two classes: the case particles *ga*, *o*, *no* and *ni*, which carry no meaning of
their own, the verb fixing their role, and which casual speech drops; and the postpositions
*de*, *e*, *to*, *kara*, *made* and *yori*, which carry a meaning and cannot be dropped. Two
markers are polysemous: *ni* marks recipients, goals, times and the location of existence, and
*de* the location of an action and its instrument, so *ni* and *de* share the locative and *ni*
and *e* the allative. *Ga* is recorded as the nominative, setting aside the exhaustive-listing
reading of Kuroda and Kuno; *no* is also a nominalizer, *to* a quotative complementizer and
*kara* a reason conjunction, uses outside case marking. Sadakane and Koizumi's four *ni*
lexemes refine the single *ni* entry, the matter of `Studies/SadakaneKoizumi1995.lean`.

## Main definitions

* `Japanese.Case.Marker`, `Japanese.Case.caseParticles`, `Japanese.Case.postpositions` —
  the markers and Tsujimura's two classes
* `Japanese.Case.inventory` — the cases the markers realize

## References

* [kuno-1987]
* [kuroda-1972]
* [sadakane-koizumi-1995]
* [tsujimura-2014]
-/

namespace Japanese.Case

/-- A case-marking particle: its kana form and the cases it realizes, with its romanization. -/
structure Marker extends _root_.Case.Marker where
  /-- The romanization. -/
  romaji : String
  deriving DecidableEq

/-! ### Case particles -/

/-- *ga*, the nominative. -/
def ga : Marker := { form := "が", romaji := "ga", cases := {.nom} }

/-- *o*, the accusative. -/
def o : Marker := { form := "を", romaji := "o", cases := {.acc} }

/-- *no*, the genitive. -/
def no_ : Marker := { form := "の", romaji := "no", cases := {.gen} }

/-- *ni*: the dative of recipients, the allative of goals, the temporal of times and the
locative of existence. -/
def ni : Marker := { form := "に", romaji := "ni", cases := {.dat, .loc, .all, .tem} }

/-! ### Postpositions -/

/-- *de*: the locative of an action's place and the instrumental. -/
def de : Marker := { form := "で", romaji := "de", cases := {.loc, .inst} }

/-- *e*, the allative of motion toward. -/
def e : Marker := { form := "へ", romaji := "e", cases := {.all} }

/-- *to*, the comitative. -/
def to_ : Marker := { form := "と", romaji := "to", cases := {.com} }

/-- *kara*, the ablative of spatial and temporal sources. -/
def kara : Marker := { form := "から", romaji := "kara", cases := {.abl} }

/-- *made*, the terminative of spatial and temporal endpoints. -/
def made : Marker := { form := "まで", romaji := "made", cases := {.ter} }

/-- *yori*, the literary ablative, in the colloquial language the standard marker of the
comparative (`Japanese.Comparison.yori`). -/
def yori : Marker := { form := "より", romaji := "yori", cases := {.abl} }

/-! ### Tsujimura's classes and the inventory -/

/-- The case particles, dropped in casual speech. -/
def caseParticles : Finset Marker := {ga, o, no_, ni}

/-- The postpositions, which carry a meaning and are never dropped. -/
def postpositions : Finset Marker := {de, e, to_, kara, made, yori}

/-- All the case markers. -/
def caseMarkers : Finset Marker := caseParticles ∪ postpositions

/-- The cases the markers realize. -/
def inventory : Finset Case := _root_.Case.Marker.inventory (caseMarkers.image (·.toMarker))

end Japanese.Case
