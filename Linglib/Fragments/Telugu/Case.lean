module

public import Linglib.Syntax.Case.Basic

/-!
# Telugu case

Telugu marks four cases on the noun by suffix and the other relations by postposition. The
nominative is the bare stem and the genitive the oblique stem, neither with a suffix; the
accusative suffix is *-ni* and the dative *-ki*, each also heard with *-u* for *-i* except after
an *i*. The oblique stem carries the accusative and dative suffixes and the postpositions alike,
among them *lō* 'in' and *nunci* 'from'. Dravidian grammars keep the postpositions apart from
the cases, and Aitha shows the Telugu ones to stand outside the noun's prosodic word. The forms
are those of the paradigms of *illu* 'house' and *samudram* 'ocean' that Aitha reproduces from
Krishnamurti and Gwynn's grammar; the oblique stem is the matter of `Studies/Aitha2026.lean`.

## Main definitions

* `Telugu.Case.ni`, `Telugu.Case.ki`: the accusative and dative suffixes.
* `Telugu.Case.lō`, `Telugu.Case.nunci`: the locative and ablative postpositions.
* `Telugu.Case.inventory`: the cases, the unmarked two with those the markers realize.

## References

* [aitha-2026]
* [kolichala-2026]
-/

@[expose] public section

namespace Telugu.Case

/-! ### Suffixes -/

/-- The accusative *-ni*, also *-nu* except after an *i*. -/
def ni : Case.Marker := { form := "-ni/-nu", cases := {.acc} }

/-- The dative *-ki*, also *-ku* except after an *i*. -/
def ki : Case.Marker := { form := "-ki/-ku", cases := {.dat} }

/-- The case suffixes, inside the noun's prosodic word. -/
def suffixes : Finset Case.Marker := {ni, ki}

/-! ### Postpositions -/

/-- *lō* 'in', the locative. -/
def lō : Case.Marker := { form := "lō", cases := {.loc} }

/-- *nunci* 'from', the ablative. -/
def nunci : Case.Marker := { form := "nunci", cases := {.abl} }

/-- The postpositions, separate words after the oblique stem. -/
def postpositions : Finset Case.Marker := {lō, nunci}

/-! ### The inventory -/

/-- The unmarked cases, the nominative on the bare stem and the genitive on the oblique stem. -/
def unmarked : Finset Case := {.nom, .gen}

/-- The cases, the unmarked two with those the suffixes and the postpositions realize. -/
def inventory : Finset Case := unmarked ∪ Case.Marker.inventory (suffixes ∪ postpositions)

end Telugu.Case
