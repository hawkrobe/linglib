import Mathlib.Data.Finset.Union
import Linglib.Syntax.Case.Basic

/-!
# Korean case markers

Korean marks case with postpositional particles, several with allomorphs chosen by the final
segment of the noun: the nominative *-i* after a consonant and *-ga* after a vowel, the
accusative *-eul* and *-reul*, the genitive *-ui*, the dative *-ege*, or *-hante* in the
colloquial language, the locative *-eseo*, the ablative *-buteo* and *-eseo*, the instrumental
*-(eu)ro* and the comitative *-gwa* and *-wa*, as Sohn describes them. The cases the markers
realize run from the nominative to the comitative without a gap on Blake's hierarchy.

## Main definitions

* `Korean.Case.CaseMarker`, `Korean.Case.markers` — the markers
* `Korean.Case.inventory` — the cases they realize

## Main results

* `Korean.Case.inventory_isValid` — the inventory is contiguous on Blake's hierarchy

## References

* [blake-1994]
* [sohn-1999]
-/

namespace Korean.Case

/-- A case-marking particle: its form, with allomorphs, and the cases it realizes. -/
structure CaseMarker where
  /-- The romanized form, allomorphs separated by a slash. -/
  form : String
  /-- The cases the marker realizes. -/
  cases : Finset Case
  deriving DecidableEq

/-- The nominative *-i* after a consonant and *-ga* after a vowel. -/
def ga : CaseMarker := { form := "-i/-ga", cases := {.nom} }

/-- The accusative *-eul* after a consonant and *-reul* after a vowel. -/
def reul : CaseMarker := { form := "-eul/-reul", cases := {.acc} }

/-- The genitive *-ui*. -/
def ui : CaseMarker := { form := "-ui", cases := {.gen} }

/-- The dative *-ege*, colloquially *-hante*. -/
def ege : CaseMarker := { form := "-ege/-hante", cases := {.dat} }

/-- *-eseo*, the locative of an action's place and the ablative. -/
def eseo : CaseMarker := { form := "-eseo", cases := {.loc, .abl} }

/-- The ablative *-buteo* of temporal and spatial starting points. -/
def buteo : CaseMarker := { form := "-buteo", cases := {.abl} }

/-- The instrumental *-euro* after a consonant and *-ro* after a vowel. -/
def ro : CaseMarker := { form := "-(eu)ro", cases := {.inst} }

/-- The comitative *-gwa* after a consonant and *-wa* after a vowel. -/
def wa : CaseMarker := { form := "-gwa/-wa", cases := {.com} }

/-- The case markers. -/
def markers : Finset CaseMarker := {ga, reul, ui, ege, eseo, buteo, ro, wa}

/-- The cases the markers realize. -/
def inventory : Finset Case := markers.biUnion (·.cases)

/-- The inventory is contiguous on Blake's hierarchy. -/
theorem inventory_isValid : Case.IsValidInventory inventory := by decide

end Korean.Case
