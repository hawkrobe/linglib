import Linglib.Syntax.Case.Basic

/-!
# Korean case markers

Korean marks case with postpositional particles, which Sohn treats as bound words rather than
clitics, several with allomorphs chosen by the final segment of the noun: the nominative *-i*
after a consonant and *-ga* after a vowel, the accusative *-eul* and *-reul*, the genitive
*-ui*, the dative *-ege*, colloquially *-hante* and to a social superior *-kke*, the locative
*-e* of a state and goal and *-eseo* of an action and source, the ablative *-buteo*, the
instrumental and directional *-(eu)ro*, and the comitative *-gwa* and *-wa*, *-hago* and the
casual *-(i)rang*. Casual speech drops the nominative, accusative, genitive and dative
particles. Forms are in the Revised Romanization; Sohn writes *ka*, *(l)ul*, *uy*, *eykey*,
*hanthey*, *kkey*, *ey*, *eyse*, *pwuthe*, *(u)lo* and *(k)wa*.

## Main definitions

* `Korean.Case.markers` — the markers, with allomorphs in the form
* `Korean.Case.inventory` — the cases they realize

## References

* [sohn-1994]
-/

namespace Korean.Case

/-- The nominative *-i* after a consonant and *-ga* after a vowel. -/
def ga : Case.Marker := { form := "-i/-ga", cases := {.nom} }

/-- The accusative *-eul* after a consonant and *-reul* after a vowel. -/
def reul : Case.Marker := { form := "-eul/-reul", cases := {.acc} }

/-- The genitive *-ui*. -/
def ui : Case.Marker := { form := "-ui", cases := {.gen} }

/-- The dative *-ege*, colloquially *-hante*. -/
def ege : Case.Marker := { form := "-ege/-hante", cases := {.dat} }

/-- The honorific dative *-kke*. -/
def kke : Case.Marker := { form := "-kke", cases := {.dat} }

/-- *-e*, the locative of a state and the goal of motion. -/
def e : Case.Marker := { form := "-e", cases := {.loc, .all} }

/-- *-eseo*, the locative of an action and the source of motion. -/
def eseo : Case.Marker := { form := "-eseo", cases := {.loc, .abl} }

/-- The ablative *-buteo* 'from', also after *-eseo* and *-(eu)ro*. -/
def buteo : Case.Marker := { form := "-buteo", cases := {.abl} }

/-- *-(eu)ro*, the instrumental and the directional 'toward'. -/
def ro : Case.Marker := { form := "-(eu)ro", cases := {.inst, .all} }

/-- The comitative *-gwa* after a consonant and *-wa* after a vowel, *-hago*, and the casual
*-(i)rang*. -/
def wa : Case.Marker := { form := "-gwa/-wa, -hago, -(i)rang", cases := {.com} }

/-- The case markers. -/
def markers : Finset Case.Marker := {ga, reul, ui, ege, kke, e, eseo, buteo, ro, wa}

/-- The cases the markers realize. -/
def inventory : Finset Case := Case.Marker.inventory markers

end Korean.Case
