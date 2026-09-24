module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Swahili verbs

This file defines the Swahili verbs of Palmieri's appendix on lexical reciprocity: nine verbs
in *-an-* with a lexicalized reciprocal entry and the eight binary bases they derive from.
Palmieri diagnoses the reciprocal entries as lexical by singular predication, under a modal
and in the habitual, and by the order of the reciprocal against the applicative and causative
suffixes. Some bases have drifted in meaning, *pambana* 'fight' from *pamba* 'decorate', and
*jibizana* 'discuss' has no binary base at all. The reciprocal marker and the derivational pairs
are in `Reciprocals.lean`.

## Main definitions

* `Swahili.Verbs.achana`, `gawana`, `gombana`, `gongana`, `jibizana`, `pambana`, `patana`,
  `pigana`, `shindana`: the lexical reciprocals
* `Swahili.Verbs.acha`, `gawa`, `gomba`, `gonga`, `pamba`, `pata`, `piga`, `shinda`: their
  binary bases

## References

* [G. Palmieri, *Lexical and Grammatical Reciprocity: Perspectives from Romance, Bantu and
  Beyond* (2024)][palmieri-2024]
-/

@[expose] public section

namespace Swahili.Verbs

/-! ### Lexical reciprocal verbs -/

/-- *achana* 'break up, divorce'. -/
def achana : Verb where
  form := "achana"
  frames := [ArgumentFrame.intransitive]

/-- *gawana* 'share'. -/
def gawana : Verb where
  form := "gawana"
  frames := [ArgumentFrame.intransitive]

/-- *gombana* 'quarrel'. -/
def gombana : Verb where
  form := "gombana"
  frames := [ArgumentFrame.intransitive]

/-- *gongana* 'collide'. -/
def gongana : Verb where
  form := "gongana"
  frames := [ArgumentFrame.intransitive]

/-- *jibizana* 'discuss, talk, dialogue', which has no binary base. -/
def jibizana : Verb where
  form := "jibizana"
  frames := [ArgumentFrame.intransitive]

/-- *pambana* 'fight, be in conflict'. -/
def pambana : Verb where
  form := "pambana"
  frames := [ArgumentFrame.intransitive]

/-- *patana* 'agree'. -/
def patana : Verb where
  form := "patana"
  frames := [ArgumentFrame.intransitive]

/-- *pigana* 'fight'. -/
def pigana : Verb where
  form := "pigana"
  frames := [ArgumentFrame.intransitive]

/-- *shindana* 'compete'. -/
def shindana : Verb where
  form := "shindana"
  frames := [ArgumentFrame.intransitive]

/-! ### Binary bases -/

/-- *acha* 'leave, abandon'. -/
def acha : Verb where
  form := "acha"
  frames := [ArgumentFrame.np]

/-- *gawa* 'distribute'. -/
def gawa : Verb where
  form := "gawa"
  frames := [ArgumentFrame.np]

/-- *gomba* 'argue with'. -/
def gomba : Verb where
  form := "gomba"
  frames := [ArgumentFrame.np]

/-- *gonga* 'crash against'. -/
def gonga : Verb where
  form := "gonga"
  frames := [ArgumentFrame.np]

/-- *pamba* 'decorate'. -/
def pamba : Verb where
  form := "pamba"
  frames := [ArgumentFrame.np]

/-- *pata* 'find'. -/
def pata : Verb where
  form := "pata"
  frames := [ArgumentFrame.np]

/-- *piga* 'hit'. -/
def piga : Verb where
  form := "piga"
  frames := [ArgumentFrame.np]

/-- *shinda* 'defeat'. -/
def shinda : Verb where
  form := "shinda"
  frames := [ArgumentFrame.np]

end Swahili.Verbs
