module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Japanese verbs

The Japanese clause-embedding and departure predicates the studies of Qing and Uegaki and of
Ozaki consume: the preferential attitudes *tanoshimi* 'look forward to', *osore* 'fear',
*kitai* 'expect', *nozomu* 'hope' and *shinpai* 'worry', whose distributivity over
alternatives follows from the kind of preference each records; the morphological causative
in *-(s)ase*, whose causee is accusative under the coercive reading and dative under the
permissive one; and the departure verbs *hanareru* 'leave' and *deru* 'exit', which take
their source in the accusative or the ablative and are unaccusative, their Voice being
non-thematic.

## Main definitions

* `Japanese.Verb` — a Japanese verb, the root `Verb` with its romanization
* `Japanese.verbs` — the attitude, causative and departure verbs

## References

* [ozaki-2026]
* [qing-uegaki-2025]
* [song-1996]
-/

@[expose] public section

namespace Japanese

open ArgumentStructure

/-- A Japanese verb: the root entry, its `form` the romanized citation form. -/
structure Verb extends _root_.Verb where
  deriving BEq

/-! ### Preferential attitudes -/

/-- *tanoshimi* 'look forward to', a positive preference relative to relevance. -/
def tanosimi : Verb where
  form := "tanosimi"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.relevanceBased .positive))

/-- *osore* 'fear', a negative preference by comparison of degrees. -/
def osore : Verb where
  form := "osore"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative))

/-- *kitai* 'expect, hope', a positive preference by comparison of degrees. -/
def kitai : Verb where
  form := "kitai"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *nozomu* 'hope', a positive preference by comparison of degrees. -/
def nozomu : Verb where
  form := "nozomu"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *shinpai* 'worry', a preference relative to uncertainty. -/
def shinpai : Verb where
  form := "shinpai"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .uncertaintyBased)

/-! ### Causatives -/

/-- *ik-ase-ru* 'make go', the causative of *iku* with an accusative causee. -/
def ik_ase : Verb where
  form := "ik-ase-ru"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  causative := some .make

/-- *tabe-sase-ru* 'make eat', the causative of *taberu* with an accusative causee. -/
def tabe_sase : Verb where
  form := "tabe-sase-ru"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  causative := some .make

/-! ### Departure verbs -/

/-- *hanareru* 'leave': the leaver its theme, the source accusative or ablative, and no
thematic Voice. -/
def hanareru : Verb where
  form := "hanareru"
  frames := [ArgumentFrame.np]
  voiceType := some .nonThematic
  passivizable := false

/-- *deru* 'exit': the leaver its theme, the source accusative or ablative, and no thematic
Voice. -/
def deru : Verb where
  form := "deru"
  frames := [ArgumentFrame.np]
  voiceType := some .nonThematic
  passivizable := false

/-- The inventory. -/
def verbs : List Verb :=
  [tanosimi, osore, kitai, nozomu, shinpai, ik_ase, tabe_sase, hanareru, deru]

end Japanese
