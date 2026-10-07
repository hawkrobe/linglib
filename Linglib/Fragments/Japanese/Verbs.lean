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

* `Japanese.Verb` — a Japanese verb, the root `Verb` with its spelling
* `Japanese.verbs` — the attitude, causative and departure verbs

## References

* [ozaki-2026]
* [qing-uegaki-2025]
* [song-1996]
-/

@[expose] public section

namespace Japanese

open ArgumentStructure

/-- A Japanese verb is the root entry, with its romanized citation form, and its spelling. -/
structure Verb extends _root_.Verb where
  /-- The spelling in kanji and kana. -/
  script : String
  deriving BEq

/-! ### Preferential attitudes -/

/-- 楽しみ *tanoshimi* 'look forward to', a positive preference relative to relevance. -/
def tanoshimi : Verb where
  form := "tanoshimi"
  script := "楽しみ"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive false)

/-- 恐れ *osore* 'fear', a negative preference by comparison of degrees. -/
def osore : Verb where
  form := "osore"
  script := "恐れ"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative true)

/-- 期待 *kitai* 'expect, hope', a positive preference by comparison of degrees. -/
def kitai : Verb where
  form := "kitai"
  script := "期待"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- 望む *nozomu* 'hope', a positive preference by comparison of degrees. -/
def nozomu : Verb where
  form := "nozomu"
  script := "望む"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- 心配 *shinpai* 'worry', a preference relative to uncertainty. -/
def shinpai : Verb where
  form := "shinpai"
  script := "心配"
  frames := [ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative false)

/-! ### Causatives -/

/-- 行かせる *ik-ase-ru* 'make go', the causative of *iku* with an accusative causee. -/
def ik_ase : Verb where
  form := "ik-ase-ru"
  script := "行かせる"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]

/-- 食べさせる *tabe-sase-ru* 'make eat', the causative of *taberu* with an accusative causee. -/
def tabe_sase : Verb where
  form := "tabe-sase-ru"
  script := "食べさせる"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]

/-! ### Departure verbs -/

/-- 離れる *hanareru* 'leave' takes the leaver as its theme and the source in the accusative or
ablative, with no thematic Voice. -/
def hanareru : Verb where
  form := "hanareru"
  script := "離れる"
  frames := [ArgumentFrame.np]
  voiceType := some .nonThematic
  passivizable := false

/-- 出る *deru* 'exit' takes the leaver as its theme and the source in the accusative or ablative,
with no thematic Voice. -/
def deru : Verb where
  form := "deru"
  script := "出る"
  frames := [ArgumentFrame.np]
  voiceType := some .nonThematic
  passivizable := false

/-- The inventory. -/
def verbs : List Verb :=
  [tanoshimi, osore, kitai, nozomu, shinpai, ik_ase, tabe_sase, hanareru, deru]

end Japanese
