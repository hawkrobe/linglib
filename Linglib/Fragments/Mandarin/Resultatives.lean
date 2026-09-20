import Linglib.Syntax.ConstructionGrammar.Resultatives
import Linglib.Semantics.Aspect.Phasal

/-!
# Mandarin resultative compounds and phase complements

This file enters Mandarin V-V resultative compounds and phase complements. A resultative
compound such as *dǎ-sǐ* 'hit-die' pairs a verb describing the causing event with a verb
describing the result, and the result is predicated either of the object, as in *dǎ-sǐ*, or of
the subject, as in *kū-lèi* 'cry-tired'; Mandarin admits both and does not restrict the result
to the direct object. A phase complement is one of a closed class of grammaticalized second
verbs, *dào* 到, *wán* 完, *hǎo* 好, *diào* 掉 and *zhù* 住, marking the attainment,
completion, removal or persistence of a result, and each is entered with the change of state
it marks. Tay's analysis of the compounds as words built in morphology lives in
`Studies/Tay2024.lean`.

## Main definitions

* `Compound` — a V-V resultative compound with the orientation of its result.
* `PhaseComplement` — a phase complement with the change of state it marks.

## TODO

The change-of-state types are a coarse fit. Sybesma distinguishes *-dào* (attainment of a
goal) from *-hǎo* (attainment of a satisfactory state) and *-diào* (removal of the patient),
all completions rather than inceptions, and *-wán* marks the cessation of the activity rather
than a result of the patient; `Aspect.Phasal` has no completion constructor. The toneless form
*dao* also covers 倒 'fall' in *tuī-dǎo* 'push over', which is not the phase complement 到.

## References

* [tay-2024]
* [sybesma-2017]
-/

namespace Mandarin.Resultatives

/-! ### Compounds -/

/-- A Mandarin V-V resultative compound with its two verbs, its characters, its gloss, its
translation and the argument its result is predicated of. -/
structure Compound where
  /-- The first verb, describing the causing event. -/
  v1 : String
  /-- The second verb, describing the result. -/
  v2 : String
  /-- The characters. -/
  hanzi : String
  /-- The verb-by-verb gloss. -/
  gloss : String
  /-- The translation. -/
  translation : String
  /-- The argument the result is predicated of. -/
  orientation : ConstructionGrammar.Resultatives.ResultOrientation
  deriving Repr, DecidableEq

/-- *dǎ-sǐ* 打死 'hit-die', 'beat to death'. -/
def da_si : Compound :=
  { v1 := "dǎ", v2 := "sǐ", hanzi := "打死", gloss := "hit-die", translation := "beat to death",
    orientation := .objectOriented }

/-- *dǎ-pò* 打破 'hit-break', 'break by hitting'. -/
def da_po : Compound :=
  { v1 := "dǎ", v2 := "pò", hanzi := "打破", gloss := "hit-break",
    translation := "break by hitting", orientation := .objectOriented }

/-- *kū-lèi* 哭累 'cry-tired', 'cry oneself tired'. -/
def ku_lei : Compound :=
  { v1 := "kū", v2 := "lèi", hanzi := "哭累", gloss := "cry-tired",
    translation := "cry oneself tired", orientation := .subjectOriented }

/-- *chī-bǎo* 吃饱 'eat-full', 'eat until full'. -/
def chi_bao : Compound :=
  { v1 := "chī", v2 := "bǎo", hanzi := "吃饱", gloss := "eat-full",
    translation := "eat until full", orientation := .subjectOriented }

/-- *pǎo-lèi* 跑累 'run-tired', 'run oneself tired'. -/
def pao_lei : Compound :=
  { v1 := "pǎo", v2 := "lèi", hanzi := "跑累", gloss := "run-tired",
    translation := "run oneself tired", orientation := .subjectOriented }

/-- *kū-shī* 哭湿 'cry-wet', 'cry (a handkerchief) wet'. -/
def ku_shi : Compound :=
  { v1 := "kū", v2 := "shī", hanzi := "哭湿", gloss := "cry-wet",
    translation := "cry (a handkerchief) wet", orientation := .objectOriented }

/-- *tuī-kāi* 推开 'push-open'. -/
def tui_kai : Compound :=
  { v1 := "tuī", v2 := "kāi", hanzi := "推开", gloss := "push-open", translation := "push open",
    orientation := .objectOriented }

/-- *hē-zuì* 喝醉 'drink-drunk', 'drink oneself drunk'. -/
def he_zui : Compound :=
  { v1 := "hē", v2 := "zuì", hanzi := "喝醉", gloss := "drink-drunk",
    translation := "drink oneself drunk", orientation := .subjectOriented }

/-! ### Phase complements -/

/-- A Mandarin phase complement with its pinyin, its character, its gloss, the change of state
it marks and a representative verb it combines with. -/
structure PhaseComplement where
  /-- The pinyin form. -/
  pinyin : String
  /-- The character. -/
  hanzi : String
  /-- The gloss. -/
  gloss : String
  /-- The change of state the complement marks. -/
  phasal : Aspect.Phasal
  /-- A representative verb–complement combination with its translation. -/
  example_ : String
  deriving Repr, DecidableEq

/-- *-dào* 到 'arrive', *mǎi-dào* 'succeed in buying'. -/
def dao : PhaseComplement :=
  { pinyin := "dào", hanzi := "到", gloss := "arrive", phasal := .inception,
    example_ := "mǎi-dào 'succeed in buying'" }

/-- *-wán* 完 'finish', *chī-wán* 'finish eating'. -/
def wan : PhaseComplement :=
  { pinyin := "wán", hanzi := "完", gloss := "finish", phasal := .cessation,
    example_ := "chī-wán 'finish eating'" }

/-- *-hǎo* 好 'good', *zuò-hǎo* 'get done'. -/
def hao : PhaseComplement :=
  { pinyin := "hǎo", hanzi := "好", gloss := "good", phasal := .inception,
    example_ := "zuò-hǎo 'get done'" }

/-- *-diào* 掉 'fall off', *rēng-diào* 'throw away'. -/
def diao : PhaseComplement :=
  { pinyin := "diào", hanzi := "掉", gloss := "fall off", phasal := .inception,
    example_ := "rēng-diào 'throw away'" }

/-- *-zhù* 住 'hold', *jì-zhù* 'keep in mind'. -/
def zhu : PhaseComplement :=
  { pinyin := "zhù", hanzi := "住", gloss := "hold", phasal := .continuation,
    example_ := "jì-zhù 'keep in mind'" }

end Mandarin.Resultatives
