import Linglib.Theories.Semantics.Causation.Resultatives

/-!
# Mandarin Resultative Compound Fragment

Lexical entries for Mandarin V-V resultative compounds and phase complements,
parameterized by cross-linguistic types from `Theories.Semantics.Causation.Resultatives`.

## Compound data

Each V-V compound entry records V1, V2, result orientation, and realization type.
Object-oriented compounds (dǎ-sǐ "hit-die") and subject-oriented compounds
(kū-lèi "cry-tired") coexist productively — Mandarin does not enforce the
Direct Object Restriction (DOR).

## Phase complements

A closed class of grammaticalized V2 morphemes with fixed `CoSType` semantics:
dǎo 倒, wán 完, hǎo 好, diào 掉, zhù 住.

## Cross-Module Connections

- `Theories.Semantics.Causation.Resultatives`: `ResultativeRealization`,
  `ResultOrientation`, `PhaseComplement`, `CoSType`
- `Tay2024`: thesis-specific
  theorems and analysis that import this Fragment
-/

namespace Fragments.Mandarin.Resultatives

open Semantics.Causation.Resultatives
open Semantics.Verb.ChangeOfState (CoSType)

-- ════════════════════════════════════════════════════
-- § 1. Compound Data
-- ════════════════════════════════════════════════════

/-- A Mandarin V-V resultative compound lexical entry. -/
structure CompoundEntry where
  v1 : String
  v2 : String
  gloss : String
  translation : String
  orientation : ResultOrientation
  realization : ResultativeRealization := .verbCompound
  deriving Repr, BEq

/-- 打死 dǎ-sǐ "hit-die" = "beat to death" (object-oriented). -/
def da_si : CompoundEntry :=
  { v1 := "da", v2 := "si", gloss := "hit-die"
  , translation := "beat to death", orientation := .objectOriented }

/-- 打破 dǎ-pò "hit-break" = "break by hitting" (object-oriented). -/
def da_po : CompoundEntry :=
  { v1 := "da", v2 := "po", gloss := "hit-break"
  , translation := "break by hitting", orientation := .objectOriented }

/-- 哭累 kū-lèi "cry-tired" = "cry oneself tired" (subject-oriented). -/
def ku_lei : CompoundEntry :=
  { v1 := "ku", v2 := "lei", gloss := "cry-tired"
  , translation := "cry oneself tired", orientation := .subjectOriented }

/-- 吃饱 chī-bǎo "eat-full" = "eat until full" (subject-oriented). -/
def chi_bao : CompoundEntry :=
  { v1 := "chi", v2 := "bao", gloss := "eat-full"
  , translation := "eat until full", orientation := .subjectOriented }

/-- 跑累 pǎo-lèi "run-tired" = "run oneself tired" (subject-oriented). -/
def pao_lei : CompoundEntry :=
  { v1 := "pao", v2 := "lei", gloss := "run-tired"
  , translation := "run oneself tired", orientation := .subjectOriented }

/-- 哭湿 kū-shī "cry-wet" = "cry (handkerchief) wet" (object-oriented). -/
def ku_shi : CompoundEntry :=
  { v1 := "ku", v2 := "shi", gloss := "cry-wet"
  , translation := "cry (handkerchief) wet", orientation := .objectOriented }

/-- 推开 tuī-kāi "push-open" = "push open" (object-oriented). -/
def tui_kai : CompoundEntry :=
  { v1 := "tui", v2 := "kai", gloss := "push-open"
  , translation := "push open", orientation := .objectOriented }

/-- 喝醉 hē-zuì "drink-drunk" = "drink oneself drunk" (subject-oriented). -/
def he_zui : CompoundEntry :=
  { v1 := "he", v2 := "zui", gloss := "drink-drunk"
  , translation := "drink oneself drunk", orientation := .subjectOriented }

def allCompounds : List CompoundEntry :=
  [da_si, da_po, ku_lei, chi_bao, pao_lei, ku_shi, tui_kai, he_zui]

-- ════════════════════════════════════════════════════
-- § 2. Phase Complements
-- ════════════════════════════════════════════════════

/-- A phase complement lexical entry mapping form to `PhaseComplement`. -/
structure PhaseComplementEntry where
  form : String
  gloss : String
  phase : PhaseComplement
  example_ : String
  deriving Repr, BEq

def phase_dao : PhaseComplementEntry :=
  { form := "dao", gloss := "fall", phase := .dao
  , example_ := "tui-dao (push-fall = push over)" }

def phase_wan : PhaseComplementEntry :=
  { form := "wan", gloss := "finish", phase := .wan
  , example_ := "chi-wan (eat-finish = finish eating)" }

def phase_hao : PhaseComplementEntry :=
  { form := "hao", gloss := "good", phase := .hao
  , example_ := "zuo-hao (do-good = get done)" }

def phase_diao : PhaseComplementEntry :=
  { form := "diao", gloss := "fall off", phase := .diao
  , example_ := "reng-diao (throw-fall.off = throw away)" }

def phase_zhu : PhaseComplementEntry :=
  { form := "zhu", gloss := "hold", phase := .zhu
  , example_ := "ji-zhu (remember-hold = keep in mind)" }

def allPhaseComplements : List PhaseComplementEntry :=
  [phase_dao, phase_wan, phase_hao, phase_diao, phase_zhu]

end Fragments.Mandarin.Resultatives
