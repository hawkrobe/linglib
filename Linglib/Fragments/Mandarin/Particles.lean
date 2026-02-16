import Linglib.Theories.Pragmatics.NeoGricean.Presuppositions
import Linglib.Phenomena.Presupposition.Studies.Wang2025

/-!
# Mandarin Presuppositional Particles

Lexical entries for Mandarin presupposition triggers, linking Fragment-level
lexical data to the NeoGricean trigger typology (Wang 2025 Table 4.1) and
experimental data (Wang 2025 Experiments 1-3).

## Triggers

| Particle | Gloss      | Trigger Type  | Alt Structure | Alt Form        |
|----------|------------|---------------|---------------|-----------------|
| 也 ye    | also       | iterative     | deletion      | ∅               |
| 又 you   | again      | iterative     | deletion      | ∅               |
| 仍 reng  | still      | iterative     | deletion      | ∅               |
| 就 jiu   | only       | cleft         | none          | ∅               |
| 知道 zhidao | know    | factive       | replacement   | believe (以为)   |
| 不再 buzai | no longer | changeOfState | replacement   | not (不)         |
| 开始 kaishi | start   | aspectual     | replacement   | do (做)          |
| 反而 fan'er | instead | iterative     | replacement   | and (和)         |
| 而 er    | instead    | iterative     | replacement   | and (和)         |
| 还 hai   | still      | iterative     | deletion      | ∅               |

## Cross-Module Connections

- `NeoGricean.Presuppositions.AltStructure`: alternative classification
- `NeoGricean.Presuppositions.PresupTrigger`: trigger type
- `Phenomena.Presupposition.Studies.Wang2025`: experimental data

## References

- Wang, S. (2025). Presupposition, Competition, and Coherence. MIT dissertation.
-/

namespace Fragments.Mandarin.Particles

open NeoGricean.Presuppositions (PresupTrigger AltStructure PresupTriggerEntry)
open Phenomena.Presupposition.Studies.Wang2025 (MandarinTrigger)

/--
A Mandarin presuppositional particle entry.
Links surface form to trigger type and alternative structure.
-/
structure PresupParticle where
  /-- Chinese character(s) -/
  hanzi : String
  /-- Pinyin romanization -/
  pinyin : String
  /-- English gloss -/
  gloss : String
  /-- Corresponding trigger entry (type + alternative structure) -/
  triggerEntry : PresupTriggerEntry
  /-- Link to experimental data trigger identifier -/
  dataTrigger : MandarinTrigger
  deriving Repr

/-- 也 ye 'also' — additive particle, deletion alternative. -/
def ye : PresupParticle :=
  { hanzi := "也", pinyin := "yě", gloss := "also"
  , triggerEntry := { trigger := .iterative, altStructure := .deletion }
  , dataTrigger := .ye }

/-- 又 you 'again' — repetitive, deletion alternative. -/
def you : PresupParticle :=
  { hanzi := "又", pinyin := "yòu", gloss := "again"
  , triggerEntry := { trigger := .iterative, altStructure := .deletion }
  , dataTrigger := .you }

/-- 仍 reng 'still' — continuative, deletion alternative. -/
def reng : PresupParticle :=
  { hanzi := "仍", pinyin := "réng", gloss := "still"
  , triggerEntry := { trigger := .iterative, altStructure := .deletion }
  , dataTrigger := .reng }

/-- 就 jiu 'only' — exclusive, NO structural alternative. -/
def jiu : PresupParticle :=
  { hanzi := "就", pinyin := "jiù", gloss := "only"
  , triggerEntry := { trigger := .cleft, altStructure := .none }
  , dataTrigger := .jiu }

/-- 知道 zhidao 'know' — factive, replacement alternative (以为 yiwei 'believe'). -/
def zhidao : PresupParticle :=
  { hanzi := "知道", pinyin := "zhīdào", gloss := "know"
  , triggerEntry := { trigger := .factive, altStructure := .replacement, altForm := some "以为" }
  , dataTrigger := .zhidao }

/-- 不再 buzai 'no longer' — cessative, replacement alternative (不 bu 'not'). -/
def buzai : PresupParticle :=
  { hanzi := "不再", pinyin := "bú zài", gloss := "no longer"
  , triggerEntry := { trigger := .changeOfState, altStructure := .replacement, altForm := some "不" }
  , dataTrigger := .buzai }

/-- 开始 kaishi 'start' — inchoative, replacement alternative (做 zuo 'do'). -/
def kaishi : PresupParticle :=
  { hanzi := "开始", pinyin := "kāishǐ", gloss := "start"
  , triggerEntry := { trigger := .aspectual, altStructure := .replacement, altForm := some "做" }
  , dataTrigger := .kaishi }

/-- 反而 fan'er 'instead' — contrastive, replacement alternative. -/
def faner : PresupParticle :=
  { hanzi := "反而", pinyin := "fǎn'ér", gloss := "instead"
  , triggerEntry := { trigger := .iterative, altStructure := .replacement, altForm := some "和" }
  , dataTrigger := .faner }

/-- 而 er 'instead' — weaker contrastive, replacement alternative. -/
def er : PresupParticle :=
  { hanzi := "而", pinyin := "ér", gloss := "instead"
  , triggerEntry := { trigger := .iterative, altStructure := .replacement, altForm := some "和" }
  , dataTrigger := .er }

/-- All particles studied in Wang (2025). -/
def wang2025Particles : List PresupParticle :=
  [ye, you, reng, jiu, zhidao, buzai, kaishi, faner, er]

-- ============================================================================
-- Per-Datum Verification Theorems
-- ============================================================================

/-- ye has deletion alternative structure. -/
theorem ye_deletion : ye.triggerEntry.altStructure = .deletion := rfl

/-- jiu has no structural alternative. -/
theorem jiu_no_alt : jiu.triggerEntry.altStructure = .none := rfl

/-- zhidao has replacement alternative. -/
theorem zhidao_replacement : zhidao.triggerEntry.altStructure = .replacement := rfl

/-- Obligatory triggers (ye, you, reng) all have deletion alternatives. -/
theorem obligatory_all_deletion :
    ye.triggerEntry.altStructure = .deletion ∧
    you.triggerEntry.altStructure = .deletion ∧
    reng.triggerEntry.altStructure = .deletion := ⟨rfl, rfl, rfl⟩

/-- Blocked trigger (jiu) has no alternative — this is what predicts blocking. -/
theorem blocked_no_alt :
    jiu.triggerEntry.altStructure = .none := rfl

/-- ye links to experimental data trigger .ye -/
theorem ye_data_link : ye.dataTrigger = .ye := rfl

/-- jiu links to experimental data trigger .jiu -/
theorem jiu_data_link : jiu.dataTrigger = .jiu := rfl


end Fragments.Mandarin.Particles
