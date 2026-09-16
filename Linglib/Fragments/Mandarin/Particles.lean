import Linglib.Semantics.Presupposition.TriggerTypology

/-!
# Mandarin Presuppositional Particles

Lexical entries for the Mandarin presupposition triggers studied
experimentally in [wang-2025]. Entries carry consensus trigger-type
metadata only; [wang-2025]'s alternative-structure classification and the
competition analysis built on it live in `Studies/Wang2025.lean`.

| Particle    | Gloss      | Trigger Type  |
|-------------|------------|---------------|
| 也 ye       | also       | additive      |
| 又 you      | again      | iterative     |
| 再 zai      | again      | iterative     |
| 仍 reng     | still      | continuative  |
| 就 jiu      | only       | exclusive     |
| 知道 zhidao | know       | factive       |
| 不再 buzai  | no longer  | changeOfState |
| 开始 kaishi | start      | aspectual     |
| 反而 fan'er | instead    | contrastive   |
| 而 er       | instead    | contrastive   |
-/

namespace Mandarin.Particles

open Presupposition.TriggerTypology

/-- Mandarin presupposition triggers studied in [wang-2025] Experiments 1-2. -/
inductive MandarinTrigger where
  | ye     -- 也 'also' (additive)
  | you    -- 又 'again' (repetitive)
  | reng   -- 仍 'still' (continuative)
  | jiu    -- 就 'only' (exclusive)
  | zhidao -- 知道 'know' (factive)
  | buzai  -- 不再 'no longer' (cessative)
  | kaishi -- 开始 'start' (inchoative)
  | faner  -- 反而 'instead' (contrastive)
  | er     -- 而 'instead' (contrastive, weaker)
  deriving DecidableEq, Repr

/-- A Mandarin presuppositional particle entry. -/
structure PresupParticle where
  /-- Chinese character(s) -/
  hanzi : String
  /-- Pinyin romanization -/
  pinyin : String
  /-- English gloss -/
  gloss : String
  /-- Trigger type (consensus classification) -/
  trigger : PresupTrigger
  /-- The trigger identifier of the experimental data, for the particles [wang-2025] tested. -/
  dataTrigger : Option MandarinTrigger := none
  deriving Repr, DecidableEq

/-- 也 ye 'also' — additive particle ([kripke-2009]'s *too*-class). -/
def ye : PresupParticle :=
  { hanzi := "也", pinyin := "yě", gloss := "also"
  , trigger := .additive, dataTrigger := some .ye }

/-- 又 you 'again' — repetitive iterative, the higher of the two *again* adverbs. -/
def you : PresupParticle :=
  { hanzi := "又", pinyin := "yòu", gloss := "again"
  , trigger := .iterative, dataTrigger := some .you }

/-- 再 zai 'again' — repetitive iterative, the lower of the two *again* adverbs. -/
def zai : PresupParticle :=
  { hanzi := "再", pinyin := "zài", gloss := "again", trigger := .iterative }

/-- 仍 reng 'still' — continuative.
    Distinct from 又 *you* 'again' (iterative): *reng*'s presupposition is
    *uninterrupted continuation* of P throughout an interval, whereas
    *you* presupposes P-then-not-P-then-P-again. The original encoding
    of *reng* as `.iterative` (matching *you*) collapsed this contrast;
    `.continuative` was added to `PresupTrigger` to distinguish them. -/
def reng : PresupParticle :=
  { hanzi := "仍", pinyin := "réng", gloss := "still"
  , trigger := .continuative, dataTrigger := some .reng }

/-- 就 jiu 'only' — exclusive; presupposes its prejacent. -/
def jiu : PresupParticle :=
  { hanzi := "就", pinyin := "jiù", gloss := "only"
  , trigger := .exclusive, dataTrigger := some .jiu }

/-- 知道 zhidao 'know' — factive (non-factive counterpart: 以为 yiwei 'believe'). -/
def zhidao : PresupParticle :=
  { hanzi := "知道", pinyin := "zhīdào", gloss := "know"
  , trigger := .factive, dataTrigger := some .zhidao }

/-- 不再 buzai 'no longer' — cessative change-of-state. -/
def buzai : PresupParticle :=
  { hanzi := "不再", pinyin := "bú zài", gloss := "no longer"
  , trigger := .changeOfState, dataTrigger := some .buzai }

/-- 开始 kaishi 'start' — inchoative aspectual. -/
def kaishi : PresupParticle :=
  { hanzi := "开始", pinyin := "kāishǐ", gloss := "start"
  , trigger := .aspectual, dataTrigger := some .kaishi }

/-- 反而 fan'er 'instead' — contrastive. -/
def faner : PresupParticle :=
  { hanzi := "反而", pinyin := "fǎn'ér", gloss := "instead"
  , trigger := .contrastive, dataTrigger := some .faner }

/-- 而 er 'instead' — weaker contrastive. -/
def er : PresupParticle :=
  { hanzi := "而", pinyin := "ér", gloss := "instead"
  , trigger := .contrastive, dataTrigger := some .er }

/-- All particles studied in [wang-2025]. -/
def wang2025Particles : List PresupParticle :=
  [ye, you, reng, jiu, zhidao, buzai, kaishi, faner, er]

end Mandarin.Particles
