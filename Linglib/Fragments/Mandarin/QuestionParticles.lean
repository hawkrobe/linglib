import Linglib.Semantics.Questions.Bias.Defs

/-!
# Mandarin Question Particles
[zheng-2025]

Lexical entries for Mandarin interrogative particles with distributional
properties and bias profiles. The fragment commits only to theory-neutral
lexical primitives; the left-peripheral layer assignment lives in
`Zheng2025`.

## Particles

| Particle | Gloss | Evidential | Epistemic | Restriction |
|----------|-------|-----------|-----------|-------------|
| 吗 ma | PQ marker | ± | ± | polar + wh |
| 吧 ba | TAG/confirm | ± | +forP | polar only |
| 难道 nándào | NANDAO | +forP | ± | polar only |

## Cross-Module Connections

- `Bias.OriginalBias`: ba requires `.forP`; nandao/ma compatible with `.neutral`
- `Bias.ContextualEvidence`: nandao requires `.forP`; ma/ba do not
- `Kernel.nandaoFelicitous`: formal felicity conditions for nandao

-/

namespace Mandarin.QuestionParticles

open Semantics.Questions.Bias (OriginalBias ContextualEvidence)

/-- A Mandarin interrogative particle entry. -/
structure QuestionParticleEntry where
  hanzi : String
  pinyin : String
  gloss : String
  /-- Compatible with polar questions? -/
  polarOk : Bool
  /-- Compatible with declaratives? -/
  declOk : Bool
  /-- Compatible with wh-questions? -/
  whOk : Bool
  /-- Contextual-evidence bias the particle requires, or `none`. -/
  requiresContextualEvidence : Option ContextualEvidence
  /-- Original speaker bias the particle requires, or `none`. -/
  requiresOriginalBias : Option OriginalBias
  deriving Repr, DecidableEq

-- ============================================================================
-- 吗 ma — basic polar question particle
-- ============================================================================

/-- 吗 ma — unmarked polar question particle.
Sentence-final particle that turns a declarative into a yes/no question.
No bias requirements; compatible with all contexts. -/
def ma : QuestionParticleEntry where
  hanzi := "吗"
  pinyin := "ma"
  gloss := "PQ (basic polar question marker)"
  polarOk := true
  declOk := false
  whOk := true
  requiresContextualEvidence := none
  requiresOriginalBias := none

-- ============================================================================
-- 吧 ba — confirmation-seeking / tag particle
-- ============================================================================

/-- 吧 ba — confirmation-seeking particle.
Speaker expects a positive answer and seeks confirmation. Comparable to
English tag questions ("It's raining, isn't it?"). Requires original
speaker bias for p but no evidential bias. -/
def ba : QuestionParticleEntry where
  hanzi := "吧"
  pinyin := "ba"
  gloss := "TAG (confirmation-seeking)"
  polarOk := true
  declOk := false
  whOk := false
  requiresContextualEvidence := none
  requiresOriginalBias := some .forP

-- ============================================================================
-- 难道 nándào — evidential question particle
-- ============================================================================

/-- 难道 nándào — evidential question particle.
Marks that the speaker has encountered unexpected contextual evidence
supporting the prejacent. Compatible with neutral epistemic state
(pure inquiry use, [zheng-2025] ex. 3). -/
def nandao : QuestionParticleEntry where
  hanzi := "难道"
  pinyin := "nándào"
  gloss := "NANDAO (evidential Q-particle)"
  polarOk := true
  declOk := false
  whOk := false
  requiresContextualEvidence := some .forP
  requiresOriginalBias := none

def allQuestionParticles : List QuestionParticleEntry := [ma, ba, nandao]

-- ============================================================================
-- Per-Datum Verification Theorems
-- ============================================================================

-- ma

/-- ma is the unmarked baseline: no bias requirements. -/
theorem ma_no_bias :
    ma.requiresContextualEvidence = none ∧ ma.requiresOriginalBias = none :=
  ⟨rfl, rfl⟩

/-- ma is compatible with wh-questions (unlike ba and nandao). -/
theorem ma_wh_ok : ma.whOk = true := rfl

-- ba

/-- ba requires epistemic bias (speaker expects p). -/
theorem ba_requires_epistemic :
    ba.requiresOriginalBias = some .forP ∧ ba.requiresContextualEvidence = none :=
  ⟨rfl, rfl⟩

/-- ba is restricted to polar questions. -/
theorem ba_polar_only :
    ba.polarOk = true ∧ ba.declOk = false ∧ ba.whOk = false :=
  ⟨rfl, rfl, rfl⟩

-- nandao

/-- nandao is restricted to polar questions ([zheng-2025] ex. 12). -/
theorem nandao_polar_only :
    nandao.polarOk = true ∧ nandao.declOk = false ∧ nandao.whOk = false :=
  ⟨rfl, rfl, rfl⟩

/-- nandao requires evidential but not epistemic bias ([zheng-2025] §2). -/
theorem nandao_bias_profile :
    nandao.requiresContextualEvidence = some .forP ∧ nandao.requiresOriginalBias = none :=
  ⟨rfl, rfl⟩

/-- nandao is compatible with neutral original speaker bias (pure inquiry). -/
theorem nandao_neutral_bias_ok :
    nandao.requiresOriginalBias = none := rfl

-- ============================================================================
-- Cross-Particle Contrast Theorems
-- ============================================================================

/-- The three particles form a bias contrast triple: ma is neutral,
ba requires epistemic, nandao requires evidential. -/
theorem bias_contrast_triple :
    ma.requiresContextualEvidence = none ∧ ma.requiresOriginalBias = none ∧
    ba.requiresContextualEvidence = none ∧ ba.requiresOriginalBias = some .forP ∧
    nandao.requiresContextualEvidence = some .forP ∧ nandao.requiresOriginalBias = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Only ma is compatible with wh-questions. -/
theorem only_ma_allows_wh :
    allQuestionParticles.filter (·.whOk) = [ma] := by decide

/-- No particle requires BOTH contextual-evidence and original-speaker bias. -/
theorem no_double_bias :
    allQuestionParticles.all
      (λ p => !(p.requiresContextualEvidence.isSome && p.requiresOriginalBias.isSome)) = true := by
  decide

end Mandarin.QuestionParticles
