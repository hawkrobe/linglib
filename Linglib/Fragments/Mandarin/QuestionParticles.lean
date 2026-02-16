import Linglib.Theories.Semantics.Modality.BiasedPQ
import Linglib.Phenomena.Questions.Typology

/-!
# Mandarin Question Particles

Lexical entries for Mandarin interrogative particles with distributional
properties and bias profiles.

## Particles

| Particle | Gloss | Evidential | Epistemic | Layer | Restriction |
|----------|-------|-----------|-----------|-------|-------------|
| 吗 ma | PQ marker | ± | ± | CP | polar + wh |
| 吧 ba | TAG/confirm | ± | +forP | PerspP | polar only |
| 难道 nándào | NANDAO | +forP | ± | PerspP | polar only |

## Cross-Module Connections

- `BiasedPQ.OriginalBias`: ba requires `.forP`; nandao/ma compatible with `.neutral`
- `BiasedPQ.ContextualEvidence`: nandao requires `.forP`; ma/ba do not
- `Typology.QParticleLayer`: ma is CP, ba and nandao are PerspP
- `Kernel.nandaoFelicitous`: formal felicity conditions for nandao

## References

- Zheng, A.A. (2026). nandao-Qs: When Surprise Sparks Inquiry. WCCFL 43.
- Li, C.N. & Thompson, S.A. (1981). Mandarin Chinese: A Functional Reference Grammar.
- Chu, C.C. (1998). A Discourse Grammar of Mandarin Chinese.
-/

namespace Fragments.Mandarin.QuestionParticles

open IntensionalSemantics.Modal.BiasedPQ (OriginalBias ContextualEvidence)
open Phenomena.Questions.Typology (QParticleLayer)

/-- A Mandarin interrogative particle entry. -/
structure QuestionParticleEntry where
  hanzi : String
  pinyin : String
  gloss : String
  /-- Left-peripheral layer (approximate for adverbial particles). -/
  layer : QParticleLayer
  /-- Compatible with polar questions? -/
  polarOk : Bool
  /-- Compatible with declaratives? -/
  declOk : Bool
  /-- Compatible with wh-questions? -/
  whOk : Bool
  /-- Requires positive evidential bias (contextual evidence for p)? -/
  requiresEvidentialBias : Bool
  /-- Requires negative epistemic bias (prior belief against p)? -/
  requiresEpistemicBias : Bool
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- 吗 ma — basic polar question particle
-- ============================================================================

/-- 吗 ma — unmarked polar question particle (Li & Thompson 1981).
Sentence-final particle that turns a declarative into a yes/no question.
No bias requirements; compatible with all contexts. CP-layer: appears in
matrix, subordinated, and quasi-subordinated positions. -/
def ma : QuestionParticleEntry where
  hanzi := "吗"
  pinyin := "ma"
  gloss := "PQ (basic polar question marker)"
  layer := .cp
  polarOk := true
  declOk := false
  whOk := true
  requiresEvidentialBias := false
  requiresEpistemicBias := false

-- ============================================================================
-- 吧 ba — confirmation-seeking / tag particle
-- ============================================================================

/-- 吧 ba — confirmation-seeking particle (Chu 1998, Li & Thompson 1981).
Speaker expects a positive answer and seeks confirmation. Comparable to
English tag questions ("It's raining, isn't it?"). Requires original
speaker bias for p but no evidential bias. -/
def ba : QuestionParticleEntry where
  hanzi := "吧"
  pinyin := "ba"
  gloss := "TAG (confirmation-seeking)"
  layer := .perspP
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := false
  requiresEpistemicBias := true

-- ============================================================================
-- 难道 nándào — evidential question particle
-- ============================================================================

/-- 难道 nándào — evidential question particle (Zheng 2026).
Marks that the speaker has encountered unexpected contextual evidence
supporting the prejacent. Compatible with neutral epistemic state
(pure inquiry use, Zheng 2026 ex. 3). -/
def nandao : QuestionParticleEntry where
  hanzi := "难道"
  pinyin := "nándào"
  gloss := "NANDAO (evidential Q-particle)"
  layer := .perspP
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := true
  requiresEpistemicBias := false

def allQuestionParticles : List QuestionParticleEntry := [ma, ba, nandao]

-- ============================================================================
-- Per-Datum Verification Theorems
-- ============================================================================

-- ma

/-- ma is the unmarked baseline: no bias requirements. -/
theorem ma_no_bias :
    ma.requiresEvidentialBias = false ∧ ma.requiresEpistemicBias = false :=
  ⟨rfl, rfl⟩

/-- ma is CP-layer: widest distribution. -/
theorem ma_layer : ma.layer = .cp := rfl

/-- ma is compatible with wh-questions (unlike ba and nandao). -/
theorem ma_wh_ok : ma.whOk = true := rfl

-- ba

/-- ba requires epistemic bias (speaker expects p). -/
theorem ba_requires_epistemic :
    ba.requiresEpistemicBias = true ∧ ba.requiresEvidentialBias = false :=
  ⟨rfl, rfl⟩

/-- ba is restricted to polar questions. -/
theorem ba_polar_only :
    ba.polarOk = true ∧ ba.declOk = false ∧ ba.whOk = false :=
  ⟨rfl, rfl, rfl⟩

-- nandao

/-- nandao is restricted to polar questions (Zheng 2026 ex. 12). -/
theorem nandao_polar_only :
    nandao.polarOk = true ∧ nandao.declOk = false ∧ nandao.whOk = false :=
  ⟨rfl, rfl, rfl⟩

/-- nandao requires evidential but not epistemic bias (Zheng 2026 §2). -/
theorem nandao_bias_profile :
    nandao.requiresEvidentialBias = true ∧ nandao.requiresEpistemicBias = false :=
  ⟨rfl, rfl⟩

/-- nandao is compatible with neutral original speaker bias (pure inquiry). -/
theorem nandao_neutral_bias_ok :
    nandao.requiresEpistemicBias = false := rfl

/-- nandao is at the PerspP layer. -/
theorem nandao_layer : nandao.layer = .perspP := rfl

-- ============================================================================
-- Cross-Particle Contrast Theorems
-- ============================================================================

/-- The three particles form a bias contrast triple: ma is neutral,
ba requires epistemic, nandao requires evidential. -/
theorem bias_contrast_triple :
    ma.requiresEvidentialBias = false ∧ ma.requiresEpistemicBias = false ∧
    ba.requiresEvidentialBias = false ∧ ba.requiresEpistemicBias = true ∧
    nandao.requiresEvidentialBias = true ∧ nandao.requiresEpistemicBias = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Only ma is compatible with wh-questions. -/
theorem only_ma_allows_wh :
    allQuestionParticles.filter (·.whOk) = [ma] := by native_decide

/-- ba and nandao are PerspP; ma is CP (wider distribution). -/
theorem layer_contrast :
    ma.layer = .cp ∧ ba.layer = .perspP ∧ nandao.layer = .perspP :=
  ⟨rfl, rfl, rfl⟩

/-- No particle requires BOTH evidential and epistemic bias. -/
theorem no_double_bias :
    allQuestionParticles.all
      (λ p => !(p.requiresEvidentialBias && p.requiresEpistemicBias)) = true := by
  native_decide

end Fragments.Mandarin.QuestionParticles
