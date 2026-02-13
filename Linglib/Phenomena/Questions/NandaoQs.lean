import Linglib.Core.Basic
import Linglib.Theories.IntensionalSemantics.Modal.Kernel
import Linglib.Fragments.Mandarin.QuestionParticles

/-!
# Nandao-Q Empirical Data (Zheng 2026)

Theory-neutral data on Mandarin *nandao*-question felicity. The core finding
is that positive evidential bias is **necessary** for nandao-Q felicity, while
negative epistemic bias is **neither necessary nor sufficient**.

## Key Generalizations

1. Positive evidential bias (contextual evidence for p) → nandao felicitous
2. Epistemic bias alone (prior belief against p, no evidence) → nandao infelicitous
3. Evidence must be **unexpected** relative to prior information state
4. Nandao-Qs can function as pure inquiry (no prior belief required)

## References

- Zheng, A.A. (2026). nandao-Qs: When Surprise Sparks Inquiry. WCCFL 43.
- Alleton, V. (1988). The so-called 'rhetorical interrogation' in Mandarin Chinese.
- Xu, L. (2012/2017). Nandao questions.
-/

namespace Phenomena.Questions.NandaoQs

/-- A nandao-Q felicity datum. -/
structure NandaoDatum where
  /-- Example number from Zheng 2026 -/
  exampleNum : String
  /-- Context description -/
  context : String
  /-- The nandao-Q sentence (pinyin) -/
  sentence : String
  /-- Is there positive evidential bias (contextual evidence for p)? -/
  evidentialBias : Bool
  /-- Is there negative epistemic bias (prior belief against p)? -/
  epistemicBias : Bool
  /-- Is the evidence unexpected? -/
  unexpectedEvidence : Bool
  /-- Is the nandao-Q felicitous? -/
  felicitous : Bool
  deriving Repr, DecidableEq, BEq

-- ════════════════════════════════════════════════════════════════════════════
-- §1 — Rhetorical, Biased, and Pure Inquiry Uses
-- ════════════════════════════════════════════════════════════════════════════

/-- Ex. 1: Rhetorical use. Lee working on Sunday (evidence) contradicts B's
norm that people don't work Sundays (epistemic/deontic bias). -/
def rhetoricalUse : NandaoDatum where
  exampleNum := "1"
  context := "Lee plans to work on Sunday; B thinks people don't work Sundays"
  sentence := "Nandao ta fafeng-le ma? (Is he crazy?)"
  evidentialBias := true
  epistemicBias := true
  unexpectedEvidence := true
  felicitous := true

/-- Ex. 2: Biased question. A believes not-raining; B enters with dripping
raincoat (evidence contradicting belief). -/
def biasedUse : NandaoDatum where
  exampleNum := "2"
  context := "A believes not-raining; B enters with dripping raincoat"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := true
  epistemicBias := true
  unexpectedEvidence := true
  felicitous := true

/-- Ex. 3: Pure inquiry (NOVEL). Same evidence as ex. 2 but A has NO prior
belief about the weather. Nandao is still felicitous. -/
def pureInquiry : NandaoDatum where
  exampleNum := "3"
  context := "A has no weather expectation; B enters with dripping raincoat"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := true
  epistemicBias := false
  unexpectedEvidence := true
  felicitous := true

-- ════════════════════════════════════════════════════════════════════════════
-- §2 — Epistemic Bias Not Sufficient
-- ════════════════════════════════════════════════════════════════════════════

/-- Ex. 4a: Epistemic bias without evidence. Speaker believes room is empty
but has no contextual evidence either way. -/
def epistemicOnly : NandaoDatum where
  exampleNum := "4a"
  context := "Speaker believes room is empty; no contextual evidence"
  sentence := "Nandao wuli you ren? (Are there people in the room?)"
  evidentialBias := false
  epistemicBias := true
  unexpectedEvidence := false
  felicitous := false

-- ════════════════════════════════════════════════════════════════════════════
-- §3 — Evidence Without Epistemic Bias
-- ════════════════════════════════════════════════════════════════════════════

/-- Ex. 5 ctx 1: Evidence + no belief → felicitous. -/
def evidenceNoBelief : NandaoDatum where
  exampleNum := "5.1"
  context := "No prior beliefs; B enters with dripping raincoat"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := true
  epistemicBias := false
  unexpectedEvidence := true
  felicitous := true

/-- Ex. 5 ctx 2: No evidence + no belief → infelicitous. -/
def noEvidenceNoBelief : NandaoDatum where
  exampleNum := "5.2"
  context := "No prior beliefs; B enters normally (no raincoat)"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := false
  epistemicBias := false
  unexpectedEvidence := false
  felicitous := false

/-- Ex. 5 ctx 3: No evidence + epistemic bias → infelicitous. -/
def beliefNoEvidence : NandaoDatum where
  exampleNum := "5.3"
  context := "A thinks it won't rain; B enters normally (no raincoat)"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := false
  epistemicBias := true
  unexpectedEvidence := false
  felicitous := false

-- ════════════════════════════════════════════════════════════════════════════
-- §4 — Unexpectedness Required
-- ════════════════════════════════════════════════════════════════════════════

/-- Ex. 6 ctx 1: Unexpected evidence → felicitous. -/
def unexpectedEvidence_ : NandaoDatum where
  exampleNum := "6.1"
  context := "B doesn't think people work Sundays; A says Lee is working Sunday"
  sentence := "Nandao ta hen.mang ma? (Is he busy?)"
  evidentialBias := true
  epistemicBias := true
  unexpectedEvidence := true
  felicitous := true

/-- Ex. 6 ctx 2: Expected evidence → infelicitous. -/
def expectedEvidence : NandaoDatum where
  exampleNum := "6.2"
  context := "B knows Lee usually works Sundays; A says Lee is working Sunday"
  sentence := "Nandao ta hen.mang ma? (Is he busy?)"
  evidentialBias := true
  epistemicBias := false
  unexpectedEvidence := false
  felicitous := false

-- ════════════════════════════════════════════════════════════════════════════
-- Dataset and Generalization Theorems
-- ════════════════════════════════════════════════════════════════════════════

def allData : List NandaoDatum :=
  [ rhetoricalUse, biasedUse, pureInquiry,
    epistemicOnly,
    evidenceNoBelief, noEvidenceNoBelief, beliefNoEvidence,
    unexpectedEvidence_, expectedEvidence ]

/-- **Generalization 1**: All felicitous nandao-Qs have evidential bias. -/
theorem evidential_bias_necessary :
    (allData.filter (·.felicitous)).all (·.evidentialBias) = true := by native_decide

/-- **Generalization 2**: Some felicitous nandao-Qs lack epistemic bias
(the pure inquiry use). -/
theorem epistemic_bias_not_necessary :
    (allData.filter (λ d => d.felicitous && !d.epistemicBias)).length > 0 := by native_decide

/-- **Generalization 3**: Some infelicitous nandao-Qs have epistemic bias
(epistemic bias is not sufficient). -/
theorem epistemic_bias_not_sufficient :
    (allData.filter (λ d => d.epistemicBias && !d.felicitous)).length > 0 := by native_decide

/-- **Generalization 4**: All felicitous nandao-Qs have unexpected evidence. -/
theorem unexpectedness_necessary :
    (allData.filter (·.felicitous)).all (·.unexpectedEvidence) = true := by native_decide

/-- 9 data points from 6 examples covering 4 conditions. -/
theorem dataset_size : allData.length = 9 := by native_decide

-- ════════════════════════════════════════════════════════════════════════════
-- Bridge: Fragment Entry ↔ Empirical Data ↔ Kernel Theory
-- ════════════════════════════════════════════════════════════════════════════

/-! Bridge theorems connecting the Mandarin nandao Fragment entry to the
empirical generalizations above and to the Kernel-theoretic felicity
predicate `nandaoFelicitous`. These break if the Fragment entry, the
empirical data, or the theory change incompatibly. -/

open Fragments.Mandarin.QuestionParticles (nandao)
open IntensionalSemantics.Modal (Kernel Background nandaoFelicitous)
open IntensionalSemantics.Attitude.Intensional (World)
open Core.Proposition (BProp)

-- Fragment ↔ Data

/-- The nandao Fragment entry's evidential bias requirement matches the
empirical generalization: all felicitous nandao-Qs have evidential bias. -/
theorem fragment_data_evidential :
    nandao.requiresEvidentialBias = true ∧
    (allData.filter (·.felicitous)).all (·.evidentialBias) = true :=
  ⟨rfl, by native_decide⟩

/-- The nandao Fragment entry correctly does NOT require epistemic bias,
matching the empirical finding that some felicitous nandao-Qs lack it. -/
theorem fragment_data_epistemic :
    nandao.requiresEpistemicBias = false ∧
    (allData.filter (λ d => d.felicitous && !d.epistemicBias)).length > 0 :=
  ⟨rfl, by native_decide⟩

-- Theory ↔ Data

/-- Kernel `nandaoFelicitous` entails `evidenceSupports`, connecting the
Theory predicate to the Fragment's `requiresEvidentialBias = true` and
the empirical generalization `evidential_bias_necessary`. -/
theorem kernel_requires_evidence (k : Kernel) (u : Background) (φ : BProp World)
    (h : nandaoFelicitous k u φ = true) :
    k.evidenceSupports φ = true := by
  simp only [nandaoFelicitous] at h
  revert h; cases k.evidenceSupports φ <;> simp

end Phenomena.Questions.NandaoQs
