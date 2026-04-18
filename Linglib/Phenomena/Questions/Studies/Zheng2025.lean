import Linglib.Core.Lexical.Word
import Linglib.Fragments.Mandarin.QuestionParticles
import Linglib.Theories.Semantics.Modality.Kernel

/-!
# Zheng (2025): Nandao-Q Felicity @cite{zheng-2025}

Mandarin *nandao*-question felicity. Self-contained study file:
empirical data, the Mandarin Fragment entry, and bridges to the
Kernel-theoretic felicity predicate `nandaoFelicitous`.

The core finding is that positive evidential bias is **necessary** for
nandao-Q felicity, while negative epistemic bias is **neither necessary
nor sufficient**.

## Key Generalizations

1. Positive evidential bias (contextual evidence for p) → nandao felicitous
2. Epistemic bias alone (prior belief against p, no evidence) → nandao infelicitous
3. Evidence must be **unexpected** relative to prior information state
4. Nandao-Qs can function as pure inquiry (no prior belief required)

## Predictions verified

- `fragment_data_evidential`: Fragment entry's evidential bias requirement
  matches the empirical generalization
- `fragment_data_epistemic`: Fragment entry correctly does not require
  epistemic bias
- `kernel_requires_evidence`: Kernel `nandaoFelicitous` entails
  `evidenceSupports`

## Known gaps

- No formalization of the unexpectedness requirement in the Kernel theory
-/

namespace Phenomena.Questions.Studies.Zheng2025

-- ════════════════════════════════════════════════════════════════════════════
-- §1 — Empirical Data
-- ════════════════════════════════════════════════════════════════════════════

/-- A nandao-Q felicity datum. -/
structure NandaoDatum where
  /-- Example number from @cite{zheng-2025} -/
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
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════════════════════════════
-- §1.1 — Rhetorical, Biased, and Pure Inquiry Uses
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
-- §1.2 — Epistemic Bias Not Sufficient
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
-- §1.3 — Evidence Without Epistemic Bias
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
-- §1.4 — Unexpectedness Required
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
-- §1.5 — Dataset and Generalization Theorems
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
-- §2 — Bridges: Fragment ↔ Data, Theory ↔ Data
-- ════════════════════════════════════════════════════════════════════════════

open Fragments.Mandarin.QuestionParticles (nandao)
open Semantics.Modality (Kernel Background nandaoFelicitous)
open Semantics.Attitudes.Intensional (World)

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

/-- Kernel `nandaoFelicitous` entails `evidenceSupports`, connecting the
Theory predicate to the Fragment's `requiresEvidentialBias = true` and
the empirical generalization `evidential_bias_necessary`. -/
theorem kernel_requires_evidence (k : Kernel) (u : Background) (φ : (World → Bool))
    (h : nandaoFelicitous k u φ) :
    k.evidenceSupports φ :=
  h.1

end Phenomena.Questions.Studies.Zheng2025
