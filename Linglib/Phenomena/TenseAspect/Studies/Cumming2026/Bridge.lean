import Linglib.Fragments.English.Tense
import Linglib.Fragments.Korean.Evidentials
import Linglib.Fragments.Bulgarian.Evidentials

/-!
# Cumming (2026) Verification Theorems

Verification theorems for the cross-linguistic nonfuture downstream
generalization from Cumming (2026, *L&P* 49:153–175). Paradigm data
lives in Fragment files; this file imports them and proves the empirical
predictions.

## Key Results

1. `nonfuture_downstream`: generic master theorem — any paradigm entry whose
   EP constraint is nonfuture entails T ≤ A (downstream evidence)
2. Per-entry corollaries: one-liner applications of the generic lemma
3. Per-entry `isNonfuture` verification: breaks if EP changed
4. `future_no_downstream`: future entries do not require downstream evidence
5. `korean_te_ney_ep_diverge`: EP and UP factorize independently in Korean

## References

- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175.
-/

namespace Phenomena.TenseAspect.Studies.Cumming2026.Bridge

open Semantics.Tense.Evidential
open Fragments.English.Tense
open Fragments.Korean.Evidentials
open Fragments.Bulgarian.Evidentials

-- ════════════════════════════════════════════════════
-- § 1. Cross-Linguistic Collection
-- ════════════════════════════════════════════════════

/-- All paradigm entries across the three languages. -/
def allParadigms : List TenseEvidentialParadigm :=
  Fragments.English.Tense.allEntries ++
  Fragments.Korean.Evidentials.allEntries ++
  Fragments.Bulgarian.Evidentials.allEntries

/-- Nonfuture paradigm entries (across all languages). -/
def nonfutureParadigms : List TenseEvidentialParadigm :=
  allParadigms.filter (·.isNonfuture)

/-- Future paradigm entries (across all languages). -/
def futureParadigms : List TenseEvidentialParadigm :=
  allParadigms.filter (!·.isNonfuture)

-- ════════════════════════════════════════════════════
-- § 2. Per-Entry isNonfuture Verification
-- ════════════════════════════════════════════════════

/-- English simple past is nonfuture (EP = downstream). -/
theorem simplePast_nonfuture : simplePast.isNonfuture = true := rfl

/-- English present progressive is nonfuture (EP = downstream). -/
theorem presentProg_nonfuture : presentProg.isNonfuture = true := rfl

/-- Korean -te PAST is nonfuture (EP = strictDownstream). -/
theorem tePast_nonfuture : tePast.isNonfuture = true := rfl

/-- Korean -te PRESENT is nonfuture (EP = contemporaneous). -/
theorem tePresent_nonfuture : tePresent.isNonfuture = true := rfl

/-- Korean -ney PAST is nonfuture (EP = strictDownstream). -/
theorem neyPast_nonfuture : neyPast.isNonfuture = true := rfl

/-- Korean -ney PRESENT is nonfuture (EP = contemporaneous). -/
theorem neyPresent_nonfuture : neyPresent.isNonfuture = true := rfl

/-- Bulgarian NFUT + -l is nonfuture (EP = downstream). -/
theorem nfutL_nonfuture : nfutL.isNonfuture = true := rfl

-- ════════════════════════════════════════════════════
-- § 3. Master Downstream Theorem
-- ════════════════════════════════════════════════════

/-- **Generic nonfuture downstream** (Cumming 2026, §5): any paradigm entry
    whose EP constraint is nonfuture entails T ≤ A (downstream evidence).
    Delegates to `EPCondition.nonfuture_implies_downstream`. -/
theorem nonfuture_downstream (p : TenseEvidentialParadigm) (f : EvidentialFrame ℤ)
    (h_nf : p.isNonfuture = true) (h_ep : p.epConstraint f) :
    downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream p.ep f h_nf h_ep

-- ════════════════════════════════════════════════════
-- § 4. Per-Entry Downstream Corollaries
-- ════════════════════════════════════════════════════

/-- English simple past EP entails downstream evidence. -/
theorem simplePast_downstream (f : EvidentialFrame ℤ) :
    simplePast.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .downstream f rfl

/-- English present progressive EP entails downstream evidence. -/
theorem presentProg_downstream (f : EvidentialFrame ℤ) :
    presentProg.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .downstream f rfl

/-- Korean -te PAST EP entails downstream evidence. -/
theorem tePast_downstream (f : EvidentialFrame ℤ) :
    tePast.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .strictDownstream f rfl

/-- Korean -te PRESENT EP entails downstream evidence. -/
theorem tePresent_downstream (f : EvidentialFrame ℤ) :
    tePresent.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .contemporaneous f rfl

/-- Korean -ney PAST EP entails downstream evidence. -/
theorem neyPast_downstream (f : EvidentialFrame ℤ) :
    neyPast.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .strictDownstream f rfl

/-- Korean -ney PRESENT EP entails downstream evidence. -/
theorem neyPresent_downstream (f : EvidentialFrame ℤ) :
    neyPresent.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .contemporaneous f rfl

/-- Bulgarian NFUT + -l EP entails downstream evidence. -/
theorem nfutL_downstream (f : EvidentialFrame ℤ) :
    nfutL.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .downstream f rfl

-- ════════════════════════════════════════════════════
-- § 5. Future Counterexample
-- ════════════════════════════════════════════════════

/-- Future entries do not require downstream evidence: the EP constraint
    is either trivially true (English bare future) or imposes A < T
    (prospective), which is the opposite of T ≤ A. -/
theorem future_no_downstream :
    Fragments.English.Tense.future.epConstraint ⟨⟨10, 10, 0, 5⟩, 0⟩ ∧
    ¬ downstreamEvidence ⟨⟨10, 10, 0, 5⟩, 0⟩ := by
  refine ⟨trivial, ?_⟩
  simp [downstreamEvidence]

-- ════════════════════════════════════════════════════
-- § 6. Korean EP/UP Factorization
-- ════════════════════════════════════════════════════

/-- **Korean -te and -ney EP diverge on the same tense** (Cumming 2026, §4):
    for present tense, -te requires T = A (contemporaneous evidence) while
    -ney requires T = A ∧ T = S (contemporaneous + speech-time present).
    The UP constraints differ: -te has T < S, -ney has T = S. This shows
    EP and UP factorize independently in the morphology. -/
theorem korean_te_ney_ep_diverge :
    -- -te PRES: UP requires T < S (past-shifted evidential perspective)
    (∃ f : EvidentialFrame ℤ,
      tePresent.upConstraint f ∧ ¬ neyPresent.upConstraint f) ∧
    -- -ney PRES: UP requires T = S (speech-time present)
    (∃ f : EvidentialFrame ℤ,
      neyPresent.upConstraint f ∧ ¬ tePresent.upConstraint f) := by
  constructor
  · -- -te PRES with T < S (e.g., T = -1, S = 0, A = -1)
    refine ⟨⟨⟨0, 0, 0, -1⟩, -1⟩, ?_, ?_⟩
    · show (-1 : ℤ) < 0; omega
    · show ¬ ((-1 : ℤ) = 0); omega
  · -- -ney PRES with T = S (e.g., T = 0, S = 0, A = 0)
    refine ⟨⟨⟨0, 0, 0, 0⟩, 0⟩, ?_, ?_⟩
    · show (0 : ℤ) = 0; rfl
    · show ¬ ((0 : ℤ) < 0); omega

end Phenomena.TenseAspect.Studies.Cumming2026.Bridge
