import Linglib.Phenomena.Questions.NandaoQs
import Linglib.Theories.Semantics.Modality.Kernel

/-!
# Bridge: Nandao-Qs × Kernel Theory / Fragment Entry

Connects the nandao-Q felicity data in `Phenomena.Questions.NandaoQs` to
the Mandarin Fragment entry and to the Kernel-theoretic felicity predicate
`nandaoFelicitous` from `Theories.IntensionalSemantics.Modal.Kernel`.

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

namespace Phenomena.Questions.NandaoQs.Bridge

open Phenomena.Questions.NandaoQs
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

end Phenomena.Questions.NandaoQs.Bridge
