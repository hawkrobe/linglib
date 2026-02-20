import Linglib.Theories.Semantics.Questions.QParticleLayer

/-!
# Q-Particle Typology Bridge (Dayal 2025)

Cross-linguistic Q-particle data classified by left-peripheral layer
(Dayal 2025: §1.3). This file imports `QParticleLayer` from Theories/
and connects Q-particle distribution to the three-point left-peripheral
structure [SAP [PerspP [CP ...]]].

The theory-neutral data (clause typing, declarative questions, shiftiness,
conjunct/disjunct marking) lives in `Phenomena.Questions.Typology`.

## References

- Dayal, V. (2025). The Interrogative Left Periphery. Linguistic Inquiry 56(4).
- Bhatt, R. & V. Dayal (2020). Polar question particles: Hindi-Urdu kya:.
- Sauerland, U. & K. Yatsushiro (2017). Two noises in the head.
-/

namespace Phenomena.Questions.TypologyBridge

open Semantics.Questions (QParticleLayer)

-- ============================================================================
-- Q-particle typology (Dayal 2025: §1.3)
-- ============================================================================

/-- A Q-particle datum. -/
structure QParticleDatum where
  language : String
  form : String
  layer : QParticleLayer
  /-- Appears in matrix questions? -/
  inMatrix : Bool
  /-- Appears in subordinated interrogatives? -/
  inSubordinated : Bool
  /-- Appears in quasi-subordinated interrogatives? -/
  inQuasiSub : Bool
  /-- Appears in quotations? -/
  inQuotation : Bool
  deriving Repr

-- Japanese ka: clause-typing particle (CP)
-- Obligatory in subordinated, optional in matrix (Dayal 2025: §1.1, §1.3)
def japanese_ka : QParticleDatum :=
  { language := "Japanese", form := "ka"
  , layer := .cp
  , inMatrix := true, inSubordinated := true
  , inQuasiSub := true, inQuotation := true }

-- Hindi-Urdu kya:: polar question particle (PQP, PerspP layer)
-- Matrix + quasi-subordinated, NOT subordinated (Bhatt & Dayal 2020)
def hindi_urdu_kya : QParticleDatum :=
  { language := "Hindi-Urdu", form := "kya:"
  , layer := .perspP
  , inMatrix := true, inSubordinated := false
  , inQuasiSub := true, inQuotation := false }

-- Japanese kke: meta question particle (MQP, SAP layer)
-- Matrix + quotation only (Sauerland & Yatsushiro 2017)
def japanese_kke : QParticleDatum :=
  { language := "Japanese", form := "kke"
  , layer := .sap
  , inMatrix := true, inSubordinated := false
  , inQuasiSub := false, inQuotation := true }

-- English quick/quickly: MQP-like adverb (SAP layer)
-- Only matrix questions, ungrammatical in embedded position (Dayal 2025: (19))
def english_quick : QParticleDatum :=
  { language := "English", form := "quick/quickly"
  , layer := .sap
  , inMatrix := true, inSubordinated := false
  , inQuasiSub := false, inQuotation := false }

def allQParticleData : List QParticleDatum :=
  [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick]

-- Key generalization: distribution follows from left-peripheral layer
-- CP particles can appear wherever CP appears (everywhere)
-- PerspP particles where PerspP appears (matrix + quasi-sub)
-- SAP particles where SAP appears (matrix + quotation)

/-- CP-layer particles appear in subordinated position. -/
theorem cp_particles_in_subordination :
    ∀ d ∈ allQParticleData,
      d.layer = .cp → d.inSubordinated = true := by
  intro d hd _
  simp [allQParticleData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp_all [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick]

/-- PerspP-layer particles do NOT appear in subordinated position. -/
theorem perspP_particles_not_in_subordination :
    ∀ d ∈ allQParticleData,
      d.layer = .perspP → d.inSubordinated = false := by
  intro d hd _
  simp [allQParticleData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp_all [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick]

/-- SAP-layer particles do NOT appear in quasi-subordinated position. -/
theorem sap_particles_not_in_quasi_sub :
    ∀ d ∈ allQParticleData,
      d.layer = .sap → d.inQuasiSub = false := by
  intro d hd _
  simp [allQParticleData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp_all [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick]

end Phenomena.Questions.TypologyBridge
