import Linglib.Theories.IntensionalSemantics.Modal.Kratzer
import Linglib.Core.Evidence

/-!
# Informational Backgrounds — Kratzer 2012 §2.3d

Epistemic modals with an **informational** (potentially non-realistic) modal base.

A weather report provides evidence for rain, but the report can be wrong:
the proposition "the report says rain" does not guarantee rain is actual.
This makes the informational background non-realistic — the actual world
may not be in ∩f(w) if the report is wrong at that world.

| World | Raining | ReportSaysRain | Notes               |
|-------|---------|----------------|---------------------|
| w0    | yes     | yes            | Report correct      |
| w1    | yes     | no             | Rain, report missed |
| w2    | no      | yes            | Dry, report wrong   |
| w3    | no      | no             | Both correct        |

Reference: Kratzer, A. (2012). Modals and Conditionals. OUP. Ch. 2 §2.3d.
-/

namespace Phenomena.Modality.InformationalBackgrounds

open IntensionalSemantics.Attitude.Intensional (World)
open IntensionalSemantics.Modal.Kratzer
open Core.Evidence

/-! ## Propositions -/

/-- It is raining. -/
def raining : BProp World := λ w =>
  match w with | .w0 => true | .w1 => true | .w2 => false | .w3 => false

/-- The weather report says it is raining. -/
def reportSaysRain : BProp World := λ w =>
  match w with | .w0 => true | .w1 => false | .w2 => true | .w3 => false

/-! ## Conversational backgrounds -/

/-- Informational modal base: accessible worlds are those where the report
    says rain. Accessible = {w0, w2}. -/
def informationalBg : ModalBase := λ _ => [reportSaysRain]

/-- Reliability assumption: if the report says rain, it's raining.
    This is a conditional proposition (report → rain). -/
def reliabilityAssumption : BProp World := λ w => !reportSaysRain w || raining w

/-- Strong epistemic base: report + reliability. Accessible = {w0} only. -/
def strongEpistemicBg : ModalBase := λ _ => [reportSaysRain, reliabilityAssumption]

/-! ## Derivation theorems -/

/-- **Report alone doesn't entail rain.** The informational base gives
    accessible worlds {w0, w2}, and raining is false at w2. -/
theorem informational_alone_not_necessity (w : World) :
    necessity informationalBg emptyBackground raining w = false := by
  cases w <;> native_decide

/-- **Report + reliability entails rain.** The strong base gives
    accessible worlds {w0}, and raining is true at w0. -/
theorem with_reliability_necessity (w : World) :
    necessity strongEpistemicBg emptyBackground raining w = true := by
  cases w <;> native_decide

/-- **The informational base is not realistic.** At w1 (it rains but
    the report doesn't say so), w1 ∉ ∩f(w1) because reportSaysRain w1 = false. -/
theorem informational_not_realistic : ¬ isRealistic informationalBg := by
  intro h
  have h1 : (informationalBg .w1).all (λ p => p .w1) = true := h .w1
  -- informationalBg .w1 = [reportSaysRain], and reportSaysRain .w1 = false
  exact absurd h1 (by decide)

/-- **The strong epistemic base is also not realistic.** At w1, the
    report doesn't say rain, so w1 fails the reportSaysRain proposition. -/
theorem strong_epistemic_not_realistic : ¬ isRealistic strongEpistemicBg := by
  intro h
  have h1 : (strongEpistemicBg .w1).all (λ p => p .w1) = true := h .w1
  exact absurd h1 (by decide)

/-- **Possibility holds under report alone.** Even without reliability,
    rain is possible (w0 is accessible and raining). -/
theorem informational_possibility (w : World) :
    possibility informationalBg emptyBackground raining w = true := by
  cases w <;> native_decide

/-! ## Evidence type bridge -/

/-- The weather report is hearsay evidence. -/
def reportEvidence : EvidentialSource := .hearsay

/-- Hearsay evidence is retrospective (the event precedes the report). -/
theorem report_is_retrospective :
    reportEvidence.toEvidentialPerspective = .retrospective := rfl

end Phenomena.Modality.InformationalBackgrounds
