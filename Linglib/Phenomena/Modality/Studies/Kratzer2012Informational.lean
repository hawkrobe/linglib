import Linglib.Theories.Semantics.Modality.Kratzer.Operators
import Linglib.Theories.Semantics.Attitudes.Intensional
import Linglib.Features.Evidentiality

/-!
# Informational Backgrounds — @cite{kratzer-2012} §2.3d

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

namespace Phenomena.Modality.InformationalBackgroundsBridge

open Semantics.Attitudes.Intensional (World)
open Semantics.Modality.Kratzer
open Features.Evidentiality

/-! ## Propositions -/

/-- It is raining. -/
def raining : World → Prop := λ w =>
  match w with | .w0 => True | .w1 => True | .w2 => False | .w3 => False

instance : DecidablePred raining := fun w => by cases w <;> unfold raining <;> infer_instance

/-- The weather report says it is raining. -/
def reportSaysRain : World → Prop := λ w =>
  match w with | .w0 => True | .w1 => False | .w2 => True | .w3 => False

instance : DecidablePred reportSaysRain :=
  fun w => by cases w <;> unfold reportSaysRain <;> infer_instance

/-! ## Conversational backgrounds -/

/-- Informational modal base: accessible worlds are those where the report
    says rain. Accessible = {w0, w2}. -/
def informationalBg : ModalBase World := λ _ => [reportSaysRain]

/-- Reliability assumption: if the report says rain, it's raining.
    This is a conditional proposition (report → rain). -/
def reliabilityAssumption : World → Prop := λ w => reportSaysRain w → raining w

/-- Strong epistemic base: report + reliability. Accessible = {w0} only. -/
def strongEpistemicBg : ModalBase World := λ _ => [reportSaysRain, reliabilityAssumption]

/-! ## Derivation theorems -/

/-- **Report alone doesn't entail rain.** The informational base gives
    accessible worlds {w0, w2}, and raining is false at w2. -/
theorem informational_alone_not_necessity (w : World) :
    ¬ necessity informationalBg emptyBackground raining w := by
  rw [necessity_iff_all]
  intro h
  have hAccW2 : (.w2 : World) ∈ accessibleWorlds informationalBg w := by
    intro p hp
    simp [informationalBg] at hp
    subst hp
    decide
  have hBestW2 : (.w2 : World) ∈ bestWorlds informationalBg emptyBackground w := by
    rw [empty_ordering_emptyBackground]; exact hAccW2
  have := h .w2 hBestW2
  simp [raining] at this

/-- **Report + reliability entails rain.** The strong base gives
    accessible worlds {w0}, and raining is true at w0. -/
theorem with_reliability_necessity (w : World) :
    necessity strongEpistemicBg emptyBackground raining w := by
  rw [necessity_iff_all]
  intro w' hw'
  rw [empty_ordering_emptyBackground] at hw'
  have hReport : reportSaysRain w' :=
    hw' reportSaysRain (by simp [strongEpistemicBg])
  have hRel : reliabilityAssumption w' :=
    hw' reliabilityAssumption (by simp [strongEpistemicBg])
  cases w' with
  | w0 => decide
  | w1 => exact absurd hReport (by decide)
  | w2 => exact absurd (hRel hReport) (by decide)
  | w3 => exact absurd hReport (by decide)

/-- **The informational base is not realistic.** At w1 (it rains but
    the report doesn't say so), w1 ∉ ∩f(w1) because reportSaysRain w1 = false. -/
theorem informational_not_realistic : ¬ isRealistic informationalBg := by
  intro h
  have h1 : reportSaysRain .w1 :=
    h .w1 reportSaysRain (by simp [informationalBg])
  exact absurd h1 (by decide)

/-- **The strong epistemic base is also not realistic.** At w1, the
    report doesn't say rain, so w1 fails the reportSaysRain proposition. -/
theorem strong_epistemic_not_realistic : ¬ isRealistic strongEpistemicBg := by
  intro h
  have h1 : reportSaysRain .w1 :=
    h .w1 reportSaysRain (by simp [strongEpistemicBg])
  exact absurd h1 (by decide)

/-- **Possibility holds under report alone.** Even without reliability,
    rain is possible (w0 is accessible and raining). -/
theorem informational_possibility (w : World) :
    possibility informationalBg emptyBackground raining w := by
  rw [possibility_iff_any]
  refine ⟨.w0, ?_, ?_⟩
  · rw [empty_ordering_emptyBackground]
    intro p hp
    simp [informationalBg] at hp
    subst hp
    decide
  · decide

/-! ## Evidence type bridge -/

/-- The weather report is hearsay evidence. -/
def reportEvidence : EvidentialSource := .hearsay

/-- Hearsay evidence is retrospective (the event precedes the report). -/
theorem report_is_retrospective :
    reportEvidence.toEvidentialPerspective = some .retrospective := rfl

end Phenomena.Modality.InformationalBackgroundsBridge
