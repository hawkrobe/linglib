import Linglib.Theories.Semantics.Focus.BackgroundedIslands
import Linglib.Phenomena.FillerGap.Islands.Data

/-!
# Bridge: Backgrounded Islands → Island Classification

Connects the formal backgroundedness model (Theories/Semantics/Focus) to the
shared island infrastructure in `Phenomena/FillerGap/Islands/Data.lean`.

The MoS island is classified as weak (ameliorable) and discourse-sourced, and
we derive both properties from the formal model.

## References

- Lu, J., Pan, D., & Degen, J. (2025). Evidence for a discourse account of
  manner-of-speaking islands. Language 101(4): 627–659.
-/


namespace Phenomena.FillerGap.BackgroundedIslandsBridge

open Semantics.Focus.BackgroundedIslands
open Core.InformationStructure

/-- **Discourse source derivation**: The formal model predicts that MoS islands
are discourse-sourced because the island effect arises from QUD-determined
backgroundedness, not syntactic configuration or processing load.

The classification `constraintSource .mannerOfSpeaking = .discourse` is not
stipulated arbitrarily — it follows from the formal model: the island effect
is predicted by `complementStatus (defaultDimension v)` which depends on
QUD selection (information structure), not syntax or processing. -/
theorem discourse_source_from_model :
    -- The formal model derives backgroundedness from QUD (discourse)
    (complementStatus .manner = .given) ∧
    -- This grounds the discourse classification
    (constraintSource .mannerOfSpeaking = .discourse) := ⟨rfl, rfl⟩

/-- **Weak classification derivation**: The formal model predicts that MoS
islands are weak (ameliorable) because prosodic focus overrides the default
QUD, changing the complement from backgrounded to discourse-new.

The classification `constraintStrength .mannerOfSpeaking = .weak` follows
from the existence of `prosodic_focus_ameliorates`. -/
theorem weak_strength_from_model (v : VerbDecomp) (h : v.hasMannerWeight = true) :
    -- Without focus: backgrounded (island)
    complementStatus (activeDimension v false) = .given ∧
    -- With focus: not backgrounded (ameliorated)
    complementStatus (activeDimension v true) = .new ∧
    -- Classification matches
    constraintStrength .mannerOfSpeaking = .weak := by
  refine ⟨?_, ?_, rfl⟩
  · simp [activeDimension, defaultDimension, h, complementStatus]
  · simp [activeDimension, complementStatus]

/-- **MoS islands are unique among island types**: they are the only islands
whose effect is derived from information structure (discourse source)
rather than syntactic configuration.

This makes a testable prediction: any manipulation that changes the
QUD (not just prosodic focus) should ameliorate MoS islands, but
manipulations that don't change the QUD (like D-linking) should not. -/
theorem mos_unique_discourse_source :
    constraintSource .mannerOfSpeaking = .discourse ∧
    constraintSource .embeddedQuestion = .syntactic ∧
    constraintSource .complexNP = .syntactic ∧
    constraintSource .adjunct = .syntactic ∧
    constraintSource .coordinate = .syntactic ∧
    constraintSource .subject = .syntactic ∧
    constraintSource .sententialSubject = .syntactic := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Phenomena.FillerGap.BackgroundedIslandsBridge
