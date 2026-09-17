import Linglib.Syntax.Voice.Basic

/-!
# English voice system

Two voices, active and passive, the active basic and the passive derived (*be* + past
participle, the agent demoted to an optional *by*-phrase and the patient promoted to subject):
a canonical asymmetrical system as the voice typology of `Syntax/Voice/Basic.lean` reads it.
-/

namespace English.VoiceSystem

/-- The two voices and the role each promotes to pivot. -/
def voices : List Voice.VoiceEntry := [⟨"Active", .agent⟩, ⟨"Passive", .patient⟩]

/-- The passive is derived from the active. -/
def symmetry : Voice.VoiceSystemSymmetry := .asymmetrical

theorem symmetry_asymmetrical : symmetry = .asymmetrical := rfl

theorem voiceCount_eq_two : Voice.voiceCount voices = 2 := rfl

theorem isActivePassive : Voice.isActivePassive voices := by decide

end English.VoiceSystem
