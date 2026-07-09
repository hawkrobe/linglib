import Linglib.Syntax.Voice.Basic

/-!
# Mam Voice System Profile

Theory-neutral typological profile of the Mam voice system: a voice
inventory any framework can consume via the `Voice.*` queries. Unlike
Toba Batak's symmetrical pivot system, Mam is three-way asymmetrical —
agentive voice is basic (a phase head, overt agent), while passive and
antipassive are derived (non-phase, implicit agent); the antipassive
demotes the object to oblique and the subject takes ABS ([scott-2023]).
Voice does not determine the pivot for extraction; instead it carries
[uOblique], which conditions the extraction morphology =(y)a'.

## Main declarations

* `Mam.VoiceSystem.voices`: the agentive, passive, and antipassive
  voice entries.
* `Mam.VoiceSystem.symmetry`: the asymmetrical classification.

## Implementation notes

The Minimalist `Voice.Head`, `ClauseSpine`, and `MamDirHead` apparatus
(=(y)a' analysis, antipassive) that previously lived here now lives in
`Studies/ElkinsTorrenceBrown2026.lean` — the primary anchor for the
Minimalist treatment of =(y)a' / oblique extraction
([elkins-torrence-brown-2026]), which also houses the antipassive Voice
apparatus from [scott-2023] §2.5.4.1; `Studies/Scott2023.lean` imports
that Mam Voice to compare φ-Agree and oblique-Agree pipelines. SJO Mam
(San Juan Ostuncalco, [elkins-torrence-brown-2026]) and SJA Mam (San
Juan Atitán, [scott-2023]) are distinct varieties; this profile
abstracts over the distinction.
-/

namespace Mam

namespace VoiceSystem

/-! ### Voice inventory -/

/-- The voices of Mam: agentive (basic), passive, antipassive. -/
def voices : List Voice.VoiceEntry :=
  [ ⟨"Agentive Voice", .agent⟩, ⟨"Passive Voice", .patient⟩,
    ⟨"Antipassive Voice", .agent⟩ ]

/-- Mam is asymmetrical — agentive is the basic voice. -/
def symmetry : Voice.VoiceSystemSymmetry := .asymmetrical

end VoiceSystem

theorem mam_voice_system_asymmetrical :
    Mam.VoiceSystem.symmetry = .asymmetrical := rfl

theorem mam_voice_count :
    Voice.voiceCount Mam.VoiceSystem.voices = 3 := rfl

/-- Mam is not a simple active/passive system — it also has antipassive. -/
theorem mam_not_simple_active_passive :
    ¬ Voice.isActivePassive Mam.VoiceSystem.voices := by decide

theorem mam_no_oblique_pivots :
    ¬ Voice.distinguishesObliques Mam.VoiceSystem.voices := by decide

end Mam
