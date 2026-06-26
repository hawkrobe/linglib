import Linglib.Syntax.Voice.Basic

/-!
# Mam Voice System Profile (theory-neutral)

Theory-neutral typological profile of the Mam voice system.

The Minimalist `VoiceHead`, `ClauseSpine`, and `MamDirHead` apparatus
that previously lived in this file (=(y)a' analysis, antipassive)
moved to:

- `Studies/ElkinsTorrenceBrown2026.lean` — primary
  anchor for the Minimalist treatment of =(y)a' / oblique extraction
  ([elkins-torrence-brown-2026]); also houses the antipassive
  Voice apparatus from [scott-2023] §2.5.4.1.
- Cross-Studies consumer:
  `Studies/Scott2023.lean` imports the Minimalist
  Mam Voice from ETB2026 to compare φ-Agree and oblique-Agree pipelines.

This Fragment file retains only `VoiceSystem.voices` / `VoiceSystem.symmetry` —
a theory-neutral voice inventory any framework can consume via the
`Voice.*` queries.

**Variety note**: SJO Mam (San Juan Ostuncalco, [elkins-torrence-brown-2026])
and SJA Mam (San Juan Atitán, [scott-2023]) are distinct varieties.
The voice system profile abstracts over the variety distinction.
-/

namespace Mam

namespace VoiceSystem

/-! ### Mam voice system: three-way asymmetrical (agentive / passive / antipassive)

Unlike Toba Batak's symmetrical pivot system, Mam's agentive voice
is the basic form (phase head, overt agent) and passive/antipassive
are derived (non-phase, implicit agent). Voice does not determine
pivot for extraction — instead, Voice carries [uOblique] which
conditions extraction morphology (=(y)a').

Agentive is basic (phase head); passive/antipassive are derived.
Antipassive demotes object to oblique, subject gets ABS ([scott-2023]).
Voice data from SJA ([scott-2023]) and SJO ([elkins-torrence-brown-2026]). -/

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
