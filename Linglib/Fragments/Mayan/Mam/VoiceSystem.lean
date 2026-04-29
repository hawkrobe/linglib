import Linglib.Phenomena.ArgumentStructure.VoiceSystem

/-!
# Mam Voice System Profile (theory-neutral)

Theory-neutral typological profile of the Mam voice system.

The Minimalist `VoiceHead`, `ClauseSpine`, and `MamDirHead` apparatus
that previously lived in this file (=(y)a' analysis, antipassive)
moved to:

- `Phenomena/FillerGap/Studies/ElkinsTorrenceBrown2026.lean` — primary
  anchor for the Minimalist treatment of =(y)a' / oblique extraction
  (@cite{elkins-torrence-brown-2026}); also houses the antipassive
  Voice apparatus from @cite{scott-2023} §2.5.4.1.
- Cross-Studies consumer:
  `Phenomena/Agreement/Studies/Scott2023.lean` imports the Minimalist
  Mam Voice from ETB2026 to compare φ-Agree and oblique-Agree pipelines.

This Fragment file retains only `mamVoiceSystem : VoiceSystemProfile` —
a theory-neutral typology profile any framework can consume.

**Variety note**: SJO Mam (San Juan Ostuncalco, @cite{elkins-torrence-brown-2026})
and SJA Mam (San Juan Atitán, @cite{scott-2023}) are distinct varieties.
The voice system profile abstracts over the variety distinction.
-/

namespace Fragments.Mayan.Mam

/-- Mam voice system: three-way asymmetrical (agentive / passive / antipassive).

    Unlike Toba Batak's symmetrical pivot system, Mam's agentive voice
    is the basic form (phase head, overt agent) and passive/antipassive
    are derived (non-phase, implicit agent). Voice does not determine
    pivot for extraction — instead, Voice carries [uOblique] which
    conditions extraction morphology (=(y)a'). -/
def mamVoiceSystem : Interfaces.VoiceSystemProfile :=
  { language := "Mam"
    voices := [ ⟨"Agentive Voice", .agent⟩, ⟨"Passive Voice", .patient⟩,
                ⟨"Antipassive Voice", .agent⟩ ]
    symmetry := .asymmetrical
    notes := "Agentive is basic (phase head); passive/antipassive are derived. " ++
             "Antipassive demotes object to oblique, subject gets ABS (Scott 2023). " ++
             "Voice data from SJA (Scott 2023) and SJO (Elkins et al. 2026)" }

theorem mam_voice_system_asymmetrical :
    mamVoiceSystem.symmetry = .asymmetrical := rfl

theorem mam_voice_count :
    mamVoiceSystem.voiceCount = 3 := rfl

/-- Mam is not a simple active/passive system — it also has antipassive. -/
theorem mam_not_simple_active_passive :
    ¬ mamVoiceSystem.isActivePassive := by decide

theorem mam_no_oblique_pivots :
    ¬ mamVoiceSystem.distinguishesObliques := by decide

end Fragments.Mayan.Mam
