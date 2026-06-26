import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Syntax.Voice.Basic

/-!
# English Predicates

Re-exports verbal and adjectival predicate entries.
-/

namespace English.Predicates

export Verbal (
  -- Types (PresupTriggerType/ComplementType/ControlType are root-namespace now)
  VerbEntry
  Preferential
  -- Functions
  allVerbs
)

export Adjectival (
  AdjectivalPredicateEntry
  allEntries
)

-- ============================================================================
-- Voice System Profile
-- ============================================================================

/-! ### English voice system

    Two-way asymmetrical (active/passive). Active is the basic, unmarked
    form. Passive is morphologically derived (BE + past participle) and
    syntactically marked (agent demotion to optional by-phrase, patient
    promotion to subject). Canonical asymmetrical system; passive is
    derived (BE + V-en). -/
namespace VoiceSystem

def voices : List Voice.VoiceEntry := [ ⟨"Active", .agent⟩, ⟨"Passive", .patient⟩ ]

def symmetry : Voice.VoiceSystemSymmetry := .asymmetrical

end VoiceSystem

theorem english_voice_system_asymmetrical :
    VoiceSystem.symmetry = .asymmetrical := rfl

theorem english_voice_count :
    Voice.voiceCount VoiceSystem.voices = 2 := rfl

theorem english_is_active_passive :
    Voice.isActivePassive VoiceSystem.voices := by decide

end English.Predicates
