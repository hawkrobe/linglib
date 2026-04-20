import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Core.VoiceSystem

/-!
# English Predicates

Re-exports verbal and adjectival predicate entries.
-/

namespace Fragments.English.Predicates

export Verbal (
  -- Types
  PresupTriggerType ComplementType ControlType VerbEntry
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

/-- English voice system: two-way asymmetrical (active/passive).

    Active is the basic, unmarked form. Passive is morphologically
    derived (BE + past participle) and syntactically marked (agent
    demotion to optional by-phrase, patient promotion to subject). -/
def englishVoiceSystem : Interfaces.VoiceSystemProfile :=
  { language := "English"
    voices := [ ⟨"Active", .agent⟩, ⟨"Passive", .patient⟩ ]
    symmetry := .asymmetrical
    notes := "Canonical asymmetrical system; passive is derived (BE + V-en)" }

theorem english_voice_system_asymmetrical :
    englishVoiceSystem.symmetry = .asymmetrical := rfl

theorem english_voice_count :
    englishVoiceSystem.voiceCount = 2 := rfl

theorem english_is_active_passive :
    englishVoiceSystem.isActivePassive := by decide

end Fragments.English.Predicates
