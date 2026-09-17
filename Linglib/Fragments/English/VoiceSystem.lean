import Linglib.Syntax.Voice.Basic

/-!
# English voice

Two voices, the active and the passive; the passive is periphrastic, *be* with the past
participle, the agent demoted to an optional *by*-phrase and the patient the subject.
-/

namespace English

/-- The active and the passive, the passive marked by the auxiliary *be* and the past
participle rather than by an affix. -/
def voices : Finset Voice := {.active, Voice.passive.analytic}

end English
