import Linglib.Syntax.Voice.Alternation

/-!
# English voice

The passive is derived from the active by *be* and the past participle, the agent demoted to
an optional *by*-phrase and the patient promoted to subject: the passivization of the valency
typology, analytically coded.
-/

namespace English

/-- The passive: passivization coded by *be* and the past participle. -/
def passive : Voice.ValencyAlternation := { Voice.passivization with marking := .analytic }

end English
