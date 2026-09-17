import Linglib.Syntax.Voice.Alternation

/-!
# English voice

Two voices, the active basic and the passive derived by *be* and the past participle, the
agent demoted to an optional *by*-phrase and the patient promoted to subject: the passivization
of the valency typology, analytically coded.
-/

open Voice

namespace English

/-- The two voices. -/
inductive Voice where
  | active
  | passive
  deriving DecidableEq, Repr

/-- What each voice does to the transitive construction: the active nothing, the passive the
analytically coded passivization. -/
def Voice.alternation : Voice → ValencyAlternation
  | .active => .refl .np
  | .passive => { passivization with marking := .analytic }

end English
