import Linglib.Syntax.Particle.Basic

/-!
# Marathi Utterance-Final Particles
[deo-2025-bara] [deo-2023]

Utterance-final Marathi discourse particles as `Particle` values. The
commitment semantics (dependent vs independent uptake) is analytical
and lives in `Studies/Deo2025.lean`.
-/

namespace Marathi.Particles

/-- *bərə* — utterance-final particle combining with declaratives,
imperatives, and wh-interrogatives, never polar interrogatives
([deo-2025-bara] §1). Conventionally signals that the speaker requests
*dependent* doxastic or preferential commitment uptake tied to an
addressee-benefiting goal ([deo-2025-bara] (20)–(21)); the apparatus
and the preferential-vs-doxastic classification live in
`Studies/Deo2025.lean`. -/
def bara : Particle where
  form := "bərə"
  position := .clauseFinal
  distribution := some
    { declarative := some .optional
      polarInterrogative := some .excluded
      constituentInterrogative := some .optional
      imperative := some .optional }

/-- *na* — utterance-final particle analyzed in [deo-2023] as
signalling preference for *independent* shared commitment (the doxastic
mirror of *bərə*). Only the imperative-augmenting use is attested in
[deo-2025-bara] (fn. 6, p. 392); other cells are unrecorded pending a
[deo-2023] formalization. -/
def na : Particle where
  form := "na"
  position := .clauseFinal
  distribution := some
    { imperative := some .optional }

/-- All Marathi utterance-final particles indexed in this file. -/
def allParticles : List Particle := [bara, na]

end Marathi.Particles
