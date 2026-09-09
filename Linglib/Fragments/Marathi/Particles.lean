import Linglib.Syntax.Category.Particle.Basic

/-!
# Marathi utterance-final particles

The utterance-final discourse particles of Marathi as `Particle` values with their clause-type
distribution. *Bərə* occurs with declaratives, imperatives and wh-interrogatives and never with
polar interrogatives ([deo-2025-bara] §1); its commitment semantics is the subject of
`Studies/Deo2025.lean`. *Na* signals a preference for independent shared commitment
([deo-2023]); only its imperative use is recorded here, from [deo-2025-bara] fn. 5 and fn. 6.

## References

* [deo-2025-bara]
* [deo-2023]
-/

namespace Marathi.Particles

/-- *bərə*: utterance-final, with declaratives, imperatives and wh-interrogatives, never with
polar interrogatives ([deo-2025-bara] §1). -/
def bara : Particle where
  form := "bərə"
  position := some .clauseFinal
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .optional
    | .polar, .matrix => some .excluded
    | .constituent, .matrix => some .optional
    | .imperative, .matrix => some .optional
    | _, _ => none

/-- *na*: utterance-final, augmenting an imperative while leaving the addressee the choice
([deo-2025-bara] fn. 5); its other uses are not recorded. -/
def na : Particle where
  form := "na"
  position := some .clauseFinal
  distribution := fun c e => match c, e with
    | .imperative, .matrix => some .optional
    | _, _ => none

/-- All Marathi utterance-final particles indexed in this file. -/
def allParticles : List Particle := [bara, na]

end Marathi.Particles
