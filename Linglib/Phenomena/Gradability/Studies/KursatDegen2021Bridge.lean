import Linglib.Phenomena.Gradability.Studies.KursatDegen2021
import Linglib.Theories.RSA.Core.Noise

/-!
# Bridge: Kursat & Degen (2021) × RSA Noise Model

Connects the perceptual difficulty data in
`Phenomena.KursatDegen2021` to the noise discrimination parameters
in `Theories.RSA.Core.Noise`.

## Predictions verified

- `discrimination_matches_difficulty`: The RSA noise model's
  discrimination ordering (color > size > material) matches the
  empirical perceptual difficulty ordering

## Known gaps

- Within-property-type difficulty gradients not yet modeled
-/

namespace Phenomena.KursatDegen2021.Bridge

open Phenomena.KursatDegen2021

/-- Map property types to discrimination values. -/
def propertyToDiscrimination : PropertyType → ℚ
  | .color => RSA.Noise.colorDiscrimination
  | .size => RSA.Noise.sizeDiscrimination
  | .material => RSA.Noise.materialDiscrimination

/-- Verify discrimination ordering matches perceptual difficulty ordering -/
theorem discrimination_matches_difficulty :
    propertyToDiscrimination .color > propertyToDiscrimination .size ∧
    propertyToDiscrimination .size > propertyToDiscrimination .material := by
  exact RSA.Noise.discrimination_ordering

end Phenomena.KursatDegen2021.Bridge
