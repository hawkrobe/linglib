import Linglib.Phenomena.Politeness.Studies.MachinoEtAl2025
import Linglib.Theories.Semantics.Lexical.Adjective.Theory

/-!
# Bridge: Machino et al. (2025) × Adjective Theory

Connects the cross-cultural intensifier data in
`Phenomena.Politeness.Studies.MachinoEtAl2025` to the modifier
direction classification from `Theories.TruthConditional.Adjective.Theory`.

## Predictions verified

- `modifierDirection`: Maps each culture × modifier pair to its
  theoretic direction (amplifier/downtoner)
- Cross-cultural divergence on "quite" verified

## Known gaps

- No formalization of the culture-specific RSA weights (ω_social, ω_info)
-/

namespace Phenomena.Politeness.Studies.MachinoEtAl2025.Bridge

open TruthConditional.Adjective (ModifierDirection)
open Phenomena.Politeness.Studies.MachinoEtAl2025

/-- Culture-specific modifier direction.
    Key finding: "quite" differs across varieties. -/
def modifierDirection : Culture → Modifier → ModifierDirection
  | _, .slightly  => .downtoner
  | _, .kindOf    => .downtoner
  | .americanEnglish, .quite => .amplifier   -- AmE: "quite good" ≈ "very good"
  | .britishEnglish, .quite  => .downtoner   -- BrE: "quite good" ≈ "fairly good"
  | _, .very      => .amplifier
  | _, .extremely => .amplifier

-- Verify cross-cultural difference for "quite"
#guard modifierDirection .americanEnglish .quite == .amplifier
#guard modifierDirection .britishEnglish .quite == .downtoner

-- Verify universal directions
#guard modifierDirection .americanEnglish .slightly == .downtoner
#guard modifierDirection .britishEnglish .slightly == .downtoner
#guard modifierDirection .americanEnglish .very == .amplifier
#guard modifierDirection .britishEnglish .very == .amplifier

end Phenomena.Politeness.Studies.MachinoEtAl2025.Bridge
