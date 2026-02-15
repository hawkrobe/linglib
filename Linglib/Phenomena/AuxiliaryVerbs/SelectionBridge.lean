import Linglib.Phenomena.AuxiliaryVerbs.Selection
import Linglib.Theories.TruthConditional.Verb.Aspect

/-!
# Bridge: Auxiliary Selection × Vendler Aspect Classes

Connects the auxiliary selection data in
`Phenomena.AuxiliaryVerbs.Selection` to Vendler's aspectual
classification from `Theories.TruthConditional.Verb.Aspect`.

## Predictions verified

- `achievement_typically_unaccusative`: Vendler achievements map to
  unaccusativity
- `achievement_selects_be`: Achievements therefore select *be* in
  split-auxiliary languages

## Known gaps

- Sorace (2000) gradient hierarchy not yet formalized
-/

namespace Phenomena.AuxiliaryVerbs.Selection.Bridge

open TruthConditional.Verb.Aspect (VendlerClass)
open Phenomena.AuxiliaryVerbs.Selection

/-- Vendler's achievement class (telic, punctual) typically corresponds to
    unaccusativity: canonical achievements are change-of-state verbs whose
    subject is a theme/patient. -/
def vendlerClassToTypicalTransitivity : VendlerClass → TransitivityClass
  | .achievement    => .unaccusative
  | .accomplishment => .transitive
  | .activity       => .unergative
  | .state          => .unergative

/-- Achievements are typically unaccusative. -/
theorem achievement_typically_unaccusative :
    vendlerClassToTypicalTransitivity .achievement = .unaccusative := rfl

/-- Achievements typically select *be* in split-auxiliary languages. -/
theorem achievement_selects_be :
    canonicalSelection (vendlerClassToTypicalTransitivity .achievement) = .be := rfl

end Phenomena.AuxiliaryVerbs.Selection.Bridge
