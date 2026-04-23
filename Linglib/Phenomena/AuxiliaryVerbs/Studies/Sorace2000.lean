import Linglib.Phenomena.AuxiliaryVerbs.Selection
import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect

/-!
# Sorace (2000): Auxiliary Selection × Vendler Aspect Classes
@cite{sorace-2000}

Connects the auxiliary selection data in
`Phenomena.AuxiliaryVerbs.Selection` to Vendler's aspectual
classification from `Theories.Semantics.Tense.Aspect.LexicalAspect`.

## Known gaps

- @cite{sorace-2000}'s gradient Auxiliary Selection Hierarchy is
  not yet formalized — `vendlerClassToTypicalTransitivity` is a
  flat lookup, not a derivation from proto-role entailments. A
  principled version would build the mapping out of
  `Theories/Semantics/Verb/EntailmentProfile.lean` so that, e.g.,
  the achievement → unaccusative arrow falls out of
  `changeOfState ∧ ¬volition`. TODO when EntailmentProfile-based
  unaccusativity diagnostics are wired up.
-/

namespace Phenomena.AuxiliaryVerbs.Studies.Sorace2000

open Core.Verbs
open Phenomena.AuxiliaryVerbs.Selection

/-- Vendler's achievement class (telic, punctual) typically corresponds to
    unaccusativity: canonical achievements are change-of-state verbs whose
    subject is a theme/patient.

    TODO: derive this from proto-role entailments in
    `Theories/Semantics/Verb/EntailmentProfile.lean` (cf. file docstring).
    Today this is a stipulated lookup; the rfl-trivial theorems that
    chained it with `canonicalSelection` have been dropped because they
    just unpacked two lookup tables. -/
def vendlerClassToTypicalTransitivity : VendlerClass → TransitivityClass
  | .achievement    => .unaccusative
  | .accomplishment => .transitive
  | .activity       => .unergative
  | .state          => .unergative
  | .semelfactive   => .unergative

end Phenomena.AuxiliaryVerbs.Studies.Sorace2000
