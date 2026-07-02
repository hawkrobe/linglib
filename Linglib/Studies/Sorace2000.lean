import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
import Linglib.Features.Aktionsart

/-!
# Sorace (2000): Auxiliary Selection × Vendler Aspect Classes
[sorace-2000]

Connects the auxiliary selection substrate in
`AuxiliarySelection` to Vendler's aspectual
classification from `Features.Aktionsart`.

## Known gaps

- [sorace-2000]'s gradient Auxiliary Selection Hierarchy is
  not yet formalized — `vendlerClassToTypicalTransitivity` is a
  flat lookup, not a derivation from proto-role entailments. A
  principled version would build the mapping out of
  `Features/EntailmentProfile.lean` so that, e.g.,
  the achievement → unaccusative arrow falls out of
  `changeOfState ∧ ¬volition`. TODO when EntailmentProfile-based
  unaccusativity diagnostics are wired up.
-/

namespace Sorace2000

open Features
open ArgumentStructure.AuxiliarySelection

/-- Vendler's achievement class (telic, punctual) typically corresponds to
    unaccusativity: canonical achievements are change-of-state verbs whose
    subject is a theme/patient.

    TODO: derive this from proto-role entailments in
    `Features/EntailmentProfile.lean` (cf. file docstring).
    Today this is a stipulated lookup; the rfl-trivial theorems that
    chained it with `canonicalSelection` have been dropped because they
    just unpacked two lookup tables. -/
def vendlerClassToTypicalTransitivity : VendlerClass → TransitivityClass
  | .achievement    => .unaccusative
  | .accomplishment => .transitive
  | .activity       => .unergative
  | .state          => .unergative
  | .semelfactive   => .unergative

/-- A have-only perfect system agrees with the canonical split exactly on
    the classes that do not select *be* ([sorace-2000]): English, with its
    have-only perfect, diverges from Italian precisely on the BE-selecting
    classes (*has arrived* vs *è arrivato*). -/
theorem haveOnly_agrees_with_canonical_iff (c : TransitivityClass) :
    SelectionRule.haveOnly.selects true c = some (canonicalSelection c) ↔
      ¬ SelectsBe c := by
  cases c <;> decide

end Sorace2000
