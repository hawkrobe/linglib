import Linglib.Theories.Semantics.Verb.Roots.Basic

/-!
# Derivational Operators

@cite{beavers-koontz-garboden-2020} @cite{rappaport-hovav-levin-1998}

A **derivational operator** is a language-specific morphological process
that applies to a root subject to a structural condition on the root's
entailments. The collection of operators that successfully apply to a
root is the root's **orbit** under the inventory.

For Yukatek and other languages, partitioning roots by orbit recovers
language-specific verb-stem classifications (Bohnemeyer's 5-way; Lucy's
3-way salience cut) as *derived* equivalence classes rather than
stipulated enums. This means typological classes become *predictions*
of (root features × operator inventory), not architectural primitives.
-/

namespace Morphology.Derivation

open Semantics.Verb.Roots (Root)

-- ════════════════════════════════════════════════════
-- § 1. Derivational Operators
-- ════════════════════════════════════════════════════

/-- A morphological operator: a name and a structural condition on
    roots specifying when the operator can apply.

    The condition is a Boolean predicate over `Root`, typically phrased
    in terms of B&K-G feature signatures. Whether such conditions are
    descriptively adequate is itself an empirical question — encoding
    them this way exposes the choice. -/
structure DerivOp where
  name : String
  applies : Root → Bool

/-- An inventory: a finite list of derivational operators. -/
abbrev Inventory := List DerivOp

namespace Inventory

/-- The orbit of a root under an inventory: the names of operators
    that apply to it. -/
def orbit (inv : Inventory) (r : Root) : List String :=
  (inv.filter (·.applies r)).map (·.name)

/-- Two roots are inventory-equivalent iff they have the same orbit. -/
def equivalent (inv : Inventory) (r₁ r₂ : Root) : Bool :=
  inv.all (λ op => op.applies r₁ == op.applies r₂)

end Inventory

end Morphology.Derivation
