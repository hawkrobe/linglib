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

    The condition is a propositional predicate over `Root`, typically
    phrased in terms of B&K-G feature signatures, with a bundled
    `DecidablePred` instance so the predicate can drive `List.filter`
    and other computational uses. Whether such conditions are
    descriptively adequate is itself an empirical question — encoding
    them this way exposes the choice. -/
structure DerivOp where
  name : String
  applies : Root → Prop
  decApplies : DecidablePred applies

attribute [instance] DerivOp.decApplies

/-- An inventory: a finite list of derivational operators. -/
abbrev Inventory := List DerivOp

namespace Inventory

/-- The orbit of a root under an inventory: the names of operators
    that apply to it. -/
def orbit (inv : Inventory) (r : Root) : List String :=
  (inv.filter (fun op => decide (op.applies r))).map (·.name)

/-- Two roots are inventory-equivalent iff every operator in the
    inventory either applies to both or neither. -/
def Equivalent (inv : Inventory) (r₁ r₂ : Root) : Prop :=
  ∀ op ∈ inv, op.applies r₁ ↔ op.applies r₂

instance (inv : Inventory) (r₁ r₂ : Root) : Decidable (Equivalent inv r₁ r₂) := by
  unfold Equivalent; infer_instance

end Inventory

end Morphology.Derivation
