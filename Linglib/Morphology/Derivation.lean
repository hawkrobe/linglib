import Linglib.Semantics.Lexical.Roots.Basic

/-!
# Morphological Operators and Root Classification

[lucy-1994] [bohnemeyer-2004]

A **morphological operator** is a language-specific process
(derivational or diagnostic-inflectional) that applies to a root
subject to a structural condition on the root's entailments. The
collection of operators that successfully apply to a root is the
root's **applicability profile** under the inventory.

Partitioning roots by applicability profile recovers language-specific
verb-stem classifications ([bohnemeyer-2004]'s 5-way Yukatek cut;
[lucy-1994]'s 3-way salience cut) as *derived* equivalence classes
rather than stipulated enums. Typological classes thereby become
*predictions* of (root features × operator inventory), not
architectural primitives.
-/

namespace Morphology.Derivation

/-! ### Operators and inventories -/

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

/-- An inventory: a finite list of morphological operators. -/
abbrev Inventory := List DerivOp

namespace Inventory

/-- The names of the operators in the inventory that apply to a root —
    the root's applicability profile. -/
def applicableNames (inv : Inventory) (r : Root) : List String :=
  (inv.filter (fun op => decide (op.applies r))).map (·.name)

/-- Two roots are inventory-equivalent iff every operator in the
    inventory either applies to both or neither. -/
def Equivalent (inv : Inventory) (r₁ r₂ : Root) : Prop :=
  ∀ op ∈ inv, op.applies r₁ ↔ op.applies r₂

instance (inv : Inventory) (r₁ r₂ : Root) : Decidable (Equivalent inv r₁ r₂) := by
  unfold Equivalent; infer_instance

end Inventory

end Morphology.Derivation
