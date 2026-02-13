import Linglib.Theories.Minimalism.Core.VerbalDecomposition

/-!
# Fission (Distributed Morphology)

Fission is a postsyntactic operation that splits a single terminal node
into two morphological exponents. This module provides the generic
framework; language-specific instantiations live in `Fragments/`.

The key parameters of any Fission rule:
1. **Structural context**: What verb-head configuration licenses Fission?
2. **Person condition**: Which person categories trigger Fission?
3. **Realization**: How is the split terminal spelled out?

## References

- Halle, M. & A. Marantz (1993). Distributed Morphology and the
  pieces of inflection. In *The View from Building 20*, 111–176.
- Noyer, R. (1997). *Features, Positions and Affixes in Autonomous
  Morphological Structure*. Garland.
- Muñoz Pérez, C. (2026). Stylistic applicatives. *Glossa* 11(1).
-/

namespace Minimalism.Morphology

open Minimalism

-- ============================================================================
-- § 1: Fission Output
-- ============================================================================

/-- The result of Fission: two clitic positions. -/
structure FissionOutput where
  /-- Cl₁: bears person features -/
  cl1Form : String
  /-- Cl₂: bears case features -/
  cl2Form : String
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- § 2: Fission Rule (Parameterized)
-- ============================================================================

/-- A Fission rule parameterized over a person category type.

    Language-specific modules instantiate this with their own
    person type, structural context, and realization function. -/
structure FissionRule (Person : Type) where
  /-- Structural context check (e.g., inchoative = vGO ∧ vBE). -/
  contextOk : List VerbHead → Bool
  /-- Person/number condition (e.g., [+PART, +SING]). -/
  personOk : Person → Bool
  /-- Realization: map person category to the two clitic forms. -/
  realize : Person → FissionOutput

-- ============================================================================
-- § 3: Generic Fission Application
-- ============================================================================

/-- Apply Fission given a rule, a person category, and a verb-head list.
    Returns `none` if either the structural or person condition fails. -/
def applyFission {Person : Type} (rule : FissionRule Person)
    (p : Person) (heads : List VerbHead) : Option FissionOutput :=
  if rule.contextOk heads && rule.personOk p then
    some (rule.realize p)
  else
    none

-- ============================================================================
-- § 4: PF Marking Condition
-- ============================================================================

/-- A PF well-formedness condition: checks whether a list of overt
    clitic forms satisfies a language-specific phonological requirement
    (e.g., anticausative marking in Spanish). -/
structure PFMarkingCondition where
  isSatisfied : List String → Bool

/-- When Fission produces a clitic that satisfies a PF condition,
    another overt marker (e.g., SE) may be optional. -/
def fissionSatisfiesPF {Person : Type} (rule : FissionRule Person)
    (pf : PFMarkingCondition) (p : Person) (heads : List VerbHead) : Bool :=
  match applyFission rule p heads with
  | some output => pf.isSatisfied [output.cl1Form]
  | none => false

end Minimalism.Morphology
