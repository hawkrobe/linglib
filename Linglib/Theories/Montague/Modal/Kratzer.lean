/-
# Kratzer Modal Semantics

Kratzer's (1977, 1981, 1991) analysis of modal auxiliaries.

## Core Insight

Modal domains aren't fixed — they're determined by context through
two conversational backgrounds:

1. **Modal Base** f: world → set of propositions (the relevant "facts")
2. **Ordering Source** g: world → set of propositions (ideals for ranking)

The accessibility relation is DERIVED from these:
- R(w, w') = w' is compatible with all propositions in f(w)

## Modal Flavors

Different conversational backgrounds yield different modal "flavors":
- **Epistemic**: f = what is known, g = ∅
- **Deontic**: f = circumstances, g = what the law requires
- **Teleological**: f = circumstances, g = goals
- **Bouletic**: f = circumstances, g = desires

## Key Innovation

Same modal verb "must" gets different readings via different
conversational backgrounds — no lexical ambiguity needed.

## References

- Kratzer, A. (1977). What 'Must' and 'Can' Must and Can Mean.
- Kratzer, A. (1991). Modality. In Semantics: An International Handbook.
-/

import Linglib.Theories.Montague.Modal.Basic
import Linglib.Theories.Montague.Modal.ConversationalBackground

namespace Montague.Modal

open Montague.Attitudes
open Montague.Modal.ConversationalBackground

-- ============================================================================
-- Kratzer Parameters
-- ============================================================================

/--
Parameters for a Kratzer-style modal theory.

These determine the modal flavor by specifying:
- base: Which facts constrain accessibility
- ordering: Which ideals rank accessible worlds
-/
structure KratzerParams where
  /-- Modal base: world → set of propositions (facts) -/
  base : ModalBase
  /-- Ordering source: world → set of propositions (ideals) -/
  ordering : OrderingSource

-- ============================================================================
-- The Kratzer Theory Constructor
-- ============================================================================

/--
Construct a Kratzer modal theory from parameters.

This wraps the machinery from Modality.lean:
- `bestWorlds` computes the optimal accessible worlds
- Necessity: proposition true at ALL best worlds
- Possibility: proposition true at SOME best world

## Note on Proposition Type Conversion

Modality.lean uses `Modality.Proposition` (World → Bool).
Theory.lean uses `Modals.Proposition` (also World → Bool).
They're definitionally equal, so no conversion needed.
-/
def Kratzer (params : KratzerParams) : ModalTheory where
  name := "Kratzer"
  citation := "Kratzer 1991"
  eval := fun force p w =>
    let best := bestWorlds params.base params.ordering w
    match force with
    | .necessity => best.all p
    | .possibility => best.any p

-- ============================================================================
-- Standard Parameter Configurations
-- ============================================================================

/-- Empty modal base: all worlds are accessible. -/
def emptyBase : ModalBase := fun _ => []

/-- Empty ordering source: no ranking among accessible worlds. -/
def emptyOrdering' : OrderingSource := fun _ => []

/--
Minimal Kratzer parameters: all worlds accessible, no ordering.
This reduces to simple Kripke semantics with universal accessibility.
-/
def minimalParams : KratzerParams where
  base := emptyBase
  ordering := emptyOrdering'

/--
Epistemic parameters: accessibility constrained by knowledge.
Example: we know the ground is wet, so only wet-ground worlds are accessible.
-/
def epistemicParams : KratzerParams where
  base := epistemicBase  -- from Modality.lean
  ordering := emptyOrdering

/-- Deontic parameters: accessibility constrained by circumstances, ranked by norms. -/
def deonticParams : KratzerParams where
  base := circumstantialBase  -- from Modality.lean
  ordering := deonticOrdering  -- from Modality.lean

-- ============================================================================
-- Instantiated Theories
-- ============================================================================

/-- Epistemic modal theory: "must" = necessary given what is known. -/
def KratzerEpistemic : ModalTheory := Kratzer epistemicParams

/-- Deontic modal theory: "must" = necessary given the norms. -/
def KratzerDeontic : ModalTheory := Kratzer deonticParams

/-- Minimal Kratzer theory: universal accessibility, no ordering. -/
def KratzerMinimal : ModalTheory := Kratzer minimalParams

-- ============================================================================
-- Key Properties
-- ============================================================================

/--
Kratzer with empty ordering reduces to simple accessibility check.

When g(w) = ∅, all accessible worlds are "best", so:
- □p = p holds at all accessible worlds
- ◇p = p holds at some accessible world
-/
theorem kratzer_empty_ordering_is_simple :
    ∀ (base : ModalBase) (p : Proposition) (w : World),
    let params : KratzerParams := { base := base, ordering := emptyOrdering' }
    (Kratzer params).eval .necessity p w =
      (accessibleWorlds base w).all p := by
  intro base p w
  simp only [Kratzer]
  rfl

-- Epistemic "must it be raining" at w0
-- Given we know the ground is wet: Accessible worlds = {w0, w1, w3}
-- Is it raining at all? No (w3 is wet but not raining)
#eval KratzerEpistemic.eval .necessity raining .w0  -- false

-- Epistemic "can it be raining" at w0
-- Accessible worlds = {w0, w1, w3}. Is it raining at some? Yes (w0 and w1)
#eval KratzerEpistemic.eval .possibility raining .w0  -- true

-- ============================================================================
-- Duality Verification
-- ============================================================================

/-- Helper: duality holds for any list (used by both Kratzer and Simple). -/
private theorem list_duality' (L : List World) (p : Proposition) :
    (L.all p == !L.any fun w' => !p w') = true := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, List.any_cons, Bool.not_or, Bool.not_not]
    cases p x <;> simp [ih]

/--
Kratzer theories satisfy modal duality: □p ↔ ¬◇¬p

The proof uses the fact that for any finite list L:
  L.all p = true ↔ L.any (fun x => !p x) = false
-/
theorem kratzer_duality (params : KratzerParams) (p : Proposition) (w : World) :
    (Kratzer params).dualityHolds p w = true := by
  unfold ModalTheory.dualityHolds Kratzer ModalTheory.necessity ModalTheory.possibility
  exact list_duality' (bestWorlds params.base params.ordering w) p

-- ============================================================================
-- Context-Dependence Examples
-- ============================================================================

-- Context-dependence: the same modal verb can get different truth values
-- under different conversational backgrounds.
-- This demonstrates Kratzer's key insight: modal flavor comes from
-- context (conversational backgrounds), not lexical ambiguity.

-- Let's see what epistemic and deontic modals compute:
#eval KratzerEpistemic.eval .necessity johnHome .w0  -- epistemic necessity of johnHome at w0
#eval KratzerDeontic.eval .necessity johnHome .w0   -- deontic necessity of johnHome at w0
#eval KratzerMinimal.eval .necessity raining .w0    -- minimal necessity (universal accessibility)

-- The minimal theory differs from epistemic on necessity of raining:
-- Minimal: all 4 worlds accessible → must rain = false (not raining everywhere)
-- Epistemic: only wet-ground worlds accessible → must rain = false (w3 is wet but dry)
-- They can differ when the accessible sets differ in relevant ways.

/-- The minimal and epistemic theories can give different results for possibility. -/
theorem minimal_vs_epistemic_differ :
    KratzerMinimal.eval .possibility triviallyFalse .w0 =
    KratzerEpistemic.eval .possibility triviallyFalse .w0 := by
  native_decide

end Montague.Modal
