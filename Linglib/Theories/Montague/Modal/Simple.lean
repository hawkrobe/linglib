/-
# Simple (Kripke) Modal Semantics

Simple modal semantics with a primitive accessibility relation.

## Core Idea

Modal operators quantify over accessible worlds:
- □p at w = ∀w'. R(w,w') → p(w')  (p is true at all accessible worlds)
- ◇p at w = ∃w'. R(w,w') ∧ p(w')  (p is true at some accessible world)

## Comparison with Kratzer

| Aspect           | Simple/Kripke         | Kratzer                    |
|------------------|----------------------|----------------------------|
| Accessibility    | Primitive relation R | Derived from backgrounds   |
| Modal flavor     | Different R for each | Different backgrounds      |
| Ordering         | None                 | Ordering source ranks      |
| Flexibility      | Less context-sensitive| Highly context-sensitive  |

## When Simple Suffices

Simple semantics is adequate when:
- We don't need to model context-dependent readings
- The ordering source is empty (no ideals/norms)
- We're studying modal logic properties (reflexivity, transitivity, etc.)

## References

- Kripke, S. (1963). Semantical Considerations on Modal Logic.
- Hughes, G.E. & Cresswell, M.J. (1996). A New Introduction to Modal Logic.
-/

import Linglib.Theories.Montague.Modal.Basic

namespace Montague.Modal

open Montague.Verb.Attitude.Examples

-- ============================================================================
-- The Simple Theory Constructor
-- ============================================================================

/--
Construct a simple modal theory from an accessibility relation.

- Necessity: proposition true at ALL accessible worlds
- Possibility: proposition true at SOME accessible world
-/
def Simple (R : World → World → Bool) : ModalTheory where
  name := "Simple"
  citation := "Kripke 1963"
  eval := fun force p w =>
    let accessible := allWorlds'.filter (R w)
    match force with
    | .necessity => accessible.all p
    | .possibility => accessible.any p

-- ============================================================================
-- Standard Accessibility Relations
-- ============================================================================

/-- Universal accessibility: every world is accessible from every world. -/
def universalR : World → World → Bool := fun _ _ => true

/-- Reflexive accessibility: each world is accessible from itself. -/
def reflexiveR : World → World → Bool := fun w w' => w == w'

/-- Empty accessibility: no world is accessible from any world. -/
def emptyR : World → World → Bool := fun _ _ => false

/-- Sample epistemic accessibility: w0↔w2, w1↔w3. -/
def sampleEpistemicR : World → World → Bool := fun w w' =>
  match w, w' with
  | .w0, .w0 => true | .w0, .w2 => true
  | .w2, .w0 => true | .w2, .w2 => true
  | .w1, .w1 => true | .w1, .w3 => true
  | .w3, .w1 => true | .w3, .w3 => true
  | _, _ => false

/-- Sample deontic accessibility: ideal worlds w0, w2 accessible from anywhere. -/
def sampleDeonticR : World → World → Bool := fun _ w' =>
  w' == .w0 || w' == .w2

-- ============================================================================
-- Instantiated Theories
-- ============================================================================

/-- Simple theory with universal accessibility (S5-like). -/
def SimpleUniversal : ModalTheory := Simple universalR

/-- Simple theory with reflexive-only accessibility (T-like). -/
def SimpleReflexive : ModalTheory := Simple reflexiveR

/-- Simple epistemic theory. -/
def SimpleEpistemic : ModalTheory := Simple sampleEpistemicR

/-- Simple deontic theory. -/
def SimpleDeontic : ModalTheory := Simple sampleDeonticR

-- ============================================================================
-- Key Properties
-- ============================================================================

/-- With universal accessibility, necessity means truth at all worlds. -/
theorem simple_universal_necessity :
    ∀ (p : Proposition) (w : World),
    SimpleUniversal.eval .necessity p w = allWorlds'.all p := by
  intro p w
  unfold SimpleUniversal Simple universalR allWorlds'
  rfl

/-- With universal accessibility, possibility means truth at some world. -/
theorem simple_universal_possibility :
    ∀ (p : Proposition) (w : World),
    SimpleUniversal.eval .possibility p w = allWorlds'.any p := by
  intro p w
  unfold SimpleUniversal Simple universalR allWorlds'
  rfl

/-- With reflexive-only accessibility, □p at w = p w (for concrete propositions). -/
theorem simple_reflexive_necessity_raining :
    ∀ (w : World), SimpleReflexive.eval .necessity raining w = raining w := by
  intro w
  cases w <;> native_decide

theorem simple_reflexive_necessity_johnHome :
    ∀ (w : World), SimpleReflexive.eval .necessity johnHome w = johnHome w := by
  intro w
  cases w <;> native_decide

-- ============================================================================
-- Duality Verification
-- ============================================================================

/-- Helper: duality holds for any list. -/
private theorem list_duality (L : List World) (p : Proposition) :
    (L.all p == !L.any fun w' => !p w') = true := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, List.any_cons, Bool.not_or, Bool.not_not]
    cases p x <;> simp [ih]

/-- Simple theories satisfy modal duality: □p ↔ ¬◇¬p -/
theorem simple_duality (R : World → World → Bool) (p : Proposition) (w : World) :
    (Simple R).dualityHolds p w = true := by
  unfold ModalTheory.dualityHolds Simple ModalTheory.necessity ModalTheory.possibility
  exact list_duality (allWorlds'.filter (R w)) p

-- ============================================================================
-- Examples
-- ============================================================================

-- With universal accessibility, "must it rain" = "does it rain everywhere"
#eval SimpleUniversal.eval .necessity raining .w0  -- false

-- With universal accessibility, "can it rain" = "does it rain somewhere"
#eval SimpleUniversal.eval .possibility raining .w0  -- true

-- With reflexive-only, "must it rain at w0" = "is it raining at w0"
#eval SimpleReflexive.eval .necessity raining .w0  -- true

-- With reflexive-only, "must it rain at w2" = "is it raining at w2"
#eval SimpleReflexive.eval .necessity raining .w2  -- false

-- ============================================================================
-- Consistency Check
-- ============================================================================

/-- Consistency (□p → ◇p) holds with universal accessibility (concrete check). -/
theorem simple_universal_consistent_raining :
    ∀ (w : World), (SimpleUniversal.necessityEntailsPossibility raining w) = true := by
  intro w
  cases w <;> native_decide

theorem simple_universal_consistent_johnHome :
    ∀ (w : World), (SimpleUniversal.necessityEntailsPossibility johnHome w) = true := by
  intro w
  cases w <;> native_decide

theorem simple_universal_consistent_triviallyTrue :
    ∀ (w : World), (SimpleUniversal.necessityEntailsPossibility triviallyTrue w) = true := by
  intro w
  cases w <;> native_decide

end Montague.Modal
