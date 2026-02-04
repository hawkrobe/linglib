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

-- The Simple Theory Constructor

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

-- Standard Accessibility Relations

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

-- Instantiated Theories

/-- Simple theory with universal accessibility (S5-like). -/
def SimpleUniversal : ModalTheory := Simple universalR

/-- Simple theory with reflexive-only accessibility (T-like). -/
def SimpleReflexive : ModalTheory := Simple reflexiveR

/-- Simple epistemic theory. -/
def SimpleEpistemic : ModalTheory := Simple sampleEpistemicR

/-- Simple deontic theory. -/
def SimpleDeontic : ModalTheory := Simple sampleDeonticR

-- Key Properties

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

-- Duality Verification

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

-- Examples

-- With universal accessibility, "must it rain" = "does it rain everywhere"
#eval SimpleUniversal.eval .necessity raining .w0  -- false

-- With universal accessibility, "can it rain" = "does it rain somewhere"
#eval SimpleUniversal.eval .possibility raining .w0  -- true

-- With reflexive-only, "must it rain at w0" = "is it raining at w0"
#eval SimpleReflexive.eval .necessity raining .w0  -- true

-- With reflexive-only, "must it rain at w2" = "is it raining at w2"
#eval SimpleReflexive.eval .necessity raining .w2  -- false

-- Consistency Check

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

-- PART: Connecting to isNormal (Completing the Derivation Chain)

/-!
## Normality: Simple Theories are Normal Modal Logics

A modal theory is **normal** if duality holds universally:
  ∀p w, □p(w) ↔ ¬◇¬p(w)

We've proven `simple_duality` for each (p, w). Now we lift this to `isNormal`.
-/

/-- All Simple theories are normal modal logics.

This completes the derivation chain:
  simple_duality (per p, w) → simple_isNormal (universal property)
-/
theorem simple_isNormal (R : World → World → Bool) : (Simple R).isNormal :=
  fun p w => simple_duality R p w

/-- Corollary: SimpleUniversal is normal. -/
theorem simpleUniversal_isNormal : SimpleUniversal.isNormal :=
  simple_isNormal universalR

/-- Corollary: SimpleReflexive is normal. -/
theorem simpleReflexive_isNormal : SimpleReflexive.isNormal :=
  simple_isNormal reflexiveR

-- PART: Kripke Correspondence Theory (Kripke 1963)

/-!
## Kripke Correspondence: R Properties ↔ Modal Axioms

The fundamental insight of Kripke (1963) is that properties of the accessibility
relation R correspond to modal axioms:

| R Property    | Modal Axiom | Name |
|---------------|-------------|------|
| Reflexive     | □p → p      | T    |
| Serial        | □p → ◇p     | D    |
| Transitive    | □p → □□p    | 4    |
| Symmetric     | p → □◇p     | B    |
| Euclidean     | ◇p → □◇p    | 5    |

These are **derivations from first principles**: the axioms FOLLOW from R properties.
-/

-- ----------------------------------------------------------------------------
-- T Axiom: □p → p (Reflexivity)
-- ----------------------------------------------------------------------------

/-- Reflexivity of R: every world accesses itself. -/
def isReflexive (R : World → World → Bool) : Prop :=
  ∀ w : World, R w w = true

/-- T Axiom: If □p at w, then p at w.

**Derivation**: If R is reflexive, then w ∈ accessible(w).
Since □p means p holds at ALL accessible worlds, p holds at w.
-/
theorem T_axiom_from_reflexivity (R : World → World → Bool) (hRefl : isReflexive R)
    (p : Proposition) (w : World)
    (hNec : (Simple R).eval .necessity p w = true) : p w = true := by
  -- □p means: (accessible worlds).all p = true
  -- Since R is reflexive, w is in accessible worlds
  -- Therefore p w = true
  unfold Simple at hNec
  simp only at hNec
  have hWIn : R w w = true := hRefl w
  have hWFiltered : w ∈ allWorlds'.filter (R w) := by
    simp only [List.mem_filter, allWorlds']
    constructor
    · -- w ∈ allWorlds
      cases w <;> simp [allWorlds]
    · exact hWIn
  exact List.all_eq_true.mp hNec w hWFiltered

/-- Reflexive accessibility gives T axiom: □p → p -/
theorem reflexive_implies_T (R : World → World → Bool) (hRefl : isReflexive R) :
    ∀ (p : Proposition) (w : World),
    (Simple R).eval .necessity p w = true → p w = true :=
  fun p w => T_axiom_from_reflexivity R hRefl p w

-- ----------------------------------------------------------------------------
-- D Axiom: □p → ◇p (Seriality)
-- ----------------------------------------------------------------------------

/-- Seriality of R: every world accesses at least one world. -/
def isSerial (R : World → World → Bool) : Prop :=
  ∀ w : World, ∃ w' : World, R w w' = true

/-- D Axiom: If □p at w, then ◇p at w.

**Derivation**: If R is serial, accessible(w) is non-empty.
□p means p holds at ALL accessible worlds.
◇p means p holds at SOME accessible world.
If all satisfy p and there exists at least one, then some satisfies p.
-/
theorem D_axiom_from_seriality (R : World → World → Bool) (hSerial : isSerial R)
    (p : Proposition) (w : World)
    (hNec : (Simple R).eval .necessity p w = true) :
    (Simple R).eval .possibility p w = true := by
  unfold Simple at hNec ⊢
  simp only at hNec ⊢
  -- Get a witness from seriality
  obtain ⟨w', hW'Acc⟩ := hSerial w
  -- w' is in the filtered list
  have hW'In : w' ∈ allWorlds'.filter (R w) := by
    simp only [List.mem_filter, allWorlds']
    constructor
    · cases w' <;> simp [allWorlds]
    · exact hW'Acc
  -- Since all accessible worlds satisfy p, w' satisfies p
  have hPw' : p w' = true := List.all_eq_true.mp hNec w' hW'In
  -- Therefore some accessible world satisfies p
  exact List.any_eq_true.mpr ⟨w', hW'In, hPw'⟩

/-- Serial accessibility gives D axiom: □p → ◇p -/
theorem serial_implies_D (R : World → World → Bool) (hSerial : isSerial R) :
    ∀ (p : Proposition) (w : World),
    (Simple R).eval .necessity p w = true → (Simple R).eval .possibility p w = true :=
  fun p w => D_axiom_from_seriality R hSerial p w

-- ----------------------------------------------------------------------------
-- Consistency as Corollary of D
-- ----------------------------------------------------------------------------

/-- Universal R is serial (trivially: all worlds accessible). -/
theorem universalR_isSerial : isSerial universalR := fun w => ⟨w, rfl⟩

/-- Reflexive R is serial (every world accesses itself). -/
theorem reflexiveR_isSerial : isSerial reflexiveR := fun w => ⟨w, by
  unfold reflexiveR
  cases w <;> rfl⟩

/-- Universal accessibility gives consistency (D axiom). -/
theorem simple_universal_isConsistent_from_D :
    ∀ (p : Proposition) (w : World),
    SimpleUniversal.necessityEntailsPossibility p w = true := by
  intro p w
  unfold ModalTheory.necessityEntailsPossibility ModalTheory.necessity ModalTheory.possibility
  -- Either □p is false (LHS of implication), or □p → ◇p by D axiom
  cases hNec : SimpleUniversal.eval .necessity p w with
  | false =>
      -- If necessity is false, the implication !false || _ = true
      simp only [SimpleUniversal, Simple, Bool.not_false, Bool.true_or]
  | true =>
      simp only [Bool.not_true, Bool.false_or]
      exact D_axiom_from_seriality universalR universalR_isSerial p w hNec

-- ----------------------------------------------------------------------------
-- K Axiom: □(p → q) → (□p → □q) (Distribution)
-- ----------------------------------------------------------------------------

/-- Material implication as a proposition. -/
def pImpl (p q : Proposition) : Proposition := fun w => !p w || q w

/-- K Axiom: Necessity distributes over implication.

**Derivation**: □(p → q) means (p → q) holds at all accessible worlds.
□p means p holds at all accessible worlds.
Combined: q holds at all accessible worlds = □q.

This is the fundamental axiom of normal modal logic - it holds for ANY R.
-/
theorem K_axiom (R : World → World → Bool) (p q : Proposition) (w : World)
    (hImpl : (Simple R).eval .necessity (pImpl p q) w = true)
    (hP : (Simple R).eval .necessity p w = true) :
    (Simple R).eval .necessity q w = true := by
  unfold Simple at hImpl hP ⊢
  simp only at hImpl hP ⊢
  -- Need to show: all accessible worlds satisfy q
  apply List.all_eq_true.mpr
  intro w' hW'Acc
  -- w' is accessible, so p → q holds at w' and p holds at w'
  have hImplW' : pImpl p q w' = true := List.all_eq_true.mp hImpl w' hW'Acc
  have hPW' : p w' = true := List.all_eq_true.mp hP w' hW'Acc
  -- Therefore q holds at w'
  unfold pImpl at hImplW'
  cases hp : p w' with
  | false => simp [hp] at hPW'
  | true => simp [hp] at hImplW'; exact hImplW'

/-- K axiom holds for all Simple theories (no conditions on R needed). -/
theorem simple_K_axiom (R : World → World → Bool) :
    ∀ (p q : Proposition) (w : World),
    (Simple R).eval .necessity (pImpl p q) w = true →
    (Simple R).eval .necessity p w = true →
    (Simple R).eval .necessity q w = true :=
  fun p q w => K_axiom R p q w

-- Summary: What We've Derived

/-!
## Summary: Kripke Correspondence Theorems

We have now DERIVED the following from first principles:

### Unconditional (hold for any R)
- `simple_duality`: □p ↔ ¬◇¬p (duality)
- `simple_isNormal`: Simple theories are normal
- `simple_K_axiom`: □(p → q) → (□p → □q) (K axiom / distribution)

### Conditional on R Properties
- `reflexive_implies_T`: Reflexive R → (□p → p)
- `serial_implies_D`: Serial R → (□p → ◇p)

### Derived Properties
- `simple_universal_isConsistent_from_D`: Universal R is consistent (via seriality)

These are the core results of Kripke (1963), proven constructively.
-/

end Montague.Modal
