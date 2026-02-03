/-
# Update Semantics (Veltman 1996)

Stub for Veltman's Update Semantics, which handles epistemic modals
like "might" via state modification.

## Key Ideas

In Update Semantics:
- Information states are sets of worlds (not assignments)
- Sentences update states by eliminating incompatible worlds
- "Might φ" is a TEST: passes if some φ-worlds remain
- No discourse referents (simpler than DRT/DPL)

## Semantic Type

⟦φ⟧ : State → State
where State = Set World

## Key Innovation

The treatment of epistemic "might":

⟦might φ⟧(s) = s if ⟦φ⟧(s) ≠ ∅, else ∅

"Might φ" tests whether φ is compatible with the current information.

## References

- Veltman, F. (1996). Defaults in Update Semantics. Journal of Philosophical Logic 25:221-261.
-/

import Linglib.Theories.DynamicSemantics.Core.Basic

namespace Theories.DynamicSemantics.UpdateSemantics

open Classical

-- ============================================================================
-- Core Types
-- ============================================================================

/--
Update Semantics state: a set of possible worlds.

Unlike DPL/DRT, no assignment component - US focuses on propositional content.
-/
def State (W : Type*) := Set W

instance {W : Type*} : Membership W (State W) := Set.instMembership
instance {W : Type*} : EmptyCollection (State W) := Set.instEmptyCollection
instance {W : Type*} : HasSubset (State W) := Set.instHasSubset

/--
Update function: how a sentence modifies a state.
-/
def Update (W : Type*) := State W → State W

-- ============================================================================
-- Basic Updates
-- ============================================================================

/--
Propositional update: eliminate worlds where φ fails.

⟦φ⟧(s) = { w ∈ s | φ(w) }
-/
def Update.prop {W : Type*} (φ : W → Bool) : Update W :=
  fun s => { w ∈ s | φ w }

/--
Conjunction: sequential update.

⟦φ ∧ ψ⟧ = ⟦ψ⟧ ∘ ⟦φ⟧
-/
def Update.conj {W : Type*} (φ ψ : Update W) : Update W :=
  fun s => ψ (φ s)

/--
Negation: test and possibly fail.

⟦¬φ⟧(s) = s if ⟦φ⟧(s) = ∅, else ∅

If φ could be true (some worlds survive φ), then ¬φ fails (returns ∅).
If φ is definitely false (no worlds survive), then ¬φ passes (returns s).
-/
def Update.neg {W : Type*} (φ : Update W) : Update W :=
  fun s => if (φ s).Nonempty then ∅ else s

-- ============================================================================
-- Epistemic Modals
-- ============================================================================

/--
Epistemic "might": compatibility test.

⟦might φ⟧(s) = s if ⟦φ⟧(s) ≠ ∅, else ∅

"It might rain" is felicitous iff rain is epistemically possible.
-/
def Update.might {W : Type*} (φ : Update W) : Update W :=
  fun s => if (φ s).Nonempty then s else ∅

/--
Epistemic "must": universal test.

⟦must φ⟧(s) = s if ⟦φ⟧(s) = s, else ∅

"It must rain" requires all worlds have rain.
-/
def Update.must {W : Type*} (φ : Update W) : Update W :=
  fun s => if φ s = s then s else ∅

-- ============================================================================
-- Key Properties
-- ============================================================================

/--
Might is a TEST: it doesn't change the state (if it passes).
-/
theorem might_is_test {W : Type*} (φ : Update W) (s : State W)
    (h : (φ s).Nonempty) :
    Update.might φ s = s := by
  simp [Update.might, h]

/--
Order matters for might.

"It's raining and it might not be raining" is contradictory.
"It might not be raining and it's raining" might pass (then learn it is).
-/
theorem might_order_matters : True := trivial  -- TODO: Formalize

-- ============================================================================
-- Support and Acceptance
-- ============================================================================

/--
State s supports φ iff updating with φ doesn't change s.

s ⊨ φ iff ⟦φ⟧(s) = s
-/
def supports {W : Type*} (s : State W) (φ : Update W) : Prop :=
  φ s = s

/--
State s accepts φ iff updating with φ yields a non-empty state.

s accepts φ iff ⟦φ⟧(s) ≠ ∅
-/
def accepts {W : Type*} (s : State W) (φ : Update W) : Prop :=
  (φ s).Nonempty

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Will Provide

### Core Types
- `State W`: Set of possible worlds
- `Update W`: State transformation function

### Operations
- `prop`: Propositional update
- `conj`: Sequential conjunction
- `neg`: Test-based negation
- `might`: Epistemic possibility
- `must`: Epistemic necessity

### Relations
- `supports`: s ⊨ φ (φ holds throughout s)
- `accepts`: s accepts φ (φ compatible with s)

### Key Properties
- `might_is_test`: Might doesn't change passing states
- Order sensitivity of epistemic modals

## TODO

Full implementation including:
- Defaults and conditionals
- More epistemic operators
- Connection to belief revision
- Comparison with DPL/DRT
-/

end Theories.DynamicSemantics.UpdateSemantics
