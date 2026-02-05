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

## Innovation

The treatment of epistemic "might":

⟦might φ⟧(s) = s if ⟦φ⟧(s) ≠ ∅, else ∅

"Might φ" tests whether φ is compatible with the current information.

## References

- Veltman, F. (1996). Defaults in Update Semantics. Journal of Philosophical Logic 25:221-261.
-/

import Linglib.Theories.DynamicSemantics.Core.Basic

namespace Theories.DynamicSemantics.UpdateSemantics

open Classical

-- Core Types

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

-- Basic Updates

/--
Propositional update: eliminate worlds where φ fails.

⟦φ⟧(s) = { w ∈ s | φ(w) }
-/
def Update.prop {W : Type*} (φ : W → Bool) : Update W :=
  λ s => { w ∈ s | φ w }

/--
Conjunction: sequential update.

⟦φ ∧ ψ⟧ = ⟦ψ⟧ ∘ ⟦φ⟧
-/
def Update.conj {W : Type*} (φ ψ : Update W) : Update W :=
  λ s => ψ (φ s)

/--
Negation: test and possibly fail.

⟦¬φ⟧(s) = s if ⟦φ⟧(s) = ∅, else ∅

If φ could be true (some worlds survive φ), then ¬φ fails (returns ∅).
If φ is definitely false (no worlds survive), then ¬φ passes (returns s).
-/
def Update.neg {W : Type*} (φ : Update W) : Update W :=
  λ s => if (φ s).Nonempty then ∅ else s

-- Epistemic Modals

/--
Epistemic "might": compatibility test.

⟦might φ⟧(s) = s if ⟦φ⟧(s) ≠ ∅, else ∅

"It might rain" is felicitous iff rain is epistemically possible.
-/
def Update.might {W : Type*} (φ : Update W) : Update W :=
  λ s => if (φ s).Nonempty then s else ∅

/--
Epistemic "must": universal test.

⟦must φ⟧(s) = s if ⟦φ⟧(s) = s, else ∅

"It must rain" requires all worlds have rain.
-/
def Update.must {W : Type*} (φ : Update W) : Update W :=
  λ s => if φ s = s then s else ∅

-- Key Properties

/--
Might is a TEST: it doesn't change the state (if it passes).
-/
theorem might_is_test {W : Type*} (φ : Update W) (s : State W)
    (h : (φ s).Nonempty) :
    Update.might φ s = s := by
  simp [Update.might, h]

/--
Order matters for epistemic might.

"It's raining and it might not be raining" is contradictory:
after learning rain, the might-not-rain test fails (no ¬rain worlds remain).
But "it might not be raining and it's raining" can succeed:
the might test passes on the initial state, then learning eliminates ¬rain worlds.

TODO: Prove by exhibiting a state with both p-worlds and ¬p-worlds.
Needs `Nontrivial W` (and classical decidability): for empty or singleton W,
no state has both p-worlds and ¬p-worlds, making the second conjunct unsatisfiable.
-/
theorem might_order_matters {W : Type*} :
    ∃ (p : W → Bool) (s : State W),
      Update.conj (Update.prop p) (Update.might (Update.prop λ w => !p w)) s = ∅ ∧
      (Update.conj (Update.might (Update.prop λ w => !p w)) (Update.prop p) s).Nonempty := by
  sorry

-- Support and Acceptance

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

end Theories.DynamicSemantics.UpdateSemantics
