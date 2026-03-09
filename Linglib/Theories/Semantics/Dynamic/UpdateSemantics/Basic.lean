import Linglib.Theories.Semantics.Dynamic.Core.CCP

/-!
# Update Semantics
@cite{veltman-1996}

In Update Semantics:
- Information states are sets of worlds (not assignments)
- Sentences update states by eliminating incompatible worlds
- "Might φ" is a TEST: passes if some φ-worlds remain
- No discourse referents (simpler than DRT/DPL)

⟦φ⟧ : State → State where State = Set World

-/

namespace Semantics.Dynamic.UpdateSemantics

open Classical

/--
Update Semantics state: a set of possible worlds.

Unlike DPL/DRT, no assignment component - US focuses on propositional content.
-/
abbrev State (W : Type*) := Set W

/--
Update function: how a sentence modifies a state.
-/
def Update (W : Type*) := State W → State W

/--
Propositional update: eliminate worlds where φ fails.

⟦φ⟧(s) = { w ∈ s | φ(w) }
-/
def Update.prop {W : Type*} (φ : W → Bool) : Update W :=
  λ s => { w ∈ s | φ w }

/--
Conjunction: sequential update.

⟦φ ∧ ψ⟧ = ⟦ψ⟧ ∘ ⟦φ⟧

Delegates to `Core.CCP.seq`.
-/
def Update.conj {W : Type*} (φ ψ : Update W) : Update W :=
  Core.CCP.seq φ ψ

/--
Negation: test and possibly fail.

⟦¬φ⟧(s) = s if ⟦φ⟧(s) = ∅, else ∅

Delegates to `Core.CCP.neg`.
-/
noncomputable def Update.neg {W : Type*} (φ : Update W) : Update W :=
  Core.CCP.neg φ

/--
Epistemic "might": compatibility test.

⟦might φ⟧(s) = s if ⟦φ⟧(s) ≠ ∅, else ∅

Delegates to `Core.CCP.might`.
-/
noncomputable def Update.might {W : Type*} (φ : Update W) : Update W :=
  Core.CCP.might φ

/--
Epistemic "must": universal test.

⟦must φ⟧(s) = s if ⟦φ⟧(s) = s, else ∅

Delegates to `Core.CCP.must`.
-/
noncomputable def Update.must {W : Type*} (φ : Update W) : Update W :=
  Core.CCP.must φ

/--
Might is a TEST: it doesn't change the state (if it passes).
-/
theorem might_is_test {W : Type*} (φ : Update W) (s : State W)
    (h : (φ s).Nonempty) :
    Update.might φ s = s := by
  simp [Update.might, Core.CCP.might, h]

/--
Order matters for epistemic might.

"It's raining and it might not be raining" is contradictory:
after learning rain, the might-not-rain test fails (no ¬rain worlds remain).
But "it might not be raining and it's raining" can succeed:
the might test passes on the initial state, then learning eliminates ¬rain worlds.

Requires `Nontrivial W`: for empty or singleton W, no state has both
p-worlds and ¬p-worlds, making the second conjunct unsatisfiable. -/
theorem might_order_matters {W : Type*} [Nontrivial W] :
    ∃ (p : W → Bool) (s : State W),
      Update.conj (Update.prop p) (Update.might (Update.prop λ w => !p w)) s = ∅ ∧
      (Update.conj (Update.might (Update.prop λ w => !p w)) (Update.prop p) s).Nonempty := by
  obtain ⟨w₁, w₂, hne⟩ := exists_pair_ne W
  let p : W → Bool := fun w => decide (w = w₁)
  use p, {w₁, w₂}
  have hp_w₁ : p w₁ = true := by simp [p]
  have hp_w₂ : p w₂ = false := by simp [p, hne.symm]
  have hnp_w₁ : (!p w₁) = false := by simp [hp_w₁]
  have hnp_w₂ : (!p w₂) = true := by simp [hp_w₂]
  constructor
  · -- "p and might(not p)" fails: after learning p, only w₁ remains, and ¬p w₁ = false
    simp only [Update.conj, Core.CCP.seq, Update.prop, Update.might, Core.CCP.might]
    have h_not_nonempty : ¬({w ∈ {w ∈ ({w₁, w₂} : Set W) | p w = true} |
        (!p w) = true}).Nonempty := by
      intro ⟨w, hw_mem, hw_np⟩
      have hw_p : p w = true := hw_mem.2
      simp [hw_p] at hw_np
    simp only [h_not_nonempty, ↓reduceIte]
  · -- "might(not p) and p" succeeds: might test passes on {w₁, w₂}, then p keeps w₁
    simp only [Update.conj, Core.CCP.seq, Update.prop, Update.might, Core.CCP.might]
    have h_nonempty : ({w ∈ ({w₁, w₂} : Set W) | (!p w) = true}).Nonempty := by
      exact ⟨w₂, Or.inr rfl, hnp_w₂⟩
    simp only [h_nonempty, ↓reduceIte]
    exact ⟨w₁, ⟨Or.inl rfl, hp_w₁⟩⟩

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

end Semantics.Dynamic.UpdateSemantics
