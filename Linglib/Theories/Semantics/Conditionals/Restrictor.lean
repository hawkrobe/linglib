import Linglib.Theories.Semantics.Modality.Kratzer.Operators
import Linglib.Theories.Semantics.Conditionals.Basic
import Linglib.Theories.Semantics.Tense.ConditionalShift

/-!
# Restrictor Theory of Conditionals
@cite{kratzer-1986} @cite{kratzer-2012}

Kratzer's restrictor analysis: if-clauses restrict the modal domain rather than
functioning as binary connectives. "If α, (must) β" is analyzed as modal
necessity/possibility over the modal base restricted by α.

This module bridges `Conditionals/Basic.lean` and `Modality/Kratzer.lean`,
deriving conditional truth conditions from modal restriction.

## Core Thesis

If-clauses are not propositional connectives. They are **restrictors** of the
modal base. "If it rains, the streets are wet" does not express a binary
relation between two propositions. Instead, "if it rains" restricts the
modal base to rain-worlds, and the (possibly covert) necessity operator
quantifies over the best of those worlds.

## Key Result

`restrictor_eq_strict`: with empty ordering source, Kratzer's conditional
necessity (∀w' ∈ Best(f+α, ∅, w). β(w')) equals the strict conditional
(∀w' ∈ ∩f(w). α(w') → β(w')) from `Conditionals/Basic.lean`.

-/

namespace Semantics.Conditionals.Restrictor

open Semantics.Modality.Kratzer

variable {W : Type*}

/-! ## Core definitions -/

/-- **If α, must β** under the restrictor analysis:
    necessity over the α-restricted modal base. -/
def conditionalNecessity (f : ModalBase W) (g : OrderingSource W)
    (α : W → Prop) (β : W → Prop) (w : W) : Prop :=
  necessity (restrictedBase f α) g β w

/-- **If α, might β** under the restrictor analysis:
    possibility over the α-restricted modal base. -/
def conditionalPossibility (f : ModalBase W) (g : OrderingSource W)
    (α : W → Prop) (β : W → Prop) (w : W) : Prop :=
  possibility (restrictedBase f α) g β w

/-! ## Structural lemma -/

/-- Restricted accessible worlds = α-worlds within the original accessible worlds. -/
theorem restricted_accessible_eq (f : ModalBase W) (α : W → Prop) (w : W) :
    accessibleWorlds (restrictedBase f α) w =
    {w' ∈ accessibleWorlds f w | α w'} := by
  ext w'
  unfold accessibleWorlds restrictedBase propIntersection
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro p hp
      exact h p (List.mem_cons_of_mem _ hp)
    · exact h α List.mem_cons_self
  · intro ⟨hAcc, hα⟩ p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hα
    · exact hAcc p hp'

/-! ## Main bridge theorems -/

/-- **Restrictor = Strict conditional**.

    With empty ordering source, "if α, must β" equals "□_f(α → β)". -/
theorem restrictor_eq_strict (f : ModalBase W) (α : W → Prop) (β : W → Prop) (w : W) :
    conditionalNecessity f emptyBackground α β w ↔
    (∀ w' ∈ accessibleWorlds f w, α w' → β w') := by
  unfold conditionalNecessity
  rw [necessity_iff_all, empty_ordering_emptyBackground, restricted_accessible_eq]
  constructor
  · intro h w' hw' hα
    exact h w' ⟨hw', hα⟩
  · intro h w' hw'
    exact h w' hw'.1 hw'.2

/-! ## Properties -/

/-- **Conditional duality**: "if α, must β" ↔ ¬"if α, might ¬β". -/
theorem conditional_duality (f : ModalBase W) (g : OrderingSource W)
    (α : W → Prop) (β : W → Prop) (w : W) :
    conditionalNecessity f g α β w ↔
    ¬ conditionalPossibility f g α (fun w' => ¬ β w') w :=
  duality (restrictedBase f α) g β w

/-- **Vacuous conditional**: if no accessible worlds satisfy α, conditional
    necessity holds vacuously. -/
theorem vacuous_conditional (f : ModalBase W) (g : OrderingSource W)
    (α : W → Prop) (β : W → Prop) (w : W)
    (h : ∀ w', w' ∈ accessibleWorlds f w → ¬ α w') :
    conditionalNecessity f g α β w := by
  unfold conditionalNecessity
  rw [necessity_iff_all]
  intro w' hw'
  have hRestr : w' ∈ accessibleWorlds (restrictedBase f α) w := hw'.1
  rw [restricted_accessible_eq] at hRestr
  exact absurd hRestr.2 (h w' hRestr.1)

/-- **Material conditional as degenerate case**: with totally realistic base
    and empty ordering, "if α, must β" reduces to material implication. -/
theorem material_from_restrictor (f : ModalBase W)
    (α : W → Prop) (β : W → Prop) (w : W)
    (hTotal : accessibleWorlds f w = {w}) :
    conditionalNecessity f emptyBackground α β w ↔
    (α w → β w) := by
  rw [restrictor_eq_strict, hTotal]
  constructor
  · intro h hα
    exact h w (Set.mem_singleton_iff.mpr rfl) hα
  · intro h w' hw' hα
    have : w' = w := Set.mem_singleton_iff.mp hw'
    subst this
    exact h hα

/-- **Restrictor monotonicity**: if α₂ entails α₁, then the α₂-restricted
    base is contained in the α₁-restricted base. -/
theorem restrictor_monotone (f : ModalBase W) (α₁ α₂ : W → Prop) (w : W)
    (h : ∀ w', α₂ w' → α₁ w') :
    ∀ w', w' ∈ accessibleWorlds (restrictedBase f α₂) w →
          w' ∈ accessibleWorlds (restrictedBase f α₁) w := by
  intro w' hw'
  rw [restricted_accessible_eq] at hw' ⊢
  exact ⟨hw'.1, h w' hw'.2⟩

/-- **Double restriction**: restricting by α₁ then α₂ equals restricting
    by (α₁ ∧ α₂). -/
theorem double_restriction (f : ModalBase W) (α₁ α₂ : W → Prop) (w : W) :
    accessibleWorlds (restrictedBase (restrictedBase f α₁) α₂) w =
    accessibleWorlds (restrictedBase f (fun w' => α₁ w' ∧ α₂ w')) w := by
  ext w'
  rw [restricted_accessible_eq, restricted_accessible_eq, restricted_accessible_eq]
  constructor
  · intro ⟨⟨hf, hα₁⟩, hα₂⟩
    exact ⟨hf, hα₁, hα₂⟩
  · intro ⟨hf, hα₁, hα₂⟩
    exact ⟨⟨hf, hα₁⟩, hα₂⟩

/-- **Restrictor strengthening**: adding a restrictor α to a modal base
    can only shrink (or preserve) the set of accessible worlds. -/
theorem restrictor_strengthens (f : ModalBase W) (α : W → Prop) (w : W) :
    ∀ w', w' ∈ accessibleWorlds (restrictedBase f α) w →
          w' ∈ accessibleWorlds f w := by
  intro w' hw'
  rw [restricted_accessible_eq] at hw'
  exact hw'.1

/-- **Conditional K axiom**: conditional necessity distributes over implication. -/
theorem conditional_K (f : ModalBase W) (g : OrderingSource W)
    (α : W → Prop) (β γ : W → Prop) (w : W)
    (hImpl : conditionalNecessity f g α (fun w' => β w' → γ w') w)
    (hBeta : conditionalNecessity f g α β w) :
    conditionalNecessity f g α γ w :=
  K_axiom (restrictedBase f α) g β γ w hImpl hBeta

/-! ## Prop-level bridge -/

open Semantics.Tense.ConditionalShift (domainRestrictedConditional)

/-- `conditionalNecessity` (with empty ordering source) corresponds to
    `domainRestrictedConditional` at the Prop level. -/
theorem conditionalNecessity_iff_domainRestricted
    (f : ModalBase W) (α : W → Prop) (β : W → Prop) (w : W) :
    conditionalNecessity f emptyBackground α β w ↔
    (∀ w' ∈ accessibleWorlds f w, α w' → β w') :=
  restrictor_eq_strict f α β w

end Semantics.Conditionals.Restrictor
