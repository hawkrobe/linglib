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
(∀w' ∈ ∩f(w). α(w') → β(w')) from `Conditionals/Basic.lean`. This is the
core bridge connecting the two currently-independent modules.

-/

namespace Semantics.Conditionals.Restrictor

open Semantics.Modality.Kratzer
open Semantics.Conditionals (materialImpB strictImpFinite)
open Semantics.Attitudes.Intensional
open Core.Proposition

/-! ## Helper -/

/-- Filtering by P then checking all Q equals checking all (¬P ∨ Q)
    on the original list. Standard list property used in the main bridge. -/
private theorem filter_all_eq_all_imp {α : Type} (L : List α) (P Q : α → Bool) :
    (L.filter P).all Q = L.all (λ x => !P x || Q x) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, List.all_cons]
    cases P x <;> simp [ih]

/-! ## Core definitions -/

/-- **If α, must β** under the restrictor analysis:
    necessity over the α-restricted modal base.

    ⟦if α, must β⟧(w) = ∀w' ∈ Best(f+α, g, w). β(w') -/
def conditionalNecessity (f : ModalBase) (g : OrderingSource)
    (α β : BProp World) (w : World) : Prop :=
  necessity (restrictedBase f α) g β w

/-- **If α, might β** under the restrictor analysis:
    possibility over the α-restricted modal base.

    ⟦if α, might β⟧(w) = ∃w' ∈ Best(f+α, g, w). β(w') -/
def conditionalPossibility (f : ModalBase) (g : OrderingSource)
    (α β : BProp World) (w : World) : Prop :=
  possibility (restrictedBase f α) g β w

/-! ## Structural lemma -/

/-- Restricted accessible worlds = α-worlds within the original accessible worlds.

    This is the foundational decomposition: restricting the modal base by α
    and then computing accessibility is the same as computing accessibility
    first and then filtering by α. -/
theorem restricted_accessible_eq (f : ModalBase) (α : BProp World) (w : World) :
    accessibleWorlds (restrictedBase f α) w =
    (accessibleWorlds f w).filter α := by
  unfold accessibleWorlds restrictedBase propIntersection
  rw [List.filter_filter]
  apply List.filter_congr
  intro w' _
  simp only [List.all_cons, Bool.and_comm]

/-! ## Main bridge theorems -/

/-- **Restrictor = Strict conditional** (the core bridge theorem).

    With empty ordering source, "if α, must β" (restrictor analysis from
    `Kratzer.lean`) equals "□_f(α → β)" (strict conditional from
    `Conditionals/Basic.lean`).

    ∀w' ∈ Best(f+α, ∅, w). β(w') ⟺ ∀w' ∈ ∩f(w). α(w') → β(w')

    This connects `Modality/Kratzer.lean` to `Conditionals/Basic.lean`. -/
theorem restrictor_eq_strict (f : ModalBase) (α β : BProp World) (w : World) :
    conditionalNecessity f emptyBackground α β w ↔
    strictImpFinite (accessibleWorlds f) α β w = true := by
  unfold conditionalNecessity
  rw [necessity_iff_all]
  rw [empty_ordering_emptyBackground]
  rw [restricted_accessible_eq]
  unfold strictImpFinite
  simp only [filter_all_eq_all_imp]

/-- Kratzer's `materialImplication` equals `materialImpB` from
    `Conditionals/Basic.lean` — the two modules defined the same operation
    independently. -/
theorem kratzer_material_eq_conditional (p q : BProp World) (w : World) :
    materialImplication p q w = materialImpB p q w := rfl

/-! ## Properties -/

/-- **Conditional duality**: "if α, must β" ↔ ¬"if α, might ¬β". -/
theorem conditional_duality (f : ModalBase) (g : OrderingSource)
    (α β : BProp World) (w : World) :
    conditionalNecessity f g α β w ↔
    ¬ conditionalPossibility f g α (λ w' => !β w') w :=
  duality (restrictedBase f α) g β w

/-- **Vacuous conditional**: if no accessible worlds satisfy α, conditional
    necessity holds vacuously (for any β and any ordering source). -/
theorem vacuous_conditional (f : ModalBase) (g : OrderingSource)
    (α β : BProp World) (w : World)
    (h : ((accessibleWorlds f w).filter α).isEmpty = true) :
    conditionalNecessity f g α β w := by
  unfold conditionalNecessity
  rw [necessity_iff_all]
  have hRestr : accessibleWorlds (restrictedBase f α) w = [] := by
    rw [restricted_accessible_eq]
    cases hL : (accessibleWorlds f w).filter α with
    | nil => rfl
    | cons => simp [List.isEmpty, hL] at h
  unfold bestWorlds
  rw [hRestr]
  simp

/-- **Material conditional as degenerate case**: with totally realistic base
    and empty ordering, "if α, must β" reduces to material implication.

    When ∩f(w) = {w} and g = ∅, the restrictor conditional collapses to the
    classical truth-functional conditional ¬α(w) ∨ β(w). -/
theorem material_from_restrictor (f : ModalBase)
    (α β : BProp World) (w : World)
    (hTotal : accessibleWorlds f w = [w]) :
    conditionalNecessity f emptyBackground α β w ↔
    materialImpB α β w = true := by
  rw [restrictor_eq_strict]
  unfold strictImpFinite materialImpB
  simp [hTotal]

/-- **Restrictor monotonicity**: if α₂ entails α₁, then the α₂-restricted
    base is contained in the α₁-restricted base. Stronger antecedents
    yield fewer accessible worlds. -/
theorem restrictor_monotone (f : ModalBase) (α₁ α₂ : BProp World) (w : World)
    (h : ∀ w', α₂ w' = true → α₁ w' = true) :
    ∀ w', w' ∈ accessibleWorlds (restrictedBase f α₂) w →
          w' ∈ accessibleWorlds (restrictedBase f α₁) w := by
  intro w' hw'
  rw [restricted_accessible_eq] at hw' ⊢
  simp only [List.mem_filter] at hw' ⊢
  exact ⟨hw'.1, h w' hw'.2⟩

/-- **Double restriction**: restricting by α₁ then α₂ equals restricting
    by (α₁ ∧ α₂). Grounds iterated conditionals:

    "if α₁, if α₂, must β" = "if (α₁ ∧ α₂), must β" -/
theorem double_restriction (f : ModalBase) (α₁ α₂ : BProp World) (w : World) :
    accessibleWorlds (restrictedBase (restrictedBase f α₁) α₂) w =
    accessibleWorlds (restrictedBase f (λ w' => α₁ w' && α₂ w')) w := by
  simp only [restricted_accessible_eq, List.filter_filter]
  apply List.filter_congr
  intro w' _
  exact Bool.and_comm ..

/-- **Restrictor strengthening**: adding a restrictor α to a modal base
    can only shrink (or preserve) the set of accessible worlds. -/
theorem restrictor_strengthens (f : ModalBase) (α : BProp World) (w : World) :
    ∀ w', w' ∈ accessibleWorlds (restrictedBase f α) w →
          w' ∈ accessibleWorlds f w := by
  intro w' hw'
  rw [restricted_accessible_eq] at hw'
  exact List.mem_of_mem_filter hw'

/-- **Conditional K axiom**: conditional necessity distributes over
    material implication.

    If (if α, must (β → γ)) and (if α, must β), then (if α, must γ). -/
theorem conditional_K (f : ModalBase) (g : OrderingSource)
    (α β γ : BProp World) (w : World)
    (hImpl : conditionalNecessity f g α (λ w' => !β w' || γ w') w)
    (hBeta : conditionalNecessity f g α β w) :
    conditionalNecessity f g α γ w :=
  K_axiom (restrictedBase f α) g β γ w hImpl hBeta

/-! ## Prop-level bridge -/

open Semantics.Tense.ConditionalShift (domainRestrictedConditional)

/-- **Bool/Prop bridge**: `conditionalNecessity` (with empty ordering source)
    corresponds to `domainRestrictedConditional` at the Prop level.

    `conditionalNecessity f ∅ α β w = true` iff every world accessible from
    `w` under `f` that satisfies `α` also satisfies `β` — which is exactly
    `domainRestrictedConditional` over the accessible worlds, with `α` as
    antecedent and `β` as consequent.

    The two definitions live at different abstraction levels:
    - `conditionalNecessity` operates on `World4`, `Bool`, `List` (computational)
    - `domainRestrictedConditional` operates on generic `W`, `Prop`, `Set` (mathematical)

    This theorem bridges the gap for the concrete `World` type. -/
theorem conditionalNecessity_iff_domainRestricted
    (f : ModalBase) (α β : BProp World) (w : World) :
    conditionalNecessity f emptyBackground α β w ↔
    (∀ w' ∈ accessibleWorlds f w, α w' = true → β w' = true) := by
  unfold conditionalNecessity
  rw [necessity_iff_all, empty_ordering_emptyBackground, restricted_accessible_eq]
  constructor
  · intro h w' hw' hα
    have := List.all_eq_true.mp h w' (List.mem_filter.mpr ⟨hw', hα⟩)
    exact this
  · intro h
    apply List.all_eq_true.mpr
    intro w' hw'
    have hmem := List.mem_filter.mp hw'
    exact h w' hmem.1 hmem.2

end Semantics.Conditionals.Restrictor
