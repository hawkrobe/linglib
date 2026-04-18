import Linglib.Core.Order.Normality
import Mathlib.Order.Defs.PartialOrder

/-!
# Satisfaction Ordering

A `SatisfactionOrdering α Criterion` bundles a `Preorder α` with the data
that constructs it: a `satisfies : α → Criterion → Bool` relation and a
`criteria : List Criterion`. The induced `≤` is subset inclusion of
satisfied criteria.

Used by Kratzer modal semantics (worlds by ordering source) and
Phillips-Brown desire semantics (propositions by desires).

## Design

The structure `extends Preorder α`, so all of mathlib's order vocabulary
(`≤`, `<`, `IsMax`, `Maximal`, etc.) is available on `α` once
`o.toPreorder` is opened as an instance (e.g. `letI := o.toPreorder`).
The smart constructor `ofCriteria` builds the canonical satisfaction-based
preorder from a `satisfies` relation and a criteria list. A `decLE` field
carries decidability of `≤`, automatic for the `ofCriteria` construction.

`atLeastAsGood`, `equivalent`, `strictlyBetter` are kept as `@[reducible]`
aliases for `o.le`, `AntisymmRel`, and `o.lt` so call sites can use
domain-friendly names.
-/

namespace Core.Order

/-- Satisfaction-based preorder on `α` by subset inclusion of satisfied
    criteria. Extends `Preorder α` so downstream code gets `≤`, `<`, and
    mathlib's order vocabulary; retains `satisfies`/`criteria` so the
    construction data is recoverable. `decLE` carries decidability of `≤`. -/
structure SatisfactionOrdering (α : Type*) (Criterion : Type*) extends Preorder α where
  satisfies : α → Criterion → Bool
  criteria : List Criterion
  decLE : ∀ a a' : α, Decidable (a ≤ a')

namespace SatisfactionOrdering

variable {α Criterion : Type*}

instance (o : SatisfactionOrdering α Criterion) (a a' : α) :
    @Decidable (@LE.le α o.toLE a a') :=
  o.decLE a a'

/-- The list of criteria from `o.criteria` that `a` satisfies. -/
def satisfiedBy (o : SatisfactionOrdering α Criterion) (a : α) : List Criterion :=
  o.criteria.filter (o.satisfies a)

/-- Canonical constructor: build a `SatisfactionOrdering` from a satisfaction
    relation and a criteria list. The induced `≤` is "every criterion `a'`
    satisfies, `a` also satisfies". -/
def ofCriteria (satisfies : α → Criterion → Bool) (criteria : List Criterion) :
    SatisfactionOrdering α Criterion :=
  let le' : α → α → Prop :=
    fun a a' => ∀ p ∈ criteria.filter (satisfies a'), satisfies a p = true
  { le := le'
    le_refl := fun a p hp => by
      simp only [List.mem_filter] at hp
      exact hp.2
    le_trans := fun a b c hab hbc p hp => by
      simp only [List.mem_filter] at hp
      have hp_b : satisfies b p = true :=
        hbc p (by simp only [List.mem_filter]; exact hp)
      exact hab p (by simp only [List.mem_filter]; exact ⟨hp.1, hp_b⟩)
    satisfies := satisfies
    criteria := criteria
    decLE := fun a a' =>
      show Decidable (∀ p ∈ criteria.filter (satisfies a'), satisfies a p = true) by
        infer_instance }

/-! ## Domain-friendly aliases

These let study files use names that match the source literature
("at least as good as", "strictly better", "equivalent") while staying
definitionally equal to the underlying preorder. -/

/-- Readability alias for `a ≤ a'` under `o`. -/
@[reducible] def atLeastAsGood (o : SatisfactionOrdering α Criterion) (a a' : α) : Prop :=
  o.le a a'

/-- Readability alias for `a < a'` under `o`. -/
@[reducible] def strictlyBetter (o : SatisfactionOrdering α Criterion) (a a' : α) : Prop :=
  o.le a a' ∧ ¬ o.le a' a

/-- `a` and `a'` satisfy the same criteria. -/
@[reducible] def equivalent (o : SatisfactionOrdering α Criterion) (a a' : α) : Prop :=
  o.le a a' ∧ o.le a' a

/-! ## Reflexivity, transitivity, symmetry

Direct wrappers over the underlying `Preorder` methods, exposed under the
domain-friendly names. -/

theorem atLeastAsGood_refl (o : SatisfactionOrdering α Criterion) (a : α) :
    o.atLeastAsGood a a := o.le_refl a

theorem atLeastAsGood_trans (o : SatisfactionOrdering α Criterion) {a b c : α}
    (hab : o.atLeastAsGood a b) (hbc : o.atLeastAsGood b c) :
    o.atLeastAsGood a c := o.le_trans a b c hab hbc

theorem equivalent_refl (o : SatisfactionOrdering α Criterion) (a : α) :
    o.equivalent a a := ⟨o.le_refl a, o.le_refl a⟩

theorem equivalent_symm (o : SatisfactionOrdering α Criterion) {a a' : α}
    (h : o.equivalent a a') : o.equivalent a' a := ⟨h.2, h.1⟩

theorem equivalent_trans (o : SatisfactionOrdering α Criterion) {a b c : α}
    (hab : o.equivalent a b) (hbc : o.equivalent b c) : o.equivalent a c :=
  ⟨o.le_trans a b c hab.1 hbc.1, o.le_trans c b a hbc.2 hab.2⟩

/-! ## NormalityOrder projection -/

/-- The induced `NormalityOrder`: connects satisfaction-based orderings
    (Kratzer modal semantics, Phillips-Brown desire) to the default reasoning
    infrastructure (`optimal`, `refine`, `respects`, CR1–CR4). -/
def toNormalityOrder (o : SatisfactionOrdering α Criterion) : NormalityOrder α where
  le := o.le
  le_refl := o.le_refl
  le_trans := o.le_trans

/-! ## Maxima and undominated elements -/

/-- Best elements: those at-least-as-good as every candidate. (Greatest
    elements; when the order is partial, see `undominated` for maximal
    elements.) -/
def best (o : SatisfactionOrdering α Criterion) (candidates : List α) : List α :=
  candidates.filter fun a => decide (∀ a' ∈ candidates, o.le a a')

/-- Undominated elements: those not strictly dominated by any candidate. The
    Pareto frontier — equivalent to `best` when the ordering is total, but
    more general for partial orders where incomparable elements can both be
    undominated without either dominating all others. -/
def undominated (o : SatisfactionOrdering α Criterion) (candidates : List α) : List α :=
  candidates.filter fun a => decide (¬ ∃ a' ∈ candidates, o.strictlyBetter a' a)

/-- Membership characterization for `best`. -/
@[simp] theorem mem_best_iff (o : SatisfactionOrdering α Criterion)
    (candidates : List α) (a : α) :
    a ∈ o.best candidates ↔ a ∈ candidates ∧ ∀ a' ∈ candidates, o.le a a' := by
  simp [best]

/-- Membership characterization for `undominated`. -/
@[simp] theorem mem_undominated_iff (o : SatisfactionOrdering α Criterion)
    (candidates : List α) (a : α) :
    a ∈ o.undominated candidates ↔
      a ∈ candidates ∧ ¬ ∃ a' ∈ candidates, o.strictlyBetter a' a := by
  simp [undominated]

/-- Every best element is undominated. -/
theorem best_sub_undominated (o : SatisfactionOrdering α Criterion)
    (candidates : List α) {a : α} (h : a ∈ o.best candidates) :
    a ∈ o.undominated candidates := by
  rw [mem_best_iff] at h
  rw [mem_undominated_iff]
  refine ⟨h.1, ?_⟩
  rintro ⟨a', ha', hstr⟩
  exact hstr.2 (h.2 a' ha')

/-! ## Empty-criteria boundary

When constructed via `ofCriteria` with an empty criteria list, the induced
preorder is total: every pair is `≤`. -/

theorem ofCriteria_empty_le (satisfies : α → Criterion → Bool) (a a' : α) :
    (ofCriteria satisfies []).le a a' := by
  intro p hp
  simp only [List.filter_nil, List.not_mem_nil] at hp

theorem ofCriteria_empty_equivalent (satisfies : α → Criterion → Bool) (a a' : α) :
    (ofCriteria satisfies []).equivalent a a' :=
  ⟨ofCriteria_empty_le satisfies a a', ofCriteria_empty_le satisfies a' a⟩

theorem ofCriteria_empty_undominated (satisfies : α → Criterion → Bool)
    (candidates : List α) :
    (ofCriteria satisfies []).undominated candidates = candidates := by
  unfold undominated
  rw [List.filter_eq_self]
  intro a _
  simp only [decide_eq_true_eq]
  rintro ⟨a', _, hstr⟩
  exact hstr.2 (ofCriteria_empty_le satisfies a a')

theorem ofCriteria_empty_best (satisfies : α → Criterion → Bool)
    (candidates : List α) :
    (ofCriteria satisfies []).best candidates = candidates := by
  unfold best
  rw [List.filter_eq_self]
  intro a _
  simp only [decide_eq_true_eq]
  exact fun a' _ => ofCriteria_empty_le satisfies a a'

end SatisfactionOrdering

end Core.Order
