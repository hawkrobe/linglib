import Linglib.Core.Order.OfCriteria
import Mathlib.Order.Defs.PartialOrder

/-!
# Satisfaction orderings

This file defines `SatisfactionOrdering α Criterion`, which bundles a `Preorder α` with the data
that constructs it, a relation `satisfies : α → Criterion → Bool` and a list of criteria. The
induced `a ≤ a'` holds when `a` satisfies every listed criterion that `a'` satisfies.

## Implementation notes

The structure extends `Preorder α`, so the order vocabulary of mathlib (`≤`, `<`, `IsMax`,
`Maximal`) is available on `α` once `o.toPreorder` is made an instance, for example with
`letI := o.toPreorder`. The constructor `ofCriteria` builds the preorder from a satisfaction
relation and a list of criteria, and agrees with the general `Preorder.ofCriteria`
(`le_iff_ofCriteria`). The field `decLE` carries decidability of `≤`, which holds automatically
for `ofCriteria`. The reducible aliases `atLeastAsGood`, `equivalent` and `strictlyBetter` stand
for `o.le`, `AntisymmRel` and `o.lt`, so that call sites can use the names of the literature.
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

/-- The canonical constructor builds a `SatisfactionOrdering` from a satisfaction relation and a
list of criteria, with `a ≤ a'` when `a` satisfies every criterion that `a'` satisfies. -/
def ofCriteria (satisfies : α → Criterion → Bool) (criteria : List Criterion) :
    SatisfactionOrdering α Criterion :=
  let le' : α → α → Prop :=
    fun a a' ↦ ∀ p ∈ criteria.filter (satisfies a'), satisfies a p = true
  { le := le'
    le_refl := fun a p hp ↦ by
      simp only [List.mem_filter] at hp
      exact hp.2
    le_trans := fun a b c hab hbc p hp ↦ by
      simp only [List.mem_filter] at hp
      have hp_b : satisfies b p = true :=
        hbc p (by simp only [List.mem_filter]; exact hp)
      exact hab p (by simp only [List.mem_filter]; exact ⟨hp.1, hp_b⟩)
    satisfies := satisfies
    criteria := criteria
    decLE := fun a a' ↦
      show Decidable (∀ p ∈ criteria.filter (satisfies a'), satisfies a p = true) by
        infer_instance }

/-- The bundled construction agrees with the general criteria-derived preorder
`Preorder.ofCriteria`, which takes Prop-valued satisfaction and a `Set` of criteria. The order is
the same, with the `List.filter` membership unfolded, and `SatisfactionOrdering` is the decidable,
bundled specialization. -/
theorem le_iff_ofCriteria (satisfies : α → Criterion → Bool)
    (criteria : List Criterion) (a a' : α) :
    (SatisfactionOrdering.ofCriteria satisfies criteria).le a a' ↔
      (Preorder.ofCriteria (fun x c ↦ satisfies x c = true)
        {c | c ∈ criteria}).le a a' := by
  show (∀ p ∈ criteria.filter (satisfies a'), satisfies a p = true) ↔
    ∀ c ∈ criteria, satisfies a' c = true → satisfies a c = true
  constructor
  · intro h c hc hsat
    exact h c (List.mem_filter.mpr ⟨hc, hsat⟩)
  · intro h c hc
    obtain ⟨hc', hsat⟩ := List.mem_filter.mp hc
    exact h c hc' hsat

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

/-! ## Maxima and undominated elements -/

/-- The best elements are those at least as good as every candidate, the greatest elements. When the
order is partial, `undominated` gives the maximal elements. -/
def best (o : SatisfactionOrdering α Criterion) (candidates : List α) : List α :=
  candidates.filter fun a ↦ decide (∀ a' ∈ candidates, o.le a a')

/-- The undominated elements are those not strictly dominated by any candidate, the Pareto frontier.
They coincide with `best` when the ordering is total, and are more general for partial orders, where
two incomparable elements can both be undominated. -/
def undominated (o : SatisfactionOrdering α Criterion) (candidates : List α) : List α :=
  candidates.filter fun a ↦ decide (¬ ∃ a' ∈ candidates, o.strictlyBetter a' a)

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
  exact fun a' _ ↦ ofCriteria_empty_le satisfies a a'

end SatisfactionOrdering

end Core.Order
