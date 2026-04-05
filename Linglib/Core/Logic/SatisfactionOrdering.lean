import Linglib.Core.Order.Normality

/-!
# Satisfaction Ordering

Satisfaction-based orderings: ordering elements by how many criteria they satisfy.
Used by Kratzer modal semantics (worlds by propositions) and Phillips-Brown
desire semantics (propositions by desires).

The induced ordering is a `NormalityOrder` — connecting Kratzer's ordering
source semantics to the default reasoning infrastructure in `Core/Order/`.
-/

namespace Core.SatisfactionOrdering

/-- Satisfaction-based ordering on type α by subset inclusion of satisfied criteria. -/
structure SatisfactionOrdering (α : Type*) (Criterion : Type*) where
  satisfies : α → Criterion → Bool
  criteria : List Criterion

namespace SatisfactionOrdering

variable {α Criterion : Type*}

def satisfiedBy (o : SatisfactionOrdering α Criterion) (a : α) : List Criterion :=
  o.criteria.filter (o.satisfies a)

/-- Weak ordering: a ≥ a' iff a satisfies everything a' satisfies. -/
def atLeastAsGood (o : SatisfactionOrdering α Criterion) (a a' : α) : Bool :=
  (o.satisfiedBy a').all (o.satisfies a)

/-- Strict ordering: a > a' iff a ≥ a' but not a' ≥ a. -/
def strictlyBetter (o : SatisfactionOrdering α Criterion) (a a' : α) : Bool :=
  o.atLeastAsGood a a' && !o.atLeastAsGood a' a

/-- Equivalence: a and a' satisfy the same criteria. -/
def equivalent (o : SatisfactionOrdering α Criterion) (a a' : α) : Bool :=
  o.atLeastAsGood a a' && o.atLeastAsGood a' a

/-- Best elements: those at least as good as all others (maxima). -/
def best (o : SatisfactionOrdering α Criterion) (candidates : List α) : List α :=
  candidates.filter λ a => candidates.all λ a' => o.atLeastAsGood a a'

/-- Undominated elements: those not strictly dominated by any candidate.
    This is the Pareto frontier — equivalent to `best` when the ordering is
    total, but more general for partial orders where incomparable elements
    can both be undominated without either dominating all others.

    Used by Phillips-Brown's question-based desire semantics where the
    proposition ordering is generally partial (propositions can satisfy
    incomparable sets of desires). -/
def undominated (o : SatisfactionOrdering α Criterion) (candidates : List α) : List α :=
  candidates.filter λ a =>
    !(candidates.any λ a' => o.strictlyBetter a' a)

/-- Every best element is undominated. -/
theorem best_sub_undominated (o : SatisfactionOrdering α Criterion)
    (candidates : List α) (a : α) (h : a ∈ o.best candidates) :
    a ∈ o.undominated candidates := by
  simp only [best, List.mem_filter] at h
  simp only [undominated, List.mem_filter]
  refine ⟨h.1, ?_⟩
  -- Need: !(candidates.any (strictlyBetter · a)) = true
  -- i.e. candidates.any (strictlyBetter · a) = false
  -- From h.2: atLeastAsGood a a' = true for all a' ∈ candidates
  -- So strictlyBetter a' a = atLeastAsGood a' a && !true = false
  suffices candidates.any (λ a' => o.strictlyBetter a' a) = false by
    rw [this]; rfl
  rw [Bool.eq_false_iff]
  intro hany
  obtain ⟨a', ha', hstr⟩ := List.any_eq_true.mp hany
  unfold strictlyBetter at hstr
  have hge := List.all_eq_true.mp h.2 a' ha'
  simp [hge] at hstr

/-- With empty criteria, undominated = candidates. -/
theorem empty_criteria_all_undominated (o : SatisfactionOrdering α Criterion)
    (h : o.criteria = []) (candidates : List α) : o.undominated candidates = candidates := by
  unfold undominated
  rw [List.filter_eq_self]
  intro a _
  suffices candidates.any (λ a' => o.strictlyBetter a' a) = false by
    rw [this]; rfl
  rw [Bool.eq_false_iff]
  intro hany
  obtain ⟨a', _, hstr⟩ := List.any_eq_true.mp hany
  unfold strictlyBetter at hstr
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hstr
  have : o.atLeastAsGood a a' = true := by
    unfold atLeastAsGood satisfiedBy; rw [h]; simp
  rw [this] at hstr; simp at hstr

theorem atLeastAsGood_refl (o : SatisfactionOrdering α Criterion) (a : α) :
    o.atLeastAsGood a a = true := by
  unfold atLeastAsGood satisfiedBy
  simp only [List.all_eq_true, List.mem_filter, and_imp]
  intro p _ hp; exact hp

theorem atLeastAsGood_trans (o : SatisfactionOrdering α Criterion) (a b c : α)
    (hab : o.atLeastAsGood a b = true) (hbc : o.atLeastAsGood b c = true) :
    o.atLeastAsGood a c = true := by
  unfold atLeastAsGood at *
  simp only [List.all_eq_true, satisfiedBy, List.mem_filter] at *
  intro p ⟨hp_in, hp_c⟩
  have hp_b : o.satisfies b p = true := hbc p ⟨hp_in, hp_c⟩
  exact hab p ⟨hp_in, hp_b⟩

theorem empty_criteria_all_equivalent (o : SatisfactionOrdering α Criterion)
    (h : o.criteria = []) (a a' : α) : o.equivalent a a' = true := by
  unfold equivalent atLeastAsGood satisfiedBy
  simp only [h, List.filter_nil, List.all_nil, Bool.and_self]

theorem empty_criteria_all_best (o : SatisfactionOrdering α Criterion)
    (h : o.criteria = []) (candidates : List α) : o.best candidates = candidates := by
  unfold best
  simp only [List.filter_eq_self]
  intro a _
  simp only [List.all_eq_true]
  intro a' _
  unfold atLeastAsGood satisfiedBy
  simp only [h, List.filter_nil, List.all_nil]

/-- Prop-valued ordering: `a ≥ a'` iff `atLeastAsGood a a' = true`. -/
def le (o : SatisfactionOrdering α Criterion) (a a' : α) : Prop :=
  o.atLeastAsGood a a' = true

/-- The induced `NormalityOrder`: connects satisfaction-based orderings
    (Kratzer modal semantics, Phillips-Brown desire) to the default
    reasoning infrastructure (`optimal`, `refine`, `respects`, CR1–CR4). -/
def toNormalityOrder (o : SatisfactionOrdering α Criterion) :
    Core.Order.NormalityOrder α where
  le := o.le
  le_refl a := atLeastAsGood_refl o a
  le_trans a b c := atLeastAsGood_trans o a b c

def equiv (o : SatisfactionOrdering α Criterion) (a a' : α) : Prop :=
  o.le a a' ∧ o.le a' a

theorem equiv_refl (o : SatisfactionOrdering α Criterion) (a : α) : o.equiv a a :=
  ⟨atLeastAsGood_refl o a, atLeastAsGood_refl o a⟩

theorem equiv_symm (o : SatisfactionOrdering α Criterion) (a a' : α)
    (h : o.equiv a a') : o.equiv a' a := ⟨h.2, h.1⟩

theorem equiv_trans (o : SatisfactionOrdering α Criterion) (a b c : α)
    (hab : o.equiv a b) (hbc : o.equiv b c) : o.equiv a c :=
  ⟨atLeastAsGood_trans o a b c hab.1 hbc.1, atLeastAsGood_trans o c b a hbc.2 hab.2⟩

end SatisfactionOrdering

end Core.SatisfactionOrdering
