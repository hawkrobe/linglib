module

public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Order.Atoms
public import Mathlib.Tactic.DeriveFintype

/-!
# Scenarios

A scenario is the pair of co-arguments of a clause ordered by role rank, A over P in a
monotransitive clause and R over T in a ditransitive one, each carried as its value on a
referential prominence scale. Its kind compares the two values: downstream when the
higher-ranked argument is the more prominent, upstream when it is the less prominent, and
balanced when they tie. The direct and inverse contexts of cyclic Agree, the IO–DO
combinations the person-case constraint restricts, and co-argument-sensitive indexing are all
scenarios over the person scale; the argument coding splits of [haspelmath-2021] are scenarios
over its prominence scales.

## Main declarations

* `Clause.Scenario`: the two prominence values, `high` and `low`, with `Scenario.map`.
* `Clause.Scenario.Kind`: upstream, balanced, downstream, as a bounded linear order in that
  order.
* `Clause.Scenario.kindBy`: the kind of a scenario under a scale given as a rank map, and
  `Scenario.kind` for a linearly ordered scale.
* `Clause.Scenario.kind_eq_downstream_iff_eq`, `Clause.Scenario.not_kind_lt_kind`: on a
  two-element scale the downstream scenario is `⟨⊤, ⊥⟩` alone, and which scenarios can be
  the more usual.

## Implementation notes

The kind is the three-way comparison `compare` read into the three labels by
`Kind.ofOrdering`; the usualness order on kinds, downstream above upstream, is
[haspelmath-2021]'s (11). A scale need not be linearly ordered: `kindBy p` compares through
a rank map `p`, as `Person.prominence` ranks persons.

## References

* [haspelmath-2021]
* [bejar-rezac-2009]
* [deal-2024]
* [witzlack-makarevich-etal-2016]
-/

@[expose] public section

namespace Clause

/-- A scenario: the prominence values of the two co-arguments of a clause, the higher-ranked
one first. [haspelmath-2021] writes `X > Y` for `⟨X, Y⟩`. -/
structure Scenario (α : Type*) where
  /-- The prominence of the higher-ranked argument, A or R. -/
  high : α
  /-- The prominence of the lower-ranked argument, P or T. -/
  low : α
  deriving DecidableEq, Fintype

namespace Scenario

variable {α β : Type*}

/-- Apply a map to both prominence values. -/
def map (f : α → β) (s : Scenario α) : Scenario β := ⟨f s.high, f s.low⟩

@[simp] theorem map_high (f : α → β) (s : Scenario α) : (s.map f).high = f s.high := rfl

@[simp] theorem map_low (f : α → β) (s : Scenario α) : (s.map f).low = f s.low := rfl

/-- The kinds of scenario, in order of usualness. -/
inductive Kind where
  | upstream
  | balanced
  | downstream
  deriving DecidableEq, Fintype, Repr

namespace Kind

/-- Usualness of a kind: downstream scenarios are the most usual, upstream the least. -/
def usualness : Kind → ℕ
  | .upstream => 0
  | .balanced => 1
  | .downstream => 2

instance : LinearOrder Kind := LinearOrder.lift' usualness (by decide)

instance : Nontrivial Kind := ⟨⟨.upstream, .downstream, by decide⟩⟩

/-- `⊥ = upstream`, `⊤ = downstream`. -/
instance : BoundedOrder Kind where
  top := .downstream
  le_top := by decide
  bot := .upstream
  bot_le := by decide

theorem le_balanced_iff {k : Kind} : k ≤ .balanced ↔ k ≠ .downstream := by decide +revert

theorem balanced_le_iff {k : Kind} : .balanced ≤ k ↔ k ≠ .upstream := by decide +revert

/-- The kind a comparison of the higher-ranked argument's prominence with the lower-ranked
one's yields. -/
def ofOrdering : Ordering → Kind
  | .lt => .upstream
  | .eq => .balanced
  | .gt => .downstream

@[simp] theorem ofOrdering_eq_upstream {o : Ordering} : ofOrdering o = .upstream ↔ o = .lt := by
  cases o <;> decide

@[simp] theorem ofOrdering_eq_balanced {o : Ordering} : ofOrdering o = .balanced ↔ o = .eq := by
  cases o <;> decide

@[simp] theorem ofOrdering_eq_downstream {o : Ordering} :
    ofOrdering o = .downstream ↔ o = .gt := by
  cases o <;> decide

end Kind

section KindBy

variable [LinearOrder β] (p : α → β)

/-- The kind of a scenario under the scale `p`: downstream when the higher-ranked argument
ranks higher, upstream when it ranks lower, and balanced when the two tie. -/
def kindBy (s : Scenario α) : Kind := .ofOrdering (compare (p s.high) (p s.low))

theorem kindBy_eq_downstream_iff {s : Scenario α} :
    kindBy p s = .downstream ↔ p s.low < p s.high := by
  rw [kindBy, Kind.ofOrdering_eq_downstream, compare_gt_iff_gt]

theorem kindBy_eq_upstream_iff {s : Scenario α} :
    kindBy p s = .upstream ↔ p s.high < p s.low := by
  rw [kindBy, Kind.ofOrdering_eq_upstream, compare_lt_iff_lt]

theorem kindBy_eq_balanced_iff {s : Scenario α} :
    kindBy p s = .balanced ↔ p s.high = p s.low := by
  rw [kindBy, Kind.ofOrdering_eq_balanced, compare_eq_iff_eq]

end KindBy

variable [LinearOrder α]

/-- The kind of a scenario over a linearly ordered scale. -/
abbrev kind : Scenario α → Kind := kindBy id

omit [LinearOrder α] in
theorem kindBy_eq_kind_map {β : Type*} [LinearOrder β] (p : α → β) (s : Scenario α) :
    kindBy p s = (s.map p).kind := rfl

theorem kind_eq_downstream_iff {s : Scenario α} : s.kind = .downstream ↔ s.low < s.high :=
  kindBy_eq_downstream_iff id

theorem kind_eq_upstream_iff {s : Scenario α} : s.kind = .upstream ↔ s.high < s.low :=
  kindBy_eq_upstream_iff id

theorem kind_eq_balanced_iff {s : Scenario α} : s.kind = .balanced ↔ s.high = s.low :=
  kindBy_eq_balanced_iff id

/-- On a two-element scale the downstream scenario is `⟨⊤, ⊥⟩` alone. -/
theorem kind_eq_downstream_iff_eq [BoundedOrder α] [IsSimpleOrder α] {s : Scenario α} :
    s.kind = .downstream ↔ s = ⟨⊤, ⊥⟩ := by
  obtain ⟨h, l⟩ := s
  rw [kind_eq_downstream_iff]
  rcases eq_bot_or_eq_top h with rfl | rfl <;> rcases eq_bot_or_eq_top l with rfl | rfl <;> simp

/-- A scenario whose higher-ranked argument is `⊥` or whose lower-ranked one is `⊤` is at most
balanced, and one whose higher-ranked argument is `⊤` or whose lower-ranked one is `⊥` at least
balanced, so the first is never the more usual. -/
theorem not_kind_lt_kind [BoundedOrder α] {s t : Scenario α} (hs : s.high = ⊥ ∨ s.low = ⊤)
    (ht : t.high = ⊤ ∨ t.low = ⊥) : ¬ t.kind < s.kind := by
  refine not_lt.2 <|
    (Kind.le_balanced_iff.2 fun h ↦ ?_).trans (Kind.balanced_le_iff.2 fun h ↦ ?_)
  · rw [kind_eq_downstream_iff] at h
    exact hs.elim (fun e ↦ not_lt_bot (e ▸ h)) fun e ↦ not_top_lt (e ▸ h)
  · rw [kind_eq_upstream_iff] at h
    exact ht.elim (fun e ↦ not_top_lt (e ▸ h)) fun e ↦ not_lt_bot (e ▸ h)

end Scenario

end Clause
