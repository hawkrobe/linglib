import Linglib.Theories.Semantics.Degree.Aggregation
import Linglib.Theories.Semantics.Lexical.Adjective.Theory

/-!
# Adjective–Aggregation Bridge

Re-exports general aggregation mechanisms from `Semantics.Degree.Aggregation`
and proves that @cite{sassoon-2013}'s binding types (conjunctive, disjunctive,
mixed) are all counting aggregation — a single escape route from Arrow's
impossibility theorem (@cite{dambrosio-hedden-2024}).
-/

namespace Semantics.Lexical.Adjective.Aggregation

variable {α : Type}

-- Re-export general mechanisms so existing consumers don't break
export Semantics.Degree.Aggregation (countBinding majorityBinding
  weightedScore boolMeasures weightedBinding weightedBindingQ
  AggregationType countBinding_zero)

open Semantics.Degree.Aggregation

-- ════════════════════════════════════════════════════
-- Sassoon 2013 Subsumption Theorems
-- ════════════════════════════════════════════════════

private theorem all_eq_decide_filter_ge_length :
    ∀ (dims : List (α → Bool)) (x : α),
      dims.all (· x) = decide ((dims.filter (fun d => d x)).length ≥ dims.length)
  | [], _ => rfl
  | d :: ds, x => by
    have ih := all_eq_decide_filter_ge_length ds x
    simp only [List.all_cons, List.length_cons]
    cases hd : d x
    · rw [@List.filter_cons_of_neg _ (· x) d ds (by simp [hd])]
      simp only [Bool.false_and]
      exact (decide_eq_false_iff_not.mpr (by
        have := List.length_filter_le (· x) ds; omega)).symm
    · rw [@List.filter_cons_of_pos _ (· x) d ds hd]
      simp only [Bool.true_and, List.length_cons, ih]
      exact decide_eq_decide.mpr (by omega)

private theorem any_eq_decide_filter_ge_one :
    ∀ (dims : List (α → Bool)) (x : α),
      dims.any (· x) = decide ((dims.filter (fun d => d x)).length ≥ 1)
  | [], _ => rfl
  | d :: ds, x => by
    simp only [List.any_cons]
    cases hd : d x
    · rw [@List.filter_cons_of_neg _ (· x) d ds (by simp [hd])]
      simp only [Bool.false_or]
      exact any_eq_decide_filter_ge_one ds x
    · rw [@List.filter_cons_of_pos _ (· x) d ds hd]
      simp only [Bool.true_or, List.length_cons]
      exact (decide_eq_true_iff.mpr (by omega)).symm

/-- Conjunctive binding = counting with threshold k = dims.length.
    @cite{sassoon-2013}'s ∀-binding is a special case of counting. -/
theorem conjunctive_is_countAll (dims : List (α → Bool)) (x : α) :
    conjunctiveBinding dims x = countBinding dims.length dims x :=
  all_eq_decide_filter_ge_length dims x

/-- Disjunctive binding = counting with threshold k = 1.
    @cite{sassoon-2013}'s ∃-binding is a special case of counting. -/
theorem disjunctive_is_countOne (dims : List (α → Bool)) (x : α) :
    disjunctiveBinding dims x = countBinding 1 dims x :=
  any_eq_decide_filter_ge_one dims x

/-- @cite{sassoon-2013}'s binding types all map to counting aggregation.
    The key gap: Sassoon has no utilitarian or Cobb-Douglas mechanism. -/
def toAggregationType : DimensionBindingType → AggregationType
  | .conjunctive => .counting
  | .disjunctive => .counting
  | .mixed => .counting

/-- All of Sassoon 2013's binding types are counting aggregation. -/
theorem sassoon_all_counting :
    ∀ b : DimensionBindingType, toAggregationType b = AggregationType.counting := by
  intro b; cases b <;> rfl

end Semantics.Lexical.Adjective.Aggregation
