import Linglib.Theories.Syntax.Minimalism.Features

/-!
# Defective Goal
@cite{roberts-2010} @cite{storment-2025} @cite{storment-2026}

Roberts's notion of a *defective goal*: a goal whose formal features are
a proper subset of those of its probe. Defective goals trigger default
agreement (the probe's unvalued features cannot all be checked) and
underlie a range of empirical patterns: PCC effects, Setswana SM17
default subject marking in QI, Bantu locative inversion agreement.

Used by:
- `DefectiveCircumvention.lean` — Storment's probing operation that
  conditionally re-probes past a defective goal.
- `Phenomena/ArgumentStructure/Studies/Storment2026.lean` — derives
  Setswana QI agreement default from defective theme.
-/

namespace Minimalism.Probing

open Minimalism

/-- A goal `G` is **defective** with respect to a probe `P` iff `G`'s
    formal features are a proper subset of `P`'s. The probe needs more
    features than the goal has to offer, so checking is incomplete.
    @cite{roberts-2010}, ch. 2; cited as eq. (49) in @cite{storment-2026}. -/
def DefectiveGoal (probe goal : FeatureBundle) : Prop :=
  goal ⊆ probe ∧ ∃ f ∈ probe, f ∉ goal

instance (probe goal : FeatureBundle) : Decidable (DefectiveGoal probe goal) := by
  unfold DefectiveGoal; infer_instance

/-- The empty goal is defective with respect to any nonempty probe. -/
theorem DefectiveGoal.empty_of_nonempty (probe : FeatureBundle)
    (h : probe ≠ []) : DefectiveGoal probe [] := by
  refine ⟨List.nil_subset _, ?_⟩
  match probe, h with
  | f :: _, _ => exact ⟨f, List.mem_cons_self, List.not_mem_nil⟩

/-- A defective goal is necessarily *missing* some feature the probe has. -/
theorem DefectiveGoal.exists_missing {probe goal : FeatureBundle}
    (h : DefectiveGoal probe goal) : ∃ f ∈ probe, f ∉ goal := h.2

/-- A defective goal's features are all in the probe (proper subset). -/
theorem DefectiveGoal.subset {probe goal : FeatureBundle}
    (h : DefectiveGoal probe goal) : goal ⊆ probe := h.1

/-- No goal is defective with respect to itself. -/
theorem DefectiveGoal.irrefl (fb : FeatureBundle) : ¬ DefectiveGoal fb fb := by
  intro ⟨_, f, hf, hnf⟩; exact hnf hf

end Minimalism.Probing
