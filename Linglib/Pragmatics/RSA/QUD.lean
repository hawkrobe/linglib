import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# QUD-projected aggregation for RSA pragmatic models

A Question Under Discussion (QUD) partitions worlds via a projection
`project : G → W → β` — two worlds are QUD-equivalent under goal `g`
iff they project to the same value. The QUD-projected aggregation of
a non-negative weight function sums the weight over the equivalence class.

This is the architectural primitive shared by all Kao-family RSA models
(metaphor, hyperbole, irony): the speaker's "informativeness" along a
QUD dimension is the projected weight at the literally-true world. A
literally-false utterance can have positive QUD-projected mass at a
world `w` iff some QUD-equivalent world `w'` is literally true — this
is the **architectural mechanism for nonliteral interpretation**.

## Main definition

* `RSA.QUD.proj project weight g w` — sum of `weight w'` over all `w'`
  with `project g w' = project g w`.

## Main theorems

* `RSA.QUD.self_le_proj` — the world is in its own equivalence class,
  so `weight w ≤ proj project weight g w`.
* `RSA.QUD.proj_pos_iff_exists_class_member` — positive iff some
  equivalence-class member has positive weight (the headline lemma for
  nonliteral interpretation).
* `RSA.QUD.proj_le_total` — bounded by the total weight.
* `RSA.QUD.proj_le_one_of_pmf` — when the weight is a PMF, bounded by 1.

## Anchoring

QUD-projection in RSA was introduced by [goodman-stuhlmueller-2013]
and is used by [kao-bergen-goodman-2014] (metaphor),
[kao-wu-bergen-goodman-2014] (hyperbole), [kao-goodman-2015]
(irony), and the broader Kao family.
-/

set_option autoImplicit false

namespace RSA.QUD

open scoped ENNReal

/-- QUD-projected aggregation: sum of `weight w'` over the
QUD-equivalence class of `w` under projection `project g`. -/
noncomputable def proj {W G β : Type*} [Fintype W] [DecidableEq β]
    (project : G → W → β) (weight : W → ℝ≥0∞) (g : G) (w : W) : ℝ≥0∞ :=
  ∑ w' ∈ (Finset.univ : Finset W).filter (fun w' => project g w' = project g w),
    weight w'

variable {W G β : Type*} [Fintype W] [DecidableEq β]
  (project : G → W → β) (weight : W → ℝ≥0∞) (g : G) (w : W)

/-- The world `w` is in its own QUD-equivalence class, so its weight
provides a lower bound on the QUD-projected aggregation. -/
theorem self_le_proj : weight w ≤ proj project weight g w :=
  Finset.single_le_sum (f := weight) (fun _ _ => zero_le)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)

/-- **Headline lemma**: the QUD-projected aggregation is positive iff
some world in the same QUD-equivalence class has positive weight.

This is the architectural mechanism for nonliteral interpretation
across the Kao family (metaphor, hyperbole, irony): a literally-false
utterance has positive projected mass at world `w` iff there exists a
QUD-equivalent world `w'` (potentially differing on non-QUD dimensions)
that IS literally true. -/
theorem proj_pos_iff_exists_class_member :
    0 < proj project weight g w ↔
      ∃ w' ∈ (Finset.univ : Finset W).filter
              (fun w' => project g w' = project g w),
        0 < weight w' :=
  Finset.sum_pos_iff_of_nonneg (fun _ _ => zero_le)

/-- The QUD-projected aggregation is bounded by the total weight. -/
theorem proj_le_total : proj project weight g w ≤ ∑ w' : W, weight w' :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end RSA.QUD

namespace RSA.QUD

variable {W G β : Type*} [Fintype W] [DecidableEq β]
  (project : G → W → β) (p : PMF W) (g : G) (w : W)

/-- When the weight is a PMF, the QUD-projected aggregation is bounded
by 1 (the equivalence class is a subset of the support). -/
theorem proj_le_one_of_pmf : proj project (⇑p) g w ≤ 1 := by
  calc proj project (⇑p) g w
      ≤ ∑ w' : W, p w' := proj_le_total project (⇑p) g w
    _ = ∑' w' : W, p w' := (tsum_fintype _).symm
    _ = 1 := p.tsum_coe

/-- When the weight is a PMF, the QUD-projected aggregation is finite. -/
theorem proj_ne_top_of_pmf : proj project (⇑p) g w ≠ ⊤ :=
  (lt_of_le_of_lt (proj_le_one_of_pmf project p g w) ENNReal.one_lt_top).ne

end RSA.QUD
