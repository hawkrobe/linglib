import Linglib.Theories.Pragmatics.RSA.Operators
import Linglib.Phenomena.Reference.Studies.FrankGoodman2012
import Mathlib.Probability.Distributions.Uniform

/-!
# @cite{frank-goodman-2012} on mathlib `PMF` (Phase 2 pilot)
@cite{frank-goodman-2012}

The reference game ported to mathlib `PMF` directly. `extension` and `L0`
are paper-named aliases for the generic `RSA.extensionOf` and
`RSA.L0OfBoolMeaning` operators in `Theories/Pragmatics/RSA/Operators.lean`.

The key observation: Eq. S3 of the supplementary materials states that the
literal listener for utterance `w` is uniform on `{o : w(o) = true}`. That is
*exactly* `PMF.uniformOfFinset (extension w)`. Once we say so, all of the
positivity bookkeeping collapses into two coverage facts:

* every word covers some object (`extension_nonempty`)
* every object is covered by some word (`covering`)

S1 is then `PMF.normalize` of `λ u => L0 u w` (Eq. S4 with α = 1, unit cost),
and L1 is `PMF.posterior` of S1 against the uniform world prior.

## Reused from `FrankGoodman2012.lean`

* `Object`, `Feature`, `Feature.appliesTo` — the Boolean denotation matrix.
-/

set_option autoImplicit false

namespace FrankGoodman2012.PMF

open scoped ENNReal
open FrankGoodman2012

/-! ## Coverage — the only data this file needs from the matrix

`extension` and `L0` are paper-named aliases for the generic
`RSA.extensionOf` and `RSA.L0OfBoolMeaning` operators. -/

/-- Extension of a feature: the Finset of objects it applies to. -/
abbrev extension (u : Feature) : Finset Object :=
  RSA.extensionOf Feature.appliesTo u

/-- Every feature covers at least one object — checked by `decide` per case. -/
theorem extension_nonempty (u : Feature) : (extension u).Nonempty := by
  cases u
  · exact ⟨.blue_square,  RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨.green_square, RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨.blue_square,  RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨.blue_circle,  RSA.mem_extensionOf.mpr (by decide)⟩

/-- Every object is named by at least one feature. -/
theorem covering (w : Object) : ∃ u : Feature, u.appliesTo w = true := by
  cases w
  · exact ⟨.blue,  rfl⟩
  · exact ⟨.blue,  rfl⟩
  · exact ⟨.green, rfl⟩

/-! ## L0 — literal listener is uniform on the extension (Eq. S3)

Paper-named alias for `RSA.L0OfBoolMeaning`, supplying the `extension_nonempty`
witness internally so callers don't have to thread it. -/

noncomputable def L0 (u : Feature) : PMF Object :=
  RSA.L0OfBoolMeaning Feature.appliesTo u (extension_nonempty u)

@[simp] theorem mem_support_L0_iff (u : Feature) (w : Object) :
    w ∈ (L0 u).support ↔ u.appliesTo w = true :=
  RSA.mem_support_L0OfBoolMeaning_iff _ _

@[simp] theorem L0_apply_of_appliesTo {u : Feature} {w : Object} (h : u.appliesTo w = true) :
    L0 u w = ((extension u).card : ℝ≥0∞)⁻¹ :=
  RSA.L0OfBoolMeaning_apply_of_mem _ h

@[simp] theorem L0_apply_of_not_appliesTo {u : Feature} {w : Object} (h : u.appliesTo w ≠ true) :
    L0 u w = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ h

/-! ## S1 — pragmatic speaker (α = 1, unit cost ⇒ size principle by Eq. S4) -/

theorem L0_tsum_utterance_ne_zero (w : Object) : ∑' u, (L0 u w : ℝ≥0∞) ≠ 0 :=
  let ⟨u, hu⟩ := covering w
  PMF.tsum_apply_ne_zero L0 (by rw [← PMF.mem_support_iff, mem_support_L0_iff]; exact hu)

theorem L0_tsum_utterance_ne_top (w : Object) : ∑' u, (L0 u w : ℝ≥0∞) ≠ ∞ :=
  PMF.tsum_apply_ne_top (fun u => L0 u) w

noncomputable def S1 (w : Object) : PMF Feature :=
  PMF.normalize (fun u => L0 u w)
    (L0_tsum_utterance_ne_zero w) (L0_tsum_utterance_ne_top w)

@[simp] theorem mem_support_S1_iff (w : Object) (u : Feature) :
    u ∈ (S1 w).support ↔ u.appliesTo w = true := by
  rw [S1, PMF.mem_support_normalize_iff, ← PMF.mem_support_iff, mem_support_L0_iff]

/-! ## L1 — Bayesian inversion against the uniform world prior -/

noncomputable def worldPrior : PMF Object := PMF.uniformOfFintype Object

theorem worldPrior_ne_zero (w : Object) : worldPrior w ≠ 0 :=
  (worldPrior.mem_support_iff w).mp (PMF.mem_support_uniformOfFintype w)

theorem L1_marginal_ne_zero (u : Feature) :
    PMF.marginal S1 worldPrior u ≠ 0 := by
  obtain ⟨w, hw⟩ := extension_nonempty u
  refine PMF.marginal_ne_zero S1 worldPrior u (worldPrior_ne_zero w) ?_
  rw [← PMF.mem_support_iff, mem_support_S1_iff]
  exact RSA.mem_extensionOf.mp hw

noncomputable def L1 (u : Feature) : PMF Object :=
  PMF.posterior S1 worldPrior u (L1_marginal_ne_zero u)

/-! ## Mathlib payoff -/

/-- Support of `L1`: a world is supported iff `Feature.appliesTo u w`. The
uniform prior contributes nothing — every world has `worldPrior w ≠ 0`, so
support reduces to the speaker condition `u ∈ S1(w).support ↔ appliesTo u w`. -/
theorem mem_support_L1_iff_appliesTo (u : Feature) (w : Object) :
    w ∈ (L1 u).support ↔ u.appliesTo w = true := by
  rw [L1, PMF.mem_support_posterior_iff]
  refine ⟨fun ⟨_, h⟩ => (mem_support_S1_iff _ _).mp (((S1 w).mem_support_iff u).mpr h),
          fun h => ⟨worldPrior_ne_zero w,
                    ((S1 w).mem_support_iff u).mp ((mem_support_S1_iff _ _).mpr h)⟩⟩

/-! ## Pragmatic narrowing findings (parallel to bundled-API `cfg.L1` theorems)

The canonical FG2012 results: an ambiguous utterance is interpreted as
referring to the object for which it is *most informative* — i.e., the
object where the speaker would prefer it over the alternatives.

Each finding follows the **canonical migration template** (4 tactic lines):
1. `unfold L1 worldPrior` — expose primitives
2. `rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]` — cancel marginal + uniform prior
3. `exact <per-world S1 leaf>` — reduce to S1 comparison

The leaf is a per-world `S1` comparison reducible to the rational arithmetic
of the `L0` matrix. Bundled here as a sorry'd helper per finding. -/

/-- Per-world leaf for `blue_pragmatic_narrowing`: the speaker prefers `.blue`
at `.blue_square` (where `square` is the only alternative) more than at
`.blue_circle` (where `circle` is uniquely identifying).

**Numeric content**: `S1 .blue_square .blue = 1/2` (partition = 1) and
`S1 .blue_circle .blue = 1/3` (partition = 3/2). The narrowing direction
`1/3 < 1/2` is the canonical FG12 result.

**Friction not handled by `normalize_lt_of_apply_eq_pos_and_sum_lt`**: the
partition functions don't pointwise dominate (`.square` contributes 1/2 at
`.blue_square` but 0 at `.blue_circle`; `.circle` does the opposite). So
`tsum_lt_tsum` can't bridge — actual partition function computation needed.
This motivates a `pmf_partition_compute` helper. Deferred. -/
theorem S1_blue_circle_lt_blue_square : S1 .blue_circle .blue < S1 .blue_square .blue := by
  sorry  -- numeric leaf — needs partition function computation infrastructure

/-- L1 of "blue" prefers `.blue_square` over `.blue_circle` — the canonical
pragmatic narrowing finding. A speaker wanting `.blue_circle` would say
"circle" (uniquely identifying). -/
theorem blue_pragmatic_narrowing : L1 .blue .blue_square > L1 .blue .blue_circle := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_blue_circle_lt_blue_square

/-- Per-world leaf for `square_pragmatic_narrowing`. -/
theorem S1_green_square_lt_blue_square_for_square :
    S1 .green_square .square < S1 .blue_square .square := by
  sorry  -- per-model rational arithmetic on L0 matrix

/-- L1 of "square" prefers `.blue_square` over `.green_square`. -/
theorem square_pragmatic_narrowing :
    L1 .square .blue_square > L1 .square .green_square := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_green_square_lt_blue_square_for_square

/-- Per-world leaf for `green_unique_reference`: at `.blue_square`, the
speaker assigns ZERO mass to `.green` (since "green" doesn't apply); at
`.green_square`, S1 mass to `.green` is positive. So `0 < S1 .green_square .green`.

1-line discharge via `PMF.normalize_lt_of_apply_zero_pos` (the canonical
vacuous-zero cross-base lemma). -/
theorem S1_blue_square_lt_green_square_for_green :
    S1 .blue_square .green < S1 .green_square .green :=
  PMF.normalize_lt_of_apply_zero_pos _ _ _ _ _ _ Feature.green
    (L0_apply_of_not_appliesTo (by decide))
    (by rw [L0_apply_of_appliesTo (by decide)]
        simp [extension])

/-- L1 of "green" puts mass only on `.green_square` (the unique applicable world). -/
theorem green_unique_reference : L1 .green .green_square > L1 .green .blue_square := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_blue_square_lt_green_square_for_green

end FrankGoodman2012.PMF
