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

theorem L0_apply_of_appliesTo {u : Feature} {w : Object} (h : u.appliesTo w = true) :
    L0 u w = ((extension u).card : ℝ≥0∞)⁻¹ :=
  RSA.L0OfBoolMeaning_apply_of_mem _ h

theorem L0_apply_of_not_appliesTo {u : Feature} {w : Object} (h : u.appliesTo w ≠ true) :
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

end FrankGoodman2012.PMF
