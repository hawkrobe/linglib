import Linglib.Core.Probability.Posterior
import Linglib.Theories.Pragmatics.RSA.Operators
import Mathlib.Probability.Distributions.Uniform

/-!
# RSA reference game — parametric substrate

The classic Rational Speech Act reference game from
@cite{frank-goodman-2012} as a substrate, parametric in the meaning matrix
and world prior. Every paper using a "speaker normalises inverse-extension-
size weights" pattern inherits the architectural theorems below.

## The architectural pitch

WebPPL/Python implementations re-derive the size principle and pragmatic
narrowing per stimulus. Here both are proved **once**, parametric in the
vocabulary, the meaning matrix, and the world prior. Specific empirical
stimuli become one-liner instances.

## Main definitions

* `RSA.ReferenceGame.IsCovering meaning` — the structural assumption: every
  utterance has a non-empty extension AND every world is named by some
  utterance. Captured as a typeclass to avoid threading two hypotheses.
* `RSA.ReferenceGame.L0` — literal listener (Eq. S3): uniform on extension.
* `RSA.ReferenceGame.S1` — pragmatic speaker (Eq. S4 with α=1, no cost):
  `PMF.normalize` of `L0` weights — the Tenenbaum-Griffiths size principle.
* `RSA.ReferenceGame.L1` — pragmatic listener: `PMF.posterior` against any
  full-support world prior.

## Main statements

* `S1_apply_of_appliesTo` — **the size principle** as Eq. S4:
    `S1 w u = (1/|⟦u⟧|) / Σ_{u'} L0 u' w` when `u` applies to `w`.
* `S1_lt_of_partition_gt` — **the pragmatic-narrowing theorem**:
    when `u` applies to two worlds, the speaker prefers the world whose
    alternative-set has SMALLER partition function.
* `L1_gt_iff_S1_lt` — narrowing transfers from S1 to L1 (uniform prior).
* `L1_eq_pure_of_unique_extension` — when an utterance applies to a unique
  world, the listener concentrates entirely there (full mass).

## Concrete instantiation

`Studies/FrankGoodman2012.lean` instantiates these
theorems at the paper's 3-object × 4-feature stimulus. Each of the 4 paper
findings is a one-liner corollary.
-/

set_option autoImplicit false

namespace RSA.ReferenceGame

open scoped ENNReal

variable {Word Object : Type*} [Fintype Word] [Fintype Object]

/-! ## §1. The covering hypothesis -/

/-- A meaning matrix is **covering** if every utterance has a non-empty
extension AND every world is named by some utterance. Minimal data needed
to set up an RSA reference game on the model class. Captured as a typeclass
so consumers state `[IsCovering meaning]` once and inherit both facts. -/
class IsCovering (meaning : Word → Object → Bool) : Prop where
  /-- Every utterance applies to at least one object. -/
  extension_nonempty : ∀ u, (RSA.extensionOf meaning u).Nonempty
  /-- Every object is named by at least one utterance. -/
  covering : ∀ w, ∃ u, meaning u w = true

variable (meaning : Word → Object → Bool) [hCov : IsCovering meaning]

/-! ## §2. Model definitions -/

/-- Extension of an utterance: the Finset of objects to which it applies. -/
abbrev extension (u : Word) : Finset Object := RSA.extensionOf meaning u

/-- **Literal listener** (Eq. S3): uniform on the utterance's extension. -/
noncomputable def L0 (u : Word) : PMF Object :=
  RSA.L0OfBoolMeaning meaning u (hCov.extension_nonempty u)

/-- The L0 sum over utterances at any world is non-zero (covering). -/
theorem L0_tsum_ne_zero (w : Object) : (∑' u, L0 meaning u w) ≠ 0 :=
  let ⟨u, hu⟩ := hCov.covering w
  PMF.tsum_apply_ne_zero _ <| by
    show L0 meaning u w ≠ 0
    rw [← PMF.mem_support_iff]
    show w ∈ (RSA.L0OfBoolMeaning meaning u (hCov.extension_nonempty u)).support
    rw [RSA.mem_support_L0OfBoolMeaning_iff]; exact hu

/-- The L0 sum is finite. -/
theorem L0_tsum_ne_top (w : Object) : (∑' u, L0 meaning u w) ≠ ∞ :=
  PMF.tsum_apply_ne_top _ w

/-- **Pragmatic speaker** (Eq. S4 with α=1, no cost): `PMF.normalize` of
the literal-listener weights. The normalisation factor cancels the per-
utterance constant from the Boltzmann derivation; what remains is the
**size principle** — probability inversely proportional to extension size. -/
noncomputable def S1 (w : Object) : PMF Word :=
  PMF.normalize (fun u => L0 meaning u w) (L0_tsum_ne_zero meaning w)
    (L0_tsum_ne_top meaning w)

/-- The marginal `Σ_w worldPrior w · S1 w u` is non-zero whenever the
prior puts positive mass on some world to which `u` applies — the
substrate condition for `PMF.posterior`. -/
theorem L1_marginal_ne_zero {worldPrior : PMF Object} {u : Word}
    (h_witness : ∃ w ∈ extension meaning u, worldPrior w ≠ 0) :
    PMF.marginal (S1 meaning) worldPrior u ≠ 0 := by
  obtain ⟨w, hw_ext, hw_pos⟩ := h_witness
  refine PMF.marginal_ne_zero _ _ _ hw_pos ?_
  show S1 meaning w u ≠ 0
  rw [← PMF.mem_support_iff, S1, PMF.mem_support_normalize_iff]
  show L0 meaning u w ≠ 0
  rw [← PMF.mem_support_iff]
  show w ∈ (RSA.L0OfBoolMeaning meaning u (hCov.extension_nonempty u)).support
  rw [RSA.mem_support_L0OfBoolMeaning_iff]
  exact RSA.mem_extensionOf.mp hw_ext

/-- **Pragmatic listener**: posterior of `S1` against any world prior. -/
noncomputable def L1 (worldPrior : PMF Object) (u : Word)
    (h_marg : PMF.marginal (S1 meaning) worldPrior u ≠ 0) : PMF Object :=
  PMF.posterior (S1 meaning) worldPrior u h_marg

/-! ## §3. The partition function

The "partition function" `Σ_u L0 u w` is the size-principle weight of all
applicable utterances at world `w`. It is the denominator of the speaker's
softmax (Eq. S4) and the load-bearing object for pragmatic narrowing.

The structural theorem `partition_eq_filter_sum` rewrites it as a sum over
the applicable-utterance Finset — the form most consumers want. -/

/-- The partition function at world `w`: the size-principle weight summed
over all utterances. Equals `Σ_{u : meaning u w} (1/|⟦u⟧|)` (theorem
`partition_eq_filter_sum` below). -/
noncomputable def partition (w : Object) : ℝ≥0∞ := ∑' u, L0 meaning u w

/-- The partition is non-zero (covering). -/
theorem partition_ne_zero (w : Object) : partition meaning w ≠ 0 :=
  L0_tsum_ne_zero meaning w

/-- The partition is finite. -/
theorem partition_ne_top (w : Object) : partition meaning w ≠ ∞ :=
  L0_tsum_ne_top meaning w

/-- **Partition as filter sum**: the partition function equals the sum of
inverse extension cardinalities over applicable utterances. The
"non-applicable" terms vanish (their `L0` value is `0`); what remains is
the size-principle weight of each alternative.

This is the form most consumers use to compute concrete partition values. -/
theorem partition_eq_filter_sum (w : Object) [DecidableEq Word] :
    partition meaning w = ∑ u ∈ Finset.univ.filter (fun u => meaning u w = true),
                            ((extension meaning u).card : ℝ≥0∞)⁻¹ := by
  rw [partition, tsum_fintype]
  rw [show (Finset.univ : Finset Word).sum (fun u => L0 meaning u w)
        = ∑ u ∈ Finset.univ.filter (fun u => meaning u w = true), L0 meaning u w from by
        refine (Finset.sum_filter_of_ne fun u _ h_ne => ?_).symm
        by_contra h_not
        exact h_ne (RSA.L0OfBoolMeaning_apply_of_not_mem _ h_not)]
  refine Finset.sum_congr rfl (fun u h => ?_)
  rw [Finset.mem_filter] at h
  exact RSA.L0OfBoolMeaning_apply_of_mem _ h.2

/-! ## §4. Apply formulas (Eqs. S3, S4) -/

@[simp] theorem L0_apply_of_appliesTo {u : Word} {w : Object}
    (h : meaning u w = true) :
    L0 meaning u w = ((extension meaning u).card : ℝ≥0∞)⁻¹ :=
  RSA.L0OfBoolMeaning_apply_of_mem _ h

@[simp] theorem L0_apply_of_not_appliesTo {u : Word} {w : Object}
    (h : meaning u w ≠ true) :
    L0 meaning u w = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ h

/-- **Size principle** (Eq. S4): for an utterance applying to `w`, the
speaker probability is `(1/|⟦u⟧|)` divided by the sum of `1/|⟦u'⟧|` over
all utterances `u'` applying to `w` — the partition function. -/
theorem S1_apply_of_appliesTo {u : Word} {w : Object} (h : meaning u w = true) :
    S1 meaning w u = ((extension meaning u).card : ℝ≥0∞)⁻¹ / ∑' u', L0 meaning u' w := by
  rw [S1, PMF.normalize_apply, L0_apply_of_appliesTo _ h, ENNReal.div_eq_inv_mul, mul_comm]

/-- The speaker assigns zero probability to utterances that don't apply. -/
theorem S1_apply_of_not_appliesTo {u : Word} {w : Object} (h : meaning u w ≠ true) :
    S1 meaning w u = 0 := by
  rw [S1, PMF.normalize_apply, L0_apply_of_not_appliesTo _ h, zero_mul]

/-! ## §4. Pragmatic narrowing — the architectural theorem -/

/-- **Pragmatic-narrowing theorem** (parametric): when `u` applies to two
worlds `w` and `w'`, the speaker prefers `u` at `w'` over `w` iff the
partition function at `w` exceeds that at `w'`.

Architectural reading: a larger partition at a world means more competition
from informative alternatives, so the speaker is less likely to choose `u`
at that world; the listener therefore narrows toward the world with fewer
informative competitors. This is **the** load-bearing structural theorem of
@cite{frank-goodman-2012} — every paper finding is an instance.

Direct via `PMF.normalize_lt_of_apply_eq_of_sum_lt`: same numerator
(`L0 u w = L0 u w' = (extension u).card⁻¹`), comparing partitions. -/
theorem S1_lt_of_partition_gt
    {u : Word} {w w' : Object}
    (h_w : meaning u w = true) (h_w' : meaning u w' = true)
    (h_partition : (∑' u', L0 meaning u' w') < ∑' u', L0 meaning u' w) :
    S1 meaning w u < S1 meaning w' u := by
  refine PMF.normalize_lt_of_apply_eq_of_sum_lt _ _ _ _ _ _ u ?_ ?_ ?_ h_partition
  · rw [L0_apply_of_appliesTo _ h_w, L0_apply_of_appliesTo _ h_w']
  · rw [L0_apply_of_appliesTo _ h_w']
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  · rw [L0_apply_of_appliesTo _ h_w']
    exact ENNReal.inv_ne_top.mpr <| Nat.cast_ne_zero.mpr <|
      Finset.card_ne_zero.mpr (hCov.extension_nonempty _)

/-- Cross-base companion: when `u` applies to only one of the two worlds,
the speaker prefers the applying world (the other gets zero mass). -/
theorem S1_lt_of_appliesTo_only
    {u : Word} {w w' : Object}
    (h_w : meaning u w ≠ true) (h_w' : meaning u w' = true) :
    S1 meaning w u < S1 meaning w' u := by
  rw [S1_apply_of_not_appliesTo _ h_w]
  rw [pos_iff_ne_zero, ← PMF.mem_support_iff, S1, PMF.mem_support_normalize_iff]
  show L0 meaning u w' ≠ 0
  rw [← PMF.mem_support_iff]
  show w' ∈ (RSA.L0OfBoolMeaning meaning u (hCov.extension_nonempty u)).support
  rw [RSA.mem_support_L0OfBoolMeaning_iff]
  exact h_w'

/-! ## §5. L1 narrowing under uniform prior -/

variable [Nonempty Object]

/-- **L1 narrowing follows S1 narrowing** (uniform world prior): the
posterior at uniform prior reverses the speaker's preference, so L1 favours
the world S1 favours. -/
theorem L1_gt_iff_S1_lt_uniform
    {u : Word}
    (h_marg : PMF.marginal (S1 meaning) (PMF.uniformOfFintype Object) u ≠ 0)
    (w w' : Object) :
    L1 meaning (PMF.uniformOfFintype Object) u h_marg w' >
      L1 meaning (PMF.uniformOfFintype Object) u h_marg w
    ↔ S1 meaning w u < S1 meaning w' u := by
  rw [gt_iff_lt, L1, PMF.posterior_lt_iff_kernel_lt_of_uniform]

/-! ## §6. Unique reference -/

/-- **Unique-reference theorem**: when utterance `u` applies to a unique
world `w_unique` (no other world satisfies `meaning u`), the L1 posterior
concentrates entirely on `w_unique` — full mass `1`.

Architectural reading: a uniquely-identifying utterance leaves the listener
with no Bayesian uncertainty. Direct via
`PMF.posterior_eq_one_of_singleton_score_support`. -/
theorem L1_eq_one_of_unique_extension
    {u : Word} {w_unique : Object}
    (h_applies : meaning u w_unique = true)
    (h_unique : ∀ w', w' ≠ w_unique → meaning u w' ≠ true)
    (worldPrior : PMF Object) (h_prior : worldPrior w_unique ≠ 0)
    (h_marg : PMF.marginal (S1 meaning) worldPrior u ≠ 0) :
    L1 meaning worldPrior u h_marg w_unique = 1 := by
  refine PMF.posterior_eq_one_of_singleton_score_support _ _ _ _ _ (fun w' h_ne => ?_)
  right
  rw [S1_apply_of_not_appliesTo _ (h_unique w' h_ne)]

end RSA.ReferenceGame
