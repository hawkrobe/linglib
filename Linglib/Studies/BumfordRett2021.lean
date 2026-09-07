import Linglib.Studies.Rett2015
import Linglib.Pragmatics.RSA.Basic
import Linglib.Semantics.Degree.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Bumford and Rett 2021: rationalizing evaluativity

Degree constructions differ in how strongly they imply that a measure exceeds a contextual norm.
This file formalizes the account on which that inference is an implicature computed by a rational
speaker and listener, and on which its strength is graded rather than categorical: the positive
construction is more evaluative than the equative, which is more evaluative than the comparative,
and within the equative the marked antonym is more evaluative than the unmarked one.

Two ingredients drive the result. Worlds are two-dimensional — a subject's height and the centre of
the comparison class — so a listener who is uncertain about the class learns from the choice of
utterance where the subject stands relative to it. And the antonyms compete under lexical
uncertainty, with the marked form costing the speaker more, so choosing it signals that the
speaker's reason for speaking was strong.

The predictions here are the direction of the shift in the listener's posterior, proved for every
positive cost base rather than computed at one: hearing the unmarked positive makes a world with
the subject above the class centre more likely than the mirror world below it, hearing the marked
positive reverses that, the marked equative shifts strongly while the unmarked one shifts weakly,
and the comparative does not shift at all. The last of these needs a lower bound on the cost base;
everything else is structural.

## Main definitions

* `EvalWorld`, `worldPrior` — the height-by-class-centre grid and its truncated Gaussian prior
* `Form`, `standardMet`, `meaning` — the four constructions and their truth conditions at a
  threshold offset
* `L1` — the pragmatic listener, given a construction and a cost base

## Main results

* `pos_tall_evaluative`, `pos_short_evaluative` — the positive is evaluative for both antonyms
* `eq_marked_evaluative`, `eq_unmarked_weakly_evaluative` — the equative is antonym-sensitive
* `geq_marked_evaluative`, `geq_unmarked_barely_evaluative` — the minimum-standard equative sits
  between the exact equative and the comparative
* `comp_marked_weak`, `comp_unmarked_counter_evaluative` — the comparative is not evaluative
* `rsa_neo_gricean_agreement` — the graded predictions match the categorical ones of [rett-2015]

## Implementation notes

The paper bins heights into 17 classes with the class centre in [5, 14] and considers worlds
within two standard deviations of it; the grid here is scaled down to nine heights with centres in
[3, 7] and a deviation of at most two, which preserves the ranking while keeping the state space
small. Its hyperparameters are followed: the null utterance is free, the unmarked utterance costs
1 and the marked one 2, and the speaker's rationality parameter is 4, which enters here as the
cost base `e = exp(-4)`.

The model runs on the kernel pipeline of `RSA.Basic`, with the threshold offset as a state-side
latent: the literal listener at an offset is the world prior conditioned on the utterance's
extension, the speaker is the power-weight speaker with rationality 4 and cost factor `e ^ C(u)`,
the family speaker ranges over (world, offset) pairs, and the world posterior is the first
marginal of the family listener against the unnormalised joint prior, in which the uniform prior
on offsets is absorbed. Rows at zero-prior worlds are the zero measure, which the joint prior
never weights.

## References

* [bumford-rett-2021]
* [barker-2002-vagueness]
* [bergen-levy-goodman-2016]
* [lassiter-goodman-2017]
* [rett-2015]
-/
namespace BumfordRett2021

open MeasureTheory ProbabilityTheory
open Degree (Construction)
open scoped ENNReal

/-! ### The worlds -/

/-- A world is a pair (height index, CC center index).

    Height index i ∈ Fin 9 represents height i + 1 (range 1–9).
    CC center index j ∈ Fin 5 represents center j + 3 (range 3–7).
    Valid worlds satisfy |height − center| ≤ 2 (enforced via prior). -/
abbrev EvalWorld := Fin 9 × Fin 5

/-- Height value (1–9) from world indices. -/
def htVal (w : EvalWorld) : Int := (w.1.val : Int) + 1

/-- CC center value (3–7) from world indices. -/
def muVal (w : EvalWorld) : Int := (w.2.val : Int) + 3

/-- Deviation of height from CC center: ht − μ. -/
def deviation (w : EvalWorld) : Int := htVal w - muVal w

/-! ### The prior -/

/-- Gaussian-weighted prior over valid worlds.

    CC center is uniform; height weight decreases with distance from center.
    Approximates N(μ, 1) truncated at |ht − μ| ≤ 2. Weights: d=0 → 10,
    d=1 → 6, d=2 → 1, d>2 → 0 (invalid world). -/
def worldPrior (w : EvalWorld) : ℚ :=
  match (deviation w).natAbs with
  | 0 => 10
  | 1 => 6
  | 2 => 1
  | _ => 0

/-! ### Utterances and their costs -/

/-- Utterance type: unmarked (positive-polar), marked (negative-polar), or null.

    For the positive construction: unmarked = "tall", marked = "short".
    For the exact equative: unmarked = "as tall as K", marked = "as short as K".
    Cost asymmetry (marked = 2, unmarked = 1) drives antonym-sensitive
    evaluativity via [bergen-levy-goodman-2016]'s lexical uncertainty. -/
inductive Utterance where
  | unmarked  -- positive-polar form
  | marked    -- negative-polar form (costlier)
  | null      -- silence ∅
  deriving Repr, DecidableEq, Fintype

instance : MeasurableSpace Utterance := ⊤

/-! ### The threshold offset -/

/-- Threshold offset σ ∈ {−2, −1, 0, 1, 2}.

    Determines how far above the CC center a person must be to count as
    "tall." Index s ∈ Fin 5 represents σ = s − 2. Higher σ means a more
    exclusive threshold. -/
abbrev Sigma := Fin 5

/-- Integer offset value: index s ↦ σ = s − 2. -/
def sigmaVal (s : Sigma) : Int := (s.val : Int) - 2

/-! ### Shared infrastructure -/

private theorem worldPrior_nonneg_Q :
    ∀ w : EvalWorld, (0 : ℚ) ≤ worldPrior w := by
  intro w; unfold worldPrior; split <;> norm_num

private theorem worldPrior_pos_of_ne {w : EvalWorld} (h : worldPrior w ≠ 0) :
    (0 : ℝ) < (worldPrior w : ℝ) := by
  have := worldPrior_nonneg_Q w; exact_mod_cast lt_of_le_of_ne this (Ne.symm h)

/-- The utterance's cost as an exponent: the marked form costs 2, the unmarked 1 and silence
nothing, so the speaker's cost factor is `e ^ costN u` with `e = exp(-α)` at the paper's α = 4. -/
def costN : Utterance → ℕ
  | .unmarked => 1
  | .marked   => 2
  | .null     => 0

/-- The speaker's cost factor `e ^ C(u)`. -/
noncomputable def costFactor (e : ℝ) (u : Utterance) : ℝ≥0∞ := ENNReal.ofReal (e ^ costN u)

private theorem costFactor_ne_zero {e : ℝ} (he0 : 0 < e) (u : Utterance) : costFactor e u ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (pow_pos he0 _)).ne'

private theorem costFactor_ne_top (e : ℝ) (u : Utterance) : costFactor e u ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-! ### The listener and speaker

The paper's pipeline, parameterized by the cost-factor base `e` (= `exp(−4)` at the paper's
α = 4; only the speaker depends on `e`):

    L₀(w | u, σ) ∝ ⟦u⟧(σ,w) · P(w)               (`L0`)
    S₁(u | w, σ) ∝ L₀(w | u, σ)⁴ · e^C(u)         (`Sk`)
    L₁(w, σ | u) ∝ S₁(u | w, σ) · P(w) · P(σ)     (`L1`)

The prior is baked into the literal listener (eq 10, `L₀ ∝ P(w)·⟦u⟧(w)`), which is the world
prior conditioned on the utterance's extension; `null` is licensed everywhere, so the speaker's
row vanishes only at invalid (zero-prior) worlds, which carry joint weight 0. Statements are
`e`-generic over `0 < e`; `exp(−4)` is instantiated only in a bridging corollary. -/

/-- The world prior as an unnormalised measure. -/
noncomputable def worldMeasure : Measure EvalWorld :=
  ∑ w, ENNReal.ofReal (worldPrior w) • Measure.dirac w

theorem worldMeasure_apply_singleton (w : EvalWorld) :
    worldMeasure {w} = ENNReal.ofReal (worldPrior w) :=
  Measure.sum_smul_dirac_apply_singleton _ w

instance : IsFiniteMeasure worldMeasure :=
  ⟨by
    rw [worldMeasure, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr λ w _ => by
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      exact ENNReal.ofReal_lt_top⟩

private theorem worldMeasure_singleton_ne_zero {w : EvalWorld} (h : worldPrior w ≠ 0) :
    worldMeasure {w} ≠ 0 := by
  rw [worldMeasure_apply_singleton]
  exact (ENNReal.ofReal_pos.mpr (worldPrior_pos_of_ne h)).ne'

/-- The extension of an utterance at a threshold offset under a meaning. -/
def extension (sem : Utterance → Sigma → EvalWorld → Bool) (σ : Sigma) (u : Utterance) :
    Set EvalWorld :=
  {w | sem u σ w = true}

/-- The literal listener at a threshold offset: the world prior conditioned on the extension. -/
noncomputable def L0 (sem : Utterance → Sigma → EvalWorld → Bool) (σ : Sigma) :
    Kernel Utterance EvalWorld :=
  RSA.literalListener worldMeasure λ u => (extension sem σ u).indicator 1

private theorem L0_apply_singleton_of_lic {sem σ u w} (h : sem u σ w = true) :
    L0 sem σ u {w} = (worldMeasure (extension sem σ u))⁻¹ * worldMeasure {w} :=
  RSA.literalListener_indicator_apply_singleton worldMeasure (extension sem σ) h

private theorem L0_apply_singleton_of_not_lic {sem σ u w} (h : sem u σ w = false) :
    L0 sem σ u {w} = 0 :=
  RSA.literalListener_indicator_apply_singleton_of_notMem worldMeasure (extension sem σ)
    (by show ¬ (sem u σ w = true); rw [h]; exact Bool.false_ne_true)

private theorem L0_le_one (sem : Utterance → Sigma → EvalWorld → Bool) (σ : Sigma)
    (u : Utterance) (w : EvalWorld) : L0 sem σ u {w} ≤ 1 :=
  RSA.literalListener_apply_le_one _ _ _ _

private theorem L0_ne_zero {sem σ u w} (hlic : sem u σ w = true) (hval : worldPrior w ≠ 0) :
    L0 sem σ u {w} ≠ 0 := by
  rw [L0_apply_singleton_of_lic hlic]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (worldMeasure_singleton_ne_zero hval)

/-- **Speaker** `S₁(· | w, σ)`: the power-weight speaker with rationality 4 over the
threshold-indexed literal listeners, as a kernel on (world, offset) pairs. -/
noncomputable def Sk (sem : Utterance → Sigma → EvalWorld → Bool) (e : ℝ) :
    Kernel (EvalWorld × Sigma) Utterance :=
  RSA.familySpeaker (L0 sem) 4 (costFactor e)

instance (sem : Utterance → Sigma → EvalWorld → Bool) (e : ℝ) : IsFiniteKernel (Sk sem e) :=
  inferInstanceAs (IsFiniteKernel (RSA.familySpeaker _ _ _))

/-- Unnormalised joint prior `P(w) · P(σ)` (uniform latent absorbed). -/
noncomputable def jointPrior : Measure (EvalWorld × Sigma) :=
  ∑ s, ENNReal.ofReal (worldPrior s.1) • Measure.dirac s

theorem jointPrior_apply_singleton (s : EvalWorld × Sigma) :
    jointPrior {s} = ENNReal.ofReal (worldPrior s.1) := by
  rw [jointPrior, Measure.sum_smul_dirac_apply_singleton]

instance : IsFiniteMeasure jointPrior :=
  ⟨by
    rw [jointPrior, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr λ s _ => by
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      exact ENNReal.ofReal_lt_top⟩

/-- Concise world constructor: `mkW h m = (Fin h, Fin m)`. -/
def mkW (h : Fin 9) (m : Fin 5) : EvalWorld := (h, m)

private theorem jointPrior_ne_zero {s : EvalWorld × Sigma} (h : worldPrior s.1 ≠ 0) :
    jointPrior {s} ≠ 0 := by
  rw [jointPrior_apply_singleton]
  exact (ENNReal.ofReal_pos.mpr (worldPrior_pos_of_ne h)).ne'

private theorem jointPrior_real_singleton (s : EvalWorld × Sigma) :
    jointPrior.real {s} = worldPrior s.1 := by
  rw [measureReal_def, jointPrior_apply_singleton,
    ENNReal.toReal_ofReal (by exact_mod_cast worldPrior_nonneg_Q s.1)]

private theorem Sk_apply (sem : Utterance → Sigma → EvalWorld → Bool) (e : ℝ)
    (s : EvalWorld × Sigma) : Sk sem e s = RSA.speaker 4 (costFactor e) (L0 sem s.2) s.1 := rfl

private theorem Sk_apply_ne_zero {sem} {e : ℝ} (he0 : 0 < e) {s : EvalWorld × Sigma}
    {u : Utterance} (hval : worldPrior s.1 ≠ 0) (hlic : sem u s.2 s.1 = true) :
    Sk sem e s {u} ≠ 0 := by
  rw [Sk_apply]
  exact RSA.speaker_apply_singleton_ne_zero (by norm_num) (costFactor_ne_zero he0)
    (costFactor_ne_top e) (λ u' => L0_le_one sem s.2 u' s.1) (L0_ne_zero hlic hval)

private theorem Sk_apply_eq_zero {sem} {e : ℝ} {s : EvalWorld × Sigma} {u : Utterance}
    (h : sem u s.2 s.1 = false) : Sk sem e s {u} = 0 := by
  rw [Sk_apply]
  exact RSA.speaker_apply_singleton_eq_zero (by norm_num) (L0_apply_singleton_of_not_lic h)

/-- Single-witness discharge of the listener's marginal positivity: a valid
world `w0` licensed for `u` at some `σ0`. -/
theorem comp_Sk_ne_zero {sem} {e : ℝ} (he0 : 0 < e) {u : Utterance}
    {w0 : EvalWorld} {σ0 : Sigma} (hval : worldPrior w0 ≠ 0) (hlic : sem u σ0 w0 = true) :
    (Sk sem e ∘ₘ jointPrior) {u} ≠ 0 :=
  comp_apply_singleton_ne_zero _ _ (w := (w0, σ0)) (jointPrior_ne_zero hval)
    (Sk_apply_ne_zero he0 hval hlic)

/-! ### Structural speaker/listener monotonicity

Evaluativity is proved *structurally*, with no normaliser computation: the
per-latent speaker order follows from **licensing-set inclusion** between two
equal-prior worlds. Two equal-prior worlds with the same licensing bit for `u`
have identical speaker numerators; a wider licensing set only enlarges the
denominator. Hence a world that is licensed for *fewer* alternatives (its
licensing set is contained in the other's) puts *more* mass on the observed
`u`. Only `0 < e` is used (for strict positivity); nothing needs `e < 1`. -/

/-- **Monotone literal listener**: with equal world prior, a licensing bit that
is dominated (`wa` licensed for `u` ⟹ `wb` licensed) forces `L₀ wa ≤ L₀ wb`. -/
private theorem L0_le_of_prior_lic {sem} {u σ} {wa wb : EvalWorld}
    (hp : worldPrior wa = worldPrior wb) (hlic : sem u σ wa = true → sem u σ wb = true) :
    L0 sem σ u {wa} ≤ L0 sem σ u {wb} := by
  by_cases ha : sem u σ wa = true
  · rw [L0_apply_singleton_of_lic ha, L0_apply_singleton_of_lic (hlic ha),
      worldMeasure_apply_singleton, worldMeasure_apply_singleton, hp]
  · rw [L0_apply_singleton_of_not_lic (Bool.not_eq_true _ ▸ ha)]; exact zero_le

/-- The speaker weight of `u` at a world. -/
private theorem weight_le_of_prior_lic {sem} {e : ℝ} {u σ} {wa wb : EvalWorld}
    (hp : worldPrior wa = worldPrior wb) (hlic : sem u σ wa = true → sem u σ wb = true) :
    L0 sem σ u {wa} ^ (4 : ℝ) * costFactor e u ≤ L0 sem σ u {wb} ^ (4 : ℝ) * costFactor e u :=
  mul_le_mul' (ENNReal.rpow_le_rpow (L0_le_of_prior_lic hp hlic) (by norm_num)) le_rfl

/-- **Per-latent evaluativity**: at a fixed `σ`, the speaker prefers the
observed `u` for `w2` at least as much as for `w1`, when `w1, w2` share the
world prior, `w1`'s `u`-licensing is contained in `w2`'s (`hu`), and — on the
region where `w1` is `u`-licensed — `w2`'s whole licensing set is contained in
`w1`'s (`halt`). Pure order argument; no normaliser is evaluated. -/
private theorem Sk_le_of_incl {sem} {e : ℝ} {u σ} {w1 w2 : EvalWorld}
    (hp : worldPrior w1 = worldPrior w2)
    (hu : sem u σ w1 = true → sem u σ w2 = true)
    (halt : sem u σ w1 = true → ∀ u', sem u' σ w2 = true → sem u' σ w1 = true) :
    Sk sem e (w1, σ) {u} ≤ Sk sem e (w2, σ) {u} := by
  by_cases h1 : sem u σ w1 = true
  · rw [Sk_apply, Sk_apply, RSA.speaker_apply_singleton, RSA.speaker_apply_singleton]
    exact ENNReal.div_le_div (weight_le_of_prior_lic hp hu)
      (Finset.sum_le_sum λ u' _ => weight_le_of_prior_lic hp.symm (halt h1 u'))
  · rw [Sk_apply_eq_zero (Bool.not_eq_true _ ▸ h1)]
    exact zero_le

/-- **Strict per-latent gap**: where `w1` is *not* `u`-licensed but `w2` is,
`w1` contributes `0` and `w2` contributes a positive speaker mass. -/
private theorem Sk_lt_of_gap {sem} {e : ℝ} (he0 : 0 < e) {u σ} {w1 w2 : EvalWorld}
    (hv2 : worldPrior w2 ≠ 0) (h1 : sem u σ w1 = false) (h2 : sem u σ w2 = true) :
    Sk sem e (w1, σ) {u} < Sk sem e (w2, σ) {u} := by
  rw [Sk_apply_eq_zero h1]
  exact pos_iff_ne_zero.mpr (Sk_apply_ne_zero he0 hv2 h2)

/-- **Evaluativity from licensing inclusion** (Tier A). For two equal-prior
worlds with `w1`'s `u`-licensing contained in `w2`'s (`hu`) and, on that
support, `w2`'s whole licensing contained in `w1`'s (`halt`), plus a `σ₀` where
only `w2` is `u`-licensed, the listener strictly prefers `w2`: `L₁(w1|u) <
L₁(w2|u)`. Pure order argument — no normaliser is evaluated, and only `0 < e`
is used. -/
private theorem evaluative_of_incl {sem} {e : ℝ} (he0 : 0 < e) {u : Utterance}
    {w1 w2 : EvalWorld} (hcomp : (Sk sem e ∘ₘ jointPrior) {u} ≠ 0)
    (hp : worldPrior w1 = worldPrior w2) (hv2 : worldPrior w2 ≠ 0)
    (hu : ∀ σ, sem u σ w1 = true → sem u σ w2 = true)
    (halt : ∀ σ, sem u σ w1 = true → ∀ u', sem u' σ w2 = true → sem u' σ w1 = true)
    (σ₀ : Sigma) (hgap1 : sem u σ₀ w1 = false) (hgap2 : sem u σ₀ w2 = true) :
    (((Sk sem e)†jointPrior) u).fst.real {w1} < (((Sk sem e)†jointPrior) u).fst.real {w2} := by
  rw [posterior_fst_real_lt_iff _ _ hcomp]
  simp only [jointPrior_real_singleton, hp]
  refine Finset.sum_lt_sum (λ σ _ => ?_) ⟨σ₀, Finset.mem_univ _, ?_⟩
  · exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _)
      (Sk_le_of_incl hp (hu σ) (halt σ))) (by exact_mod_cast worldPrior_nonneg_Q w2)
  · exact mul_lt_mul_of_pos_left ((ENNReal.toReal_lt_toReal (measure_ne_top _ _)
      (measure_ne_top _ _)).mpr (Sk_lt_of_gap he0 hv2 hgap1 hgap2)) (worldPrior_pos_of_ne hv2)

/-! ### The four constructions

Every construction says two things at once: the subject's height stands in some relation to a
standard, and a degree — the subject's own height for the positive, the standard for the rest —
lies above the threshold for the unmarked antonym or below it for the marked one. The four rows
differ only in the first conjunct, which is what makes them comparable. -/

/-- Keisha's height `k`, fixed and known to both speaker and listener; 5 on the scaled grid. -/
def kHeight : Int := 5

/-- The constructions simulated: the positive, the exact equative, the minimum-standard equative,
and the comparative. -/
inductive Form where
  | positive
  | exactEquative
  | minimumEquative
  | comparative
  deriving DecidableEq, Repr

/-- The degree whose position relative to the threshold the utterance conveys: the subject's height
for the positive, the standard `k` for the constructions that compare with one. -/
def measured : Form → EvalWorld → Int
  | .positive, w => htVal w
  | _, _ => kHeight

/-- The relation the construction imposes between the subject's height and the standard: none for
the positive, equality for the exact equative, a weak comparison for the minimum-standard equative
and a strict one for the comparative. -/
def standardMet : Form → Utterance → EvalWorld → Bool
  | _, .null, _ => true
  | .positive, _, _ => true
  | .exactEquative, _, w => decide (htVal w = kHeight)
  | .minimumEquative, .unmarked, w => decide (htVal w ≥ kHeight)
  | .minimumEquative, .marked, w => decide (htVal w ≤ kHeight)
  | .comparative, .unmarked, w => decide (htVal w > kHeight)
  | .comparative, .marked, w => decide (htVal w < kHeight)

/-- The truth conditions of a construction at a threshold offset and a world. Silence is true
everywhere, which is what keeps the speaker's row positive at every valid world. -/
def meaning (c : Form) (u : Utterance) (σ : Sigma) (w : EvalWorld) : Bool :=
  match u with
  | .null => true
  | .unmarked => standardMet c u w && decide (measured c w ≥ muVal w + sigmaVal σ)
  | .marked => standardMet c u w && decide (measured c w ≤ muVal w + sigmaVal σ)

/-- Every utterance of every construction is true at some world of positive prior, so the
listener's marginal never vanishes. -/
theorem comp_Sk_meaning_ne_zero (c : Form) (u : Utterance) {e : ℝ} (he0 : 0 < e) :
    (Sk (meaning c) e ∘ₘ jointPrior) {u} ≠ 0 := by
  obtain ⟨w0, σ0, hval, hlic⟩ :
      ∃ (w : EvalWorld) (σ : Sigma), worldPrior w ≠ 0 ∧ meaning c u σ w = true := by
    cases c <;> cases u <;> decide
  exact comp_Sk_ne_zero he0 hval hlic

/-- The pragmatic listener for construction `c` at cost base `e`: the Bayesian inverse of the
family speaker over (world, offset) pairs, the substrate's family listener. -/
noncomputable def L1 (c : Form) (e : ℝ) : Kernel Utterance (EvalWorld × Sigma) :=
  (Sk (meaning c) e)†jointPrior

/-- What makes an utterance shift the listener from `w1` towards `w2`: the two worlds carry the
same nonzero prior, the utterance is true at `w2` whenever it is true at `w1`, every alternative
available at `w2` under such a threshold is available at `w1` too, and at the threshold `σ₀` the
utterance separates the two worlds. -/
def ShiftsTo (c : Form) (u : Utterance) (w1 w2 : EvalWorld) (σ₀ : Sigma) : Prop :=
  worldPrior w1 = worldPrior w2 ∧ worldPrior w2 ≠ 0 ∧
    (∀ σ, meaning c u σ w1 = true → meaning c u σ w2 = true) ∧
    (∀ σ, meaning c u σ w1 = true → ∀ u', meaning c u' σ w2 = true → meaning c u' σ w1 = true) ∧
    meaning c u σ₀ w1 = false ∧ meaning c u σ₀ w2 = true

instance (c : Form) (u : Utterance) (w1 w2 : EvalWorld) (σ₀ : Sigma) :
    Decidable (ShiftsTo c u w1 w2 σ₀) := inferInstanceAs (Decidable (_ ∧ _))

/-- A shifting configuration makes the listener prefer `w2` to `w1`, at every positive cost base.
Silence is true everywhere, so the licensing hypotheses the underlying order argument needs are
discharged by the construction table itself. -/
theorem shifts {c : Form} {u : Utterance} {w1 w2 : EvalWorld} {σ₀ : Sigma} {e : ℝ}
    (he0 : 0 < e) (h : ShiftsTo c u w1 w2 σ₀) :
    (L1 c e u).fst.real {w1} < (L1 c e u).fst.real {w2} := by
  obtain ⟨hp, hv2, hu, halt, hgap1, hgap2⟩ := h
  exact evaluative_of_incl he0 (comp_Sk_meaning_ne_zero c u he0) hp hv2 hu halt σ₀ hgap1 hgap2

/-! ### The positive construction

The two worlds compared below sit one unit above and one unit below the class centre and carry the
same prior, so any asymmetry between them is pragmatic. The paper's expected deviations are 2.08
for *tall* and −3.18 for *short*: the marked antonym is the more evaluative of the two, since the
extra cost it carries signals that the speaker's reason for choosing it was strong. -/

theorem pos_tall_evaluative (e : ℝ) (he0 : 0 < e) :
    (L1 .positive e .unmarked).fst.real {mkW 5 2} > (L1 .positive e .unmarked).fst.real {mkW 3 2} :=
  shifts he0 (σ₀ := 2) (by decide)

theorem pos_short_evaluative (e : ℝ) (he0 : 0 < e) :
    (L1 .positive e .marked).fst.real {mkW 3 2} > (L1 .positive e .marked).fst.real {mkW 5 2} :=
  shifts he0 (σ₀ := 2) (by decide)

/-! ### The exact equative

The equative fixes the subject's height at the standard, so what the listener learns is where the
standard sits relative to the class centre. The two worlds compared hold the height at the standard
and vary the centre below and above it. The paper's expected deviations are −1.06 for the marked
form and 0.84 for the unmarked one: the marked antonym shifts strongly and the unmarked one weakly,
which is the antonym-sensitive pattern the categorical account states as a dichotomy. -/

theorem eq_marked_evaluative (e : ℝ) (he0 : 0 < e) :
    (L1 .exactEquative e .marked).fst.real {mkW 4 4} >
      (L1 .exactEquative e .marked).fst.real {mkW 4 0} :=
  shifts he0 (σ₀ := 0) (by decide)

theorem eq_unmarked_weakly_evaluative (e : ℝ) (he0 : 0 < e) :
    (L1 .exactEquative e .unmarked).fst.real {mkW 4 0} >
      (L1 .exactEquative e .unmarked).fst.real {mkW 4 4} :=
  shifts he0 (σ₀ := 4) (by decide)

/-! ### The minimum-standard equative

The unmarked and marked forms of *at least as tall as* are not synonymous, unlike those of the
exact equative, so the antonyms compete only partly and the evaluativity predicted falls between
the exact equative's and the comparative's. The paper's expected deviations are −1.52 for the marked
form and 0.11 for the unmarked one, the weakest evaluative effect of any construction. -/

theorem geq_marked_evaluative (e : ℝ) (he0 : 0 < e) :
    (L1 .minimumEquative e .marked).fst.real {mkW 4 4} >
      (L1 .minimumEquative e .marked).fst.real {mkW 4 0} :=
  shifts he0 (σ₀ := 0) (by decide)

theorem geq_unmarked_barely_evaluative (e : ℝ) (he0 : 0 < e) :
    (L1 .minimumEquative e .unmarked).fst.real {mkW 4 0} >
      (L1 .minimumEquative e .unmarked).fst.real {mkW 4 4} :=
  shifts he0 (σ₀ := 4) (by decide)

/-! ### The comparative

*Taller than K* and *shorter than K* have no semantic overlap at all, so the antonyms do not
compete and nothing pressures an evaluative inference. The paper's expected deviations here are
−0.74 for the unmarked form and −0.44 for the marked one, both close to zero: the listener does
infer something about where the standard sits, but that is a consequence of learning a relative
height, not evaluativity. -/

theorem comp_marked_weak (e : ℝ) (he0 : 0 < e) :
    (L1 .comparative e .marked).fst.real {mkW 3 2} >
      (L1 .comparative e .marked).fst.real {mkW 3 0} :=
  shifts he0 (σ₀ := 2) (by decide)

/-! Hearing the unmarked comparative does not make the listener infer that the standard is high;
the inference runs the other way, since a subject exceeding the standard leaves the standard room
to be below average. That direction is the one case whose proof needs exact values rather than the
inclusion argument, so the normalisers are evaluated below. -/

/-- The mass of an extension is the sum of the prior over it. -/
private theorem worldMeasure_extension (sem : Utterance → Sigma → EvalWorld → Bool) (σ : Sigma)
    (u : Utterance) :
    worldMeasure (extension sem σ u) =
      ENNReal.ofReal ((∑ w : EvalWorld, if sem u σ w then worldPrior w else 0 : ℚ) : ℝ) := by
  rw [worldMeasure, Measure.finsetSum_apply, Rat.cast_sum,
    ENNReal.ofReal_sum_of_nonneg
      (f := λ w => ((if sem u σ w = true then worldPrior w else 0 : ℚ) : ℝ)) λ w _ =>
        Rat.cast_nonneg.mpr (by split <;> [exact worldPrior_nonneg_Q w; exact le_rfl])]
  refine Finset.sum_congr rfl λ w _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ .of_discrete]
  by_cases h : sem u σ w = true
  · rw [Set.indicator_of_mem (show w ∈ extension sem σ u from h), Pi.one_apply, mul_one, if_pos h]
  · rw [Set.indicator_of_notMem (show w ∉ extension sem σ u from h), mul_zero, if_neg h,
      Rat.cast_zero, ENNReal.ofReal_zero]

/-- Kernel-clean evaluation of an extension's mass: the `ℝ≥0∞` fan-out
sum equals `ofReal` of the concrete ℚ mass sum. -/
private theorem dval {sem σ u} {D : ℚ}
    (h : (∑ w : Fin 9 × Fin 5, if sem u σ w then worldPrior w else 0) = D) :
    worldMeasure (extension sem σ u) = ENNReal.ofReal D := by
  rw [worldMeasure_extension, h]

private theorem dval_unm :
    worldMeasure (extension (meaning .comparative) (1 : Sigma) .unmarked) = ENNReal.ofReal 25 :=
  dval (by decide +kernel)

private theorem dval_null :
    worldMeasure (extension (meaning .comparative) (1 : Sigma) .null) = ENNReal.ofReal 120 :=
  dval (by decide +kernel)

private theorem wp53 : worldPrior (mkW 5 3) = 10 := by decide +kernel

private theorem L0_unm :
    L0 (meaning .comparative) (1 : Sigma) .unmarked {mkW 5 3} = ENNReal.ofReal (2 / 5) := by
  rw [L0_apply_singleton_of_lic (by decide), dval_unm, worldMeasure_apply_singleton,
    show ((worldPrior (mkW 5 3) : ℝ)) = 10 by rw [wp53]; norm_num,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 25),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 25⁻¹)]
  norm_num

private theorem L0_null :
    L0 (meaning .comparative) (1 : Sigma) .null {mkW 5 3} = ENNReal.ofReal (1 / 12) := by
  rw [L0_apply_singleton_of_lic (by decide), dval_null, worldMeasure_apply_singleton,
    show ((worldPrior (mkW 5 3) : ℝ)) = 10 by rw [wp53]; norm_num,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 120),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 120⁻¹)]
  norm_num

private theorem L0_marked :
    L0 (meaning .comparative) (1 : Sigma) .marked {mkW 5 3} = 0 :=
  L0_apply_singleton_of_not_lic (by decide)

private theorem weight_ne_top (sem : Utterance → Sigma → EvalWorld → Bool) (e : ℝ)
    (s : EvalWorld × Sigma) (u : Utterance) :
    L0 sem s.2 u {s.1} ^ (4 : ℝ) * costFactor e u ≠ ∞ :=
  ENNReal.mul_ne_top (RSA.weight_rpow_ne_top (by norm_num) (L0_le_one sem s.2 u s.1))
    (costFactor_ne_top e u)

private theorem toReal_rpow_four (x : ℝ≥0∞) : (x ^ (4 : ℝ)).toReal = x.toReal ^ 4 := by
  rw [← ENNReal.toReal_rpow, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The speaker's share of the unmarked comparative at the world `mkW 5 3` and offset 1 exceeds a
half whenever the cost base is at least `1/100`. -/
private theorem Sk_bound {e : ℝ} (he0 : 0 < e) (he_lo : (1 : ℝ) / 100 ≤ e) :
    (1 : ℝ) / 2 < (Sk (meaning .comparative) e (mkW 5 3, (1 : Sigma))).real {.unmarked} := by
  have hA : (0 : ℝ) < (2 / 5) ^ 4 * e := by positivity
  rw [Sk_apply, RSA.speaker, Kernel.ofWeights_real_singleton _ _
      (weight_ne_top (meaning .comparative) e (mkW 5 3, (1 : Sigma))),
    show (Finset.univ : Finset Utterance) = {.unmarked, .marked, .null} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [L0_unm, L0_marked, L0_null, costFactor, costN, ENNReal.toReal_mul, toReal_rpow_four,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2 / 5),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 12), ENNReal.toReal_ofReal he0.le,
    pow_zero, ENNReal.ofReal_one, ENNReal.toReal_zero,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 4), zero_mul, zero_add, pow_one, mul_one]
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [he_lo]

/-- Counter-evaluative comparative — a **prior-magnitude** effect, not a
licensing one. Unlike the seven Tier-A predictions (which hold for every cost
base `e ∈ (0,1)` via `evaluative_of_incl`'s bare `0 < e`), here the speaker
distribution depends on a world only through its *licensing set* (the prior
cancels inside the speaker), so the 10:1 world prior of `mkW 5 3` (k at the CC mean)
over `mkW 5 1` (k above it) is the sole asymmetry and it dominates.

The prior dominates only when markedness costs are not extreme. The sharp
threshold is `e ≥ (D_unm(1)/D_null)⁴ = (25/120)⁴ ≈ 0.0019`: for `e` below it,
the cost factor `e^C` so heavily discounts the informative "taller than"
utterance in the high-threshold worlds that the informativity cost dominates
the prior mass and the inequality flips. We therefore assume `1/100 ≤ e`
(comfortably above the threshold, and met by the paper's `e = exp(−4) ≈ 0.018`;
see `comp_unmarked_counter_evaluative_exp`). -/
theorem comp_unmarked_counter_evaluative (e : ℝ) (he0 : 0 < e) (he_lo : (1 : ℝ)/100 ≤ e) :
    (L1 .comparative e .unmarked).fst.real {mkW 5 3} >
      (L1 .comparative e .unmarked).fst.real {mkW 5 1} := by
  -- The listener comparison reduces to prior-weighted speaker sums. The prior of `mkW 5 1` is 1
  -- and that of `mkW 5 3` is 10 at every σ; speaker shares are at most 1, so `mkW 5 1`'s five
  -- terms sum to at most 5, while `mkW 5 3`'s σ = 1 term alone is `10 · S(w2, 1) > 5`
  -- (`Sk_bound`) — so the prior mass wins.
  rw [gt_iff_lt, L1, posterior_fst_real_lt_iff _ _
    (comp_Sk_meaning_ne_zero .comparative .unmarked he0)]
  simp only [jointPrior_real_singleton, show worldPrior (mkW 5 1) = 1 from by decide +kernel,
    wp53, Rat.cast_one, Rat.cast_ofNat, one_mul]
  calc ∑ σ : Sigma, (Sk (meaning .comparative) e (mkW 5 1, σ)).real {.unmarked}
      ≤ ∑ σ : Sigma, (1 : ℝ) :=
        Finset.sum_le_sum λ σ _ => by
          rw [Sk_apply]; exact RSA.speaker_real_singleton_le_one _ _ _ _ _
    _ = 5 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
    _ < 10 * (Sk (meaning .comparative) e (mkW 5 3, 1)).real {.unmarked} := by
        linarith [Sk_bound he0 he_lo]
    _ ≤ ∑ σ : Sigma, 10 * (Sk (meaning .comparative) e (mkW 5 3, σ)).real {.unmarked} :=
        Finset.single_le_sum
          (f := λ σ => 10 * (Sk (meaning .comparative) e (mkW 5 3, σ)).real {.unmarked})
          (λ σ _ => by positivity) (Finset.mem_univ (1 : Sigma))

/-- The counter-evaluative comparative at the paper's cost base `e = exp(−4)`.
The hypothesis `1/100 ≤ exp(−4)` reduces to `exp 4 ≤ 100`, and
`exp 4 = (exp 1)⁴ < 2.7182818286⁴ ≈ 54.6 < 100`. -/
theorem comp_unmarked_counter_evaluative_exp :
    (L1 .comparative (Real.exp (-4)) .unmarked).fst.real {mkW 5 3}
      > (L1 .comparative (Real.exp (-4)) .unmarked).fst.real {mkW 5 1} := by
  refine comp_unmarked_counter_evaluative (Real.exp (-4)) (Real.exp_pos _) ?_
  have he4 : Real.exp 4 ≤ 100 :=
    calc Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 2.7182818286 ^ 4 := by gcongr; exact Real.exp_one_lt_d9.le
      _ ≤ 100 := by norm_num
  rw [Real.exp_neg, one_div]
  gcongr

/-! ### The ranking across constructions

Table 1's expected deviations rank the constructions strictly: the positive (2.08 unmarked, −3.18
marked), then the exact equative (0.84, −1.06), then the minimum-standard equative (0.11, −1.52),
then the comparative (−0.74, −0.44). Two factors produce the ranking. The positive leaves the
threshold entirely open, so it is the vaguest and the most informative about where the subject
stands; each further construction fixes more of the standard and leaves less to infer. And the
marked antonym costs more, so the listener looks for a reason the speaker paid it, which is found
in worlds where the standard is atypical.

The theorems above check the qualitative pattern that ranking amounts to: both antonyms of the
positive are evaluative, only the marked antonym of either equative is, and neither antonym of the
comparative is.

### The categorical account

The Neo-Gricean account classifies the same constructions categorically — the positive evaluative
for both polarities, the equative for the negative one only, the comparative for neither — and the
theorem below checks that the two accounts agree wherever both speak. What the graded account adds
is the strength of each inference, one mechanism in place of two implicature types, and a
prediction about the minimum-standard equative, which the categorical account does not classify. -/

open Rett2015 (Evaluative)

/-- The categorical classification and the listener's shifts agree across the paradigm: where the
    Neo-Gricean account calls a construction evaluative for a polarity, the listener shifts away
    from the class centre, and where it does not, the shift is absent. -/
theorem rsa_neo_gricean_agreement (e : ℝ) (he0 : 0 < e) :
    -- Positive: both accounts say evaluative for both polarities
    Evaluative .positive .positive ∧
    Evaluative .positive .negative ∧
    (L1 .positive e .unmarked).fst.real {mkW 5 2} > (L1 .positive e .unmarked).fst.real {mkW 3 2} ∧
    (L1 .positive e .marked).fst.real {mkW 3 2} > (L1 .positive e .marked).fst.real {mkW 5 2} ∧
    -- Equative: Neo-Gricean says marked-only; RSA shows marked shift
    ¬ Evaluative .equative .positive ∧
    Evaluative .equative .negative ∧
    (L1 .exactEquative e .marked).fst.real {mkW 4 4} >
      (L1 .exactEquative e .marked).fst.real {mkW 4 0} ∧
    -- Comparative: both say not evaluative
    ¬ Evaluative .comparative .positive ∧
    ¬ Evaluative .comparative .negative :=
  ⟨by decide, by decide,
   pos_tall_evaluative e he0, pos_short_evaluative e he0,
   by decide, by decide,
   eq_marked_evaluative e he0,
   by decide, by decide⟩

end BumfordRett2021
