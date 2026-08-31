import Linglib.Studies.Rett2015
import Linglib.Pragmatics.RSA.Canonical
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
* `L1` — the pragmatic listener, given a construction and an utterance

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

The model runs on the `PMF` pipeline of `RSA.Canonical`, with the threshold offset as the joint
listener's second coordinate: `meaningE` folds the world prior into the graded literal listener,
`Sk` is the cost-sensitive speaker (kept total at prior-zero worlds by a guard), and the world
posterior is the joint posterior's first marginal.

## References

* [bumford-rett-2021]
* [barker-2002-vagueness]
* [bergen-levy-goodman-2016]
* [lassiter-goodman-2017]
* [rett-2015]
-/
namespace BumfordRett2021

open RSA
open Degree (Construction)

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

/-! ### The threshold offset -/

/-- Threshold offset σ ∈ {−2, −1, 0, 1, 2}.

    Determines how far above the CC center a person must be to count as
    "tall." Index s ∈ Fin 5 represents σ = s − 2. Higher σ means a more
    exclusive threshold. -/
abbrev Sigma := Fin 5

/-- Integer offset value: index s ↦ σ = s − 2. -/
def sigmaVal (s : Sigma) : Int := (s.val : Int) - 2

/-! ### Shared infrastructure -/

open scoped ENNReal

private theorem worldPrior_nonneg_Q :
    ∀ w : EvalWorld, (0 : ℚ) ≤ worldPrior w := by
  intro w; unfold worldPrior; split <;> norm_num

/-- The utterance's cost as an exponent: the marked form costs 2, the unmarked 1 and silence
nothing, so the speaker's cost factor is `e ^ costN u` with `e = exp(-α)` at the paper's α = 4. -/
def costN : Utterance → ℕ
  | .unmarked => 1
  | .marked   => 2
  | .null     => 0

/-! ### The listener and speaker -/

/-! Companion architecture on `PMF`, parameterized by the cost-factor base
`e` (= `exp(−4)` at the paper's α = 4; only the speaker depends on `e`):

    L₀(w | u, σ) ∝ ⟦u⟧(σ,w) · P(w)               (`meaningE`, `L0v`)
    S₁(u | w, σ) ∝ L₀(w | u, σ)⁴ · e^C(u)         (`Sk`)
    L₁(w, σ | u) ∝ S₁(u | w, σ) · P(w) · P(σ)     (`listener`, `PMF.posterior`)

The prior is baked into the graded L₀ kernel (eq 10, `L₀ ∝ P(w)·⟦u⟧(w)`);
`null` is licensed everywhere, so the speaker normaliser vanishes only at
invalid (zero-prior) worlds, which carry joint weight 0 and are handled by a
`dite` wrapper. Statements are `e`-generic over `0 < e < 1`; `exp(−4)` is
instantiated only in bridging corollaries. -/

/-- Prior-weighted meaning `⟦u⟧(σ,w) · P(w)`, lifted to `ℝ≥0∞`. -/
def meaningE (sem : Utterance → Sigma → EvalWorld → Bool) (σ : Sigma)
    (u : Utterance) (w : EvalWorld) : ℝ≥0∞ :=
  if sem u σ w then ENNReal.ofReal (worldPrior w) else 0

private theorem meaningE_ne_top (sem) (σ) (u) (w) : meaningE sem σ u w ≠ ⊤ := by
  simp only [meaningE]; split
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top

private theorem meaningE_tsum_ne_top (sem) (σ) (u) : (∑' w, meaningE sem σ u w) ≠ ⊤ := by
  rw [tsum_fintype]; exact ENNReal.sum_ne_top.mpr fun w _ => meaningE_ne_top sem σ u w

/-- Literal-listener value `L₀(w | u, σ) = ⟦u⟧(σ,w)·P(w) / D` (well-defined
and `0` on empty extensions, since `0 · ⊤ = 0` in `ℝ≥0∞`). -/
noncomputable def L0v (sem : Utterance → Sigma → EvalWorld → Bool) (σ : Sigma)
    (u : Utterance) (w : EvalWorld) : ℝ≥0∞ :=
  meaningE sem σ u w * (∑' w', meaningE sem σ u w')⁻¹

private theorem L0v_ne_top (sem) (σ) (u) (w) : L0v sem σ u w ≠ ⊤ := by
  rw [L0v]
  rcases eq_or_ne (∑' w', meaningE sem σ u w') 0 with h | h
  · have hm : meaningE sem σ u w = 0 := by
      by_contra hm; exact (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨w, hm⟩) h
    rw [hm, zero_mul]; exact ENNReal.zero_ne_top
  · exact ENNReal.mul_ne_top (meaningE_ne_top sem σ u w) (ENNReal.inv_ne_top.mpr h)

/-- Speaker weight `L₀(w|u,σ)⁴ · e^C(u)`. -/
noncomputable def spkW (sem : Utterance → Sigma → EvalWorld → Bool) (e : ℝ)
    (s : EvalWorld × Sigma) (u : Utterance) : ℝ≥0∞ :=
  (L0v sem s.2 u s.1) ^ 4 * ENNReal.ofReal (e ^ costN u)

private theorem spkW_ne_top (sem) (e) (s) (u) : spkW sem e s u ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.pow_ne_top (L0v_ne_top sem s.2 u s.1)) ENNReal.ofReal_ne_top

private theorem spkW_tsum_ne_top (sem) (e) (s) : (∑' u, spkW sem e s u) ≠ ⊤ := by
  rw [tsum_fintype]; exact ENNReal.sum_ne_top.mpr fun u _ => spkW_ne_top sem e s u

/-- **Speaker** `S₁(· | w, σ) : PMF Utterance`, `dite`-guarded so it is total
even at invalid worlds (where every weight vanishes; those carry joint prior 0). -/
noncomputable def Sk (sem : Utterance → Sigma → EvalWorld → Bool) (e : ℝ)
    (s : EvalWorld × Sigma) : PMF Utterance :=
  if h : (∑' u, spkW sem e s u) ≠ 0 then
    PMF.normalize (spkW sem e s) h (spkW_tsum_ne_top sem e s)
  else PMF.pure .null

/-- Unnormalised joint prior `P(w) · P(σ)` (uniform latent absorbed). -/
def jointW (s : EvalWorld × Sigma) : ℝ≥0∞ := ENNReal.ofReal (worldPrior s.1)

/-- Concise world constructor: `mkW h m = (Fin h, Fin m)`. -/
def mkW (h : Fin 9) (m : Fin 5) : EvalWorld := (h, m)

private theorem worldPrior_pos_of_ne {w : EvalWorld} (h : worldPrior w ≠ 0) :
    (0 : ℝ) < (worldPrior w : ℝ) := by
  have := worldPrior_nonneg_Q w; exact_mod_cast lt_of_le_of_ne this (Ne.symm h)

private theorem jointW_ne_zero {s : EvalWorld × Sigma} (h : worldPrior s.1 ≠ 0) :
    jointW s ≠ 0 := by
  simp only [jointW]; exact (ENNReal.ofReal_pos.mpr (worldPrior_pos_of_ne h)).ne'

private theorem jointW_tsum_ne_zero : (∑' s, jointW s) ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨(mkW 4 2, 0), jointW_ne_zero (by decide)⟩

private theorem jointW_tsum_ne_top : (∑' s, jointW s) ≠ ⊤ := by
  rw [tsum_fintype]; exact ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top

/-- Listener's joint prior over `world × σ`. -/
noncomputable def jointK : PMF (EvalWorld × Sigma) :=
  PMF.normalize jointW jointW_tsum_ne_zero jointW_tsum_ne_top

private theorem jointK_ne_zero {s : EvalWorld × Sigma} (h : worldPrior s.1 ≠ 0) :
    jointK s ≠ 0 := by
  rw [jointK, ← PMF.mem_support_iff, PMF.mem_support_normalize_iff]; exact jointW_ne_zero h

private theorem L0v_ne_zero {sem σ u w} (h : meaningE sem σ u w ≠ 0) :
    L0v sem σ u w ≠ 0 :=
  mul_ne_zero h (ENNReal.inv_ne_zero.mpr (meaningE_tsum_ne_top sem σ u))

private theorem meaningE_ne_zero {sem σ u w} (hlic : sem u σ w = true)
    (hval : worldPrior w ≠ 0) : meaningE sem σ u w ≠ 0 := by
  simp only [meaningE, hlic, if_true]
  exact (ENNReal.ofReal_pos.mpr (worldPrior_pos_of_ne hval)).ne'

private theorem spkW_ne_zero {sem} {e : ℝ} (he0 : 0 < e) {s : EvalWorld × Sigma}
    {u : Utterance} (hlic : sem u s.2 s.1 = true) (hval : worldPrior s.1 ≠ 0) :
    spkW sem e s u ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero 4 (L0v_ne_zero (meaningE_ne_zero hlic hval))) ?_
  exact (ENNReal.ofReal_pos.mpr (pow_pos he0 _)).ne'

private theorem Sk_apply_ne_zero {sem} {e : ℝ} (he0 : 0 < e) {s : EvalWorld × Sigma}
    {u : Utterance} (hnull : sem .null s.2 s.1 = true) (hval : worldPrior s.1 ≠ 0)
    (hlic : sem u s.2 s.1 = true) : Sk sem e s u ≠ 0 := by
  have hsum : (∑' u', spkW sem e s u') ≠ 0 :=
    ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.null, spkW_ne_zero he0 hnull hval⟩
  rw [Sk, dif_pos hsum, ← PMF.mem_support_iff, PMF.mem_support_normalize_iff]
  exact spkW_ne_zero he0 hlic hval

/-- Single-witness discharge of the listener's marginal positivity: a valid
world `w0` licensed for `u` at some `σ0` (with `null` also licensed there). -/
theorem marg_ne_zero {sem} {e : ℝ} (he0 : 0 < e) {u : Utterance}
    {w0 : EvalWorld} {σ0 : Sigma} (hval : worldPrior w0 ≠ 0)
    (hnull : sem .null σ0 w0 = true) (hlic : sem u σ0 w0 = true) :
    PMF.marginal (Sk sem e) jointK u ≠ 0 :=
  PMF.marginal_ne_zero (Sk sem e) jointK u (a := (w0, σ0)) (jointK_ne_zero hval)
    (Sk_apply_ne_zero he0 hnull hval hlic)

/-! ### Structural speaker/listener monotonicity

Evaluativity is proved *structurally*, with no normaliser computation: the
per-latent speaker order follows from **licensing-set inclusion** between two
equal-prior worlds. Two equal-prior worlds with the same licensing bit for `u`
have identical speaker numerators; a wider licensing set only enlarges the
denominator. Hence a world that is licensed for *fewer* alternatives (its
licensing set is contained in the other's) puts *more* mass on the observed
`u`. Only `0 < e` is used (for strict positivity); nothing needs `e < 1`. -/

private theorem spkW_tsum_ne_zero {sem} {e : ℝ} (he0 : 0 < e) {s : EvalWorld × Sigma}
    (hnull : sem .null s.2 s.1 = true) (hv : worldPrior s.1 ≠ 0) :
    (∑' u', spkW sem e s u') ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.null, spkW_ne_zero he0 hnull hv⟩

private theorem Sk_apply_eq {sem} {e : ℝ} {s : EvalWorld × Sigma}
    (hsum : (∑' u', spkW sem e s u') ≠ 0) (u : Utterance) :
    Sk sem e s u = spkW sem e s u * (∑' u', spkW sem e s u')⁻¹ := by
  rw [Sk, dif_pos hsum, PMF.normalize_apply]

private theorem spkW_eq_zero_of_not_lic {sem} {e : ℝ} {s : EvalWorld × Sigma}
    {u : Utterance} (h : sem u s.2 s.1 = false) : spkW sem e s u = 0 := by
  rw [spkW]
  suffices L0v sem s.2 u s.1 = 0 by rw [this, zero_pow (by norm_num), zero_mul]
  rw [L0v, meaningE, if_neg (by simp [h]), zero_mul]

private theorem Sk_eq_zero_of_not_lic {sem} {e : ℝ} {s : EvalWorld × Sigma}
    (hsum : (∑' u', spkW sem e s u') ≠ 0) {u : Utterance} (h : sem u s.2 s.1 = false) :
    Sk sem e s u = 0 := by
  rw [Sk_apply_eq hsum, spkW_eq_zero_of_not_lic h, zero_mul]

private theorem Sk_pos {sem} {e : ℝ} (he0 : 0 < e) {s : EvalWorld × Sigma}
    (hnull : sem .null s.2 s.1 = true) (hv : worldPrior s.1 ≠ 0)
    {u : Utterance} (hlic : sem u s.2 s.1 = true) : 0 < Sk sem e s u := by
  rw [Sk_apply_eq (spkW_tsum_ne_zero he0 hnull hv)]
  exact ENNReal.mul_pos (spkW_ne_zero he0 hlic hv)
    (ENNReal.inv_ne_zero.mpr (spkW_tsum_ne_top sem e s))

/-- **Monotone speaker weight**: with equal world prior, a licensing bit that
is dominated (`wa` licensed for `u` ⟹ `wb` licensed) forces `spkW wa ≤ spkW wb`. -/
private theorem spkW_le_of_prior_lic {sem} {e : ℝ} {u σ} {wa wb : EvalWorld}
    (hp : worldPrior wa = worldPrior wb) (hlic : sem u σ wa = true → sem u σ wb = true) :
    spkW sem e (wa, σ) u ≤ spkW sem e (wb, σ) u := by
  unfold spkW L0v
  gcongr
  simp only [meaningE]
  by_cases ha : sem u σ wa = true
  · rw [if_pos ha, if_pos (hlic ha), hp]
  · rw [if_neg ha]; exact zero_le

private theorem jointK_apply_eq (s : EvalWorld × Sigma) :
    jointK s = jointW s * (∑' s', jointW s')⁻¹ := by
  rw [jointK, PMF.normalize_apply]

private theorem jointK_eq_of_prior {σ : Sigma} {w1 w2 : EvalWorld}
    (h : worldPrior w1 = worldPrior w2) : jointK (w1, σ) = jointK (w2, σ) := by
  rw [jointK_apply_eq, jointK_apply_eq, jointW, jointW, h]

private theorem jointK_ne_top (s : EvalWorld × Sigma) : jointK s ≠ ⊤ :=
  PMF.apply_ne_top jointK s

/-- **Per-latent evaluativity**: at a fixed `σ`, the speaker prefers the
observed `u` for `w2` at least as much as for `w1`, when `w1, w2` share the
world prior, `w1`'s `u`-licensing is contained in `w2`'s (`hu`), and — on the
region where `w1` is `u`-licensed — `w2`'s whole licensing set is contained in
`w1`'s (`halt`). Pure order argument; no normaliser is evaluated. -/
private theorem sk_le_of_incl {sem} {e : ℝ} (he0 : 0 < e) {u σ} {w1 w2 : EvalWorld}
    (hp : worldPrior w1 = worldPrior w2) (hv1 : worldPrior w1 ≠ 0) (hv2 : worldPrior w2 ≠ 0)
    (hnull1 : sem .null σ w1 = true) (hnull2 : sem .null σ w2 = true)
    (hu : sem u σ w1 = true → sem u σ w2 = true)
    (halt : sem u σ w1 = true → ∀ u', sem u' σ w2 = true → sem u' σ w1 = true) :
    Sk sem e (w1, σ) u ≤ Sk sem e (w2, σ) u := by
  by_cases h1 : sem u σ w1 = true
  · rw [Sk_apply_eq (spkW_tsum_ne_zero he0 hnull1 hv1) u,
        Sk_apply_eq (spkW_tsum_ne_zero he0 hnull2 hv2) u]
    refine mul_le_mul' (spkW_le_of_prior_lic hp hu) (ENNReal.inv_le_inv.mpr ?_)
    exact ENNReal.tsum_le_tsum fun u' => spkW_le_of_prior_lic hp.symm (halt h1 u')
  · rw [Sk_eq_zero_of_not_lic (spkW_tsum_ne_zero he0 hnull1 hv1) (Bool.not_eq_true _ ▸ h1)]
    exact zero_le

/-- **Strict per-latent gap**: where `w1` is *not* `u`-licensed but `w2` is,
`w1` contributes `0` and `w2` contributes a positive speaker mass. -/
private theorem sk_lt_of_gap {sem} {e : ℝ} (he0 : 0 < e) {u σ} {w1 w2 : EvalWorld}
    (hv1 : worldPrior w1 ≠ 0) (hv2 : worldPrior w2 ≠ 0)
    (hnull1 : sem .null σ w1 = true) (hnull2 : sem .null σ w2 = true)
    (h1 : sem u σ w1 = false) (h2 : sem u σ w2 = true) :
    Sk sem e (w1, σ) u < Sk sem e (w2, σ) u := by
  rw [Sk_eq_zero_of_not_lic (spkW_tsum_ne_zero he0 hnull1 hv1) h1]
  exact Sk_pos he0 hnull2 hv2 h2

/-- Strict monotonicity of a finite `ℝ≥0∞` sum from a single strictly-larger
term (the others being finite): `Finset.sum_lt_sum` is unavailable because
`ℝ≥0∞` is not cancellative. -/
private theorem ennreal_sum_lt_sum {ι} [DecidableEq ι] {s : Finset ι} {f g : ι → ℝ≥0∞}
    (hfg : ∀ i ∈ s, f i ≤ g i) {i₀ : ι} (hi₀ : i₀ ∈ s) (hlt : f i₀ < g i₀)
    (htop : ∀ i ∈ s, g i ≠ ⊤) : ∑ i ∈ s, f i < ∑ i ∈ s, g i := by
  rw [← Finset.add_sum_erase s f hi₀, ← Finset.add_sum_erase s g hi₀]
  have htop' : ∑ x ∈ s.erase i₀, g x ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i hi => htop i (Finset.mem_of_mem_erase hi)
  calc f i₀ + ∑ x ∈ s.erase i₀, f x
      ≤ f i₀ + ∑ x ∈ s.erase i₀, g x := by
        gcongr with i hi; exact hfg i (Finset.mem_of_mem_erase hi)
    _ < g i₀ + ∑ x ∈ s.erase i₀, g x := ENNReal.add_lt_add_right htop' hlt

/-- **Evaluativity from licensing inclusion** (Tier A). For two equal-prior
worlds with `w1`'s `u`-licensing contained in `w2`'s (`hu`) and, on that
support, `w2`'s whole licensing contained in `w1`'s (`halt`), plus a `σ₀` where
only `w2` is `u`-licensed, the listener strictly prefers `w2`: `L₁(w1|u) <
L₁(w2|u)`. Pure order argument — no normaliser is evaluated, and only `0 < e`
is used. -/
private theorem evaluative_of_incl {sem} {e : ℝ} (he0 : 0 < e) {u : Utterance}
    {w1 w2 : EvalWorld} (marg : PMF.marginal (Sk sem e) jointK u ≠ 0)
    (hp : worldPrior w1 = worldPrior w2) (hv1 : worldPrior w1 ≠ 0) (hv2 : worldPrior w2 ≠ 0)
    (hnull1 : ∀ σ, sem .null σ w1 = true) (hnull2 : ∀ σ, sem .null σ w2 = true)
    (hu : ∀ σ, sem u σ w1 = true → sem u σ w2 = true)
    (halt : ∀ σ, sem u σ w1 = true → ∀ u', sem u' σ w2 = true → sem u' σ w1 = true)
    (σ₀ : Sigma) (hgap1 : sem u σ₀ w1 = false) (hgap2 : sem u σ₀ w2 = true) :
    (RSA.Canonical.L1 (Sk sem e) jointK u marg).fst w1
      < (RSA.Canonical.L1 (Sk sem e) jointK u marg).fst w2 := by
  rw [RSA.Canonical.L1_world_prefers_iff]
  refine ennreal_sum_lt_sum (fun σ _ => ?_) (Finset.mem_univ σ₀) ?_
    (fun σ _ => ENNReal.mul_ne_top (jointK_ne_top _) (PMF.apply_ne_top _ _))
  · rw [jointK_eq_of_prior hp]
    gcongr
    exact sk_le_of_incl he0 hp hv1 hv2 (hnull1 σ) (hnull2 σ) (hu σ) (halt σ)
  · rw [jointK_eq_of_prior hp]
    exact ENNReal.mul_lt_mul_right (jointK_ne_zero hv2) (jointK_ne_top _)
      (sk_lt_of_gap he0 hv1 hv2 (hnull1 σ₀) (hnull2 σ₀) hgap1 hgap2)

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
everywhere, which is what keeps the speaker's normaliser positive. -/
def meaning (c : Form) (u : Utterance) (σ : Sigma) (w : EvalWorld) : Bool :=
  match u with
  | .null => true
  | .unmarked => standardMet c u w && decide (measured c w ≥ muVal w + sigmaVal σ)
  | .marked => standardMet c u w && decide (measured c w ≤ muVal w + sigmaVal σ)

/-- Every utterance of every construction is true at some world of positive prior, so the
listener's marginal never vanishes. -/
theorem marg_ne_zero_meaning (c : Form) (u : Utterance) {e : ℝ} (he0 : 0 < e) :
    PMF.marginal (Sk (meaning c) e) jointK u ≠ 0 := by
  obtain ⟨w0, σ0, hval, hlic⟩ :
      ∃ (w : EvalWorld) (σ : Sigma), worldPrior w ≠ 0 ∧ meaning c u σ w = true := by
    cases c <;> cases u <;> decide
  exact marg_ne_zero he0 hval rfl hlic

/-- The pragmatic listener after hearing `u` in construction `c`. -/
noncomputable def L1 (c : Form) (u : Utterance) {e : ℝ} (he0 : 0 < e) :
    PMF (EvalWorld × Sigma) :=
  RSA.Canonical.L1 (Sk (meaning c) e) jointK u (marg_ne_zero_meaning c u he0)

/-- What makes an utterance shift the listener from `w1` towards `w2`: the two worlds carry the
same nonzero prior, the utterance is true at `w2` whenever it is true at `w1`, every alternative
available at `w2` under such a threshold is available at `w1` too, and at the threshold `σ₀` the
utterance separates the two worlds. -/
def ShiftsTo (c : Form) (u : Utterance) (w1 w2 : EvalWorld) (σ₀ : Sigma) : Prop :=
  worldPrior w1 = worldPrior w2 ∧ worldPrior w1 ≠ 0 ∧ worldPrior w2 ≠ 0 ∧
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
    (L1 c u he0).fst w1 < (L1 c u he0).fst w2 := by
  obtain ⟨hp, hv1, hv2, hu, halt, hgap1, hgap2⟩ := h
  exact evaluative_of_incl he0 _ hp hv1 hv2 (fun _ => rfl) (fun _ => rfl) hu halt σ₀ hgap1 hgap2

/-! ### The positive construction

The two worlds compared below sit one unit above and one unit below the class centre and carry the
same prior, so any asymmetry between them is pragmatic. The paper's expected deviations are 2.08
for *tall* and −3.18 for *short*: the marked antonym is the more evaluative of the two, since the
extra cost it carries signals that the speaker's reason for choosing it was strong. -/

theorem pos_tall_evaluative (e : ℝ) (he0 : 0 < e) :
    (L1 .positive .unmarked he0).fst (mkW 5 2) > (L1 .positive .unmarked he0).fst (mkW 3 2) :=
  shifts he0 (σ₀ := 2) (by decide)

theorem pos_short_evaluative (e : ℝ) (he0 : 0 < e) :
    (L1 .positive .marked he0).fst (mkW 3 2) > (L1 .positive .marked he0).fst (mkW 5 2) :=
  shifts he0 (σ₀ := 2) (by decide)

/-! ### The exact equative

The equative fixes the subject's height at the standard, so what the listener learns is where the
standard sits relative to the class centre. The two worlds compared hold the height at the standard
and vary the centre below and above it. The paper's expected deviations are −1.06 for the marked
form and 0.84 for the unmarked one: the marked antonym shifts strongly and the unmarked one weakly,
which is the antonym-sensitive pattern the categorical account states as a dichotomy. -/

theorem eq_marked_evaluative (e : ℝ) (he0 : 0 < e) :
    (L1 .exactEquative .marked he0).fst (mkW 4 4) >
      (L1 .exactEquative .marked he0).fst (mkW 4 0) :=
  shifts he0 (σ₀ := 0) (by decide)

theorem eq_unmarked_weakly_evaluative (e : ℝ) (he0 : 0 < e) :
    (L1 .exactEquative .unmarked he0).fst (mkW 4 0) >
      (L1 .exactEquative .unmarked he0).fst (mkW 4 4) :=
  shifts he0 (σ₀ := 4) (by decide)

/-! ### The minimum-standard equative

The unmarked and marked forms of *at least as tall as* are not synonymous, unlike those of the
exact equative, so the antonyms compete only partly and the evaluativity predicted falls between
the exact equative's and the comparative's. The paper's expected deviations are −1.52 for the marked
form and 0.11 for the unmarked one, the weakest evaluative effect of any construction. -/

theorem geq_marked_evaluative (e : ℝ) (he0 : 0 < e) :
    (L1 .minimumEquative .marked he0).fst (mkW 4 4) >
      (L1 .minimumEquative .marked he0).fst (mkW 4 0) :=
  shifts he0 (σ₀ := 0) (by decide)

theorem geq_unmarked_barely_evaluative (e : ℝ) (he0 : 0 < e) :
    (L1 .minimumEquative .unmarked he0).fst (mkW 4 0) >
      (L1 .minimumEquative .unmarked he0).fst (mkW 4 4) :=
  shifts he0 (σ₀ := 4) (by decide)

/-! ### The comparative

*Taller than K* and *shorter than K* have no semantic overlap at all, so the antonyms do not
compete and nothing pressures an evaluative inference. The paper's expected deviations here are
−0.74 for the unmarked form and −0.44 for the marked one, both close to zero: the listener does
infer something about where the standard sits, but that is a consequence of learning a relative
height, not evaluativity. -/

theorem comp_marked_weak (e : ℝ) (he0 : 0 < e) :
    (L1 .comparative .marked he0).fst (mkW 3 2) > (L1 .comparative .marked he0).fst (mkW 3 0) :=
  shifts he0 (σ₀ := 2) (by decide)

/-! Hearing the unmarked comparative does not make the listener infer that the standard is high;
the inference runs the other way, since a subject exceeding the standard leaves the standard room
to be below average. That direction is the one case whose proof needs exact values rather than the
inclusion argument, so the normalisers are evaluated below. -/

private theorem meaningE_eq_ofReal (sem) (σ) (u) (w) :
    meaningE sem σ u w = ENNReal.ofReal (if sem u σ w then worldPrior w else 0) := by
  unfold meaningE; split <;> simp

/-- Kernel-clean evaluation of a graded-`L₀` normaliser: the `ℝ≥0∞` fan-out
sum equals `ofReal` of the concrete ℚ mass sum. -/
private theorem dval {sem σ u} {D : ℚ}
    (h : (∑ w : Fin 9 × Fin 5, if sem u σ w then worldPrior w else 0) = D) :
    (∑' w, meaningE sem σ u w) = ENNReal.ofReal D := by
  rw [tsum_fintype, Finset.sum_congr rfl fun w _ => meaningE_eq_ofReal sem σ u w,
    ← ENNReal.ofReal_sum_of_nonneg fun w _ => by
      split
      · exact_mod_cast worldPrior_nonneg_Q w
      · exact le_refl 0]
  congr 1
  rw [← h, Rat.cast_sum]
  exact Finset.sum_congr rfl fun w _ => by split <;> simp

private theorem dval_unm :
    (∑' w, meaningE (meaning .comparative) (1 : Sigma) .unmarked w) = ENNReal.ofReal 25 :=
  dval (by decide +kernel)

private theorem dval_null :
    (∑' w, meaningE (meaning .comparative) (1 : Sigma) .null w) = ENNReal.ofReal 120 :=
  dval (by decide +kernel)

private theorem wp53 : worldPrior (mkW 5 3) = 10 := by decide +kernel

private theorem L0v_unm :
    L0v (meaning .comparative) (1 : Sigma) .unmarked (mkW 5 3) = ENNReal.ofReal (2 / 5) := by
  unfold L0v
  rw [dval_unm, meaningE_eq_ofReal, if_pos (by decide),
    show ((worldPrior (mkW 5 3) : ℝ)) = 10 by rw [wp53]; norm_num,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 25),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 10)]
  norm_num

private theorem L0v_null :
    L0v (meaning .comparative) (1 : Sigma) .null (mkW 5 3) = ENNReal.ofReal (1 / 12) := by
  unfold L0v
  rw [dval_null, meaningE_eq_ofReal, if_pos (by decide),
    show ((worldPrior (mkW 5 3) : ℝ)) = 10 by rw [wp53]; norm_num,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 120),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 10)]
  norm_num

private theorem spkW_unm (e : ℝ) :
    spkW (meaning .comparative) e (mkW 5 3, (1 : Sigma)) .unmarked
      = ENNReal.ofReal ((2 / 5) ^ 4 * e) := by
  unfold spkW
  rw [L0v_unm, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2 / 5),
    show costN .unmarked = 1 from rfl, pow_one, ← ENNReal.ofReal_mul (by positivity)]

private theorem spkW_null (e : ℝ) :
    spkW (meaning .comparative) e (mkW 5 3, (1 : Sigma)) .null = ENNReal.ofReal ((1 / 12) ^ 4) := by
  unfold spkW
  rw [L0v_null, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1 / 12),
    show costN .null = 0 from rfl, pow_zero, ENNReal.ofReal_one, mul_one]

private theorem spkW_marked (e : ℝ) :
    spkW (meaning .comparative) e (mkW 5 3, (1 : Sigma)) .marked = 0 :=
  spkW_eq_zero_of_not_lic (by decide)

private theorem spkW_tsum (e : ℝ) :
    (∑' u, spkW (meaning .comparative) e (mkW 5 3, (1 : Sigma)) u)
      = ENNReal.ofReal ((2 / 5) ^ 4 * e) + ENNReal.ofReal ((1 / 12) ^ 4) := by
  rw [tsum_fintype,
    show (Finset.univ : Finset Utterance) = {.unmarked, .marked, .null} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    spkW_unm, spkW_marked, spkW_null, zero_add]

private theorem Sk_bound {e : ℝ} (he0 : 0 < e) (he_lo : (1 : ℝ) / 100 ≤ e) :
    (5 : ℝ≥0∞) < 10 * Sk (meaning .comparative) e (mkW 5 3, (1 : Sigma)) .unmarked := by
  have hA : (0 : ℝ) < (2 / 5) ^ 4 * e := by positivity
  have hsum : (∑' u', spkW (meaning .comparative) e (mkW 5 3, (1 : Sigma)) u') ≠ 0 := by
    rw [spkW_tsum]
    exact ((ENNReal.ofReal_pos.mpr hA).trans_le le_self_add).ne'
  rw [Sk_apply_eq hsum, spkW_unm, spkW_tsum, ← ENNReal.ofReal_add hA.le (by positivity),
    ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul hA.le,
    show (10 : ℝ≥0∞) = ENNReal.ofReal 10 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
    show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by norm_num, ENNReal.ofReal_lt_ofReal_iff (by positivity),
    ← mul_assoc, ← div_eq_mul_inv, lt_div_iff₀ (by positivity)]
  nlinarith [he_lo]

private theorem jointK_w1 (σ : Sigma) : jointK (mkW 5 1, σ) = jointK (mkW 5 1, 1) := by
  simp only [jointK_apply_eq, jointW]

private theorem jointK_w3_ratio :
    jointK (mkW 5 3, (1 : Sigma)) = 10 * jointK (mkW 5 1, (1 : Sigma)) := by
  rw [jointK_apply_eq, jointK_apply_eq, jointW, jointW, wp53,
    show worldPrior (mkW 5 1) = 1 from by decide +kernel, ← mul_assoc]
  congr 1
  rw [Rat.cast_one, ENNReal.ofReal_one, mul_one, Rat.cast_ofNat, ENNReal.ofReal_ofNat]

/-- Counter-evaluative comparative — a **prior-magnitude** effect, not a
licensing one. Unlike the seven Tier-A predictions (which hold for every cost
base `e ∈ (0,1)` via `evaluative_of_incl`'s bare `0 < e`), here the speaker
distribution depends on a world only through its *licensing set* (the prior
cancels inside `Sk`), so the 10:1 world prior of `mkW 5 3` (k at the CC mean)
over `mkW 5 1` (k above it) is the sole asymmetry and it dominates.

The prior dominates only when markedness costs are not extreme. The sharp
threshold is `e ≥ (D_unm(1)/D_null)⁴ = (25/120)⁴ ≈ 0.0019`: for `e` below it,
the cost factor `e^C` so heavily discounts the informative "taller than"
utterance in the high-threshold worlds that the informativity cost dominates
the prior mass and the inequality flips. We therefore assume `1/100 ≤ e`
(comfortably above the threshold, and met by the paper's `e = exp(−4) ≈ 0.018`;
see `comp_unmarked_counter_evaluative_exp`). -/
theorem comp_unmarked_counter_evaluative (e : ℝ) (he0 : 0 < e) (he_lo : (1 : ℝ)/100 ≤ e) :
    (L1 .comparative .unmarked he0).fst (mkW 5 3) >
      (L1 .comparative .unmarked he0).fst (mkW 5 1) := by
  -- `L1_world_prefers_iff` reduces to a comparison of joint-weighted speaker
  -- sums. `jointK(w,·)` is constant in σ, with a 10:1 prior for `mkW 5 3` over
  -- `mkW 5 1`; `Sk ≤ 1` bounds `mkW 5 1`'s five terms by `5·jointK(w1,·)`, while
  -- `mkW 5 3`'s σ = 1 term alone gives `10·jointK(w1,·)·Sk(w2,1)` with
  -- `Sk(w2,1) > 1/2` (`Sk_bound`) — so the prior mass wins.
  simp only [L1, gt_iff_lt, RSA.Canonical.L1_world_prefers_iff]
  calc ∑ σ, jointK (mkW 5 1, σ) * Sk (meaning .comparative) e (mkW 5 1, σ) .unmarked
      ≤ ∑ σ : Sigma, jointK (mkW 5 1, 1) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [jointK_w1 σ]
        calc jointK (mkW 5 1, 1) * Sk (meaning .comparative) e (mkW 5 1, σ) .unmarked
            ≤ jointK (mkW 5 1, 1) * 1 := by gcongr; exact PMF.coe_le_one _ _
          _ = jointK (mkW 5 1, 1) := mul_one _
    _ = 5 * jointK (mkW 5 1, 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
    _ < jointK (mkW 5 3, 1) * Sk (meaning .comparative) e (mkW 5 3, 1) .unmarked := by
        rw [jointK_w3_ratio, mul_right_comm]
        exact ENNReal.mul_lt_mul_left (jointK_ne_zero (by decide +kernel)) (jointK_ne_top _)
          (Sk_bound he0 he_lo)
    _ ≤ ∑ σ, jointK (mkW 5 3, σ) * Sk (meaning .comparative) e (mkW 5 3, σ) .unmarked :=
        Finset.single_le_sum
          (f := fun σ => jointK (mkW 5 3, σ) * Sk (meaning .comparative) e (mkW 5 3, σ) .unmarked)
          (fun σ _ => zero_le) (Finset.mem_univ (1 : Sigma))

/-- The counter-evaluative comparative at the paper's cost base `e = exp(−4)`.
The hypothesis `1/100 ≤ exp(−4)` reduces to `exp 4 ≤ 100`, and
`exp 4 = (exp 1)⁴ < 2.7182818286⁴ ≈ 54.6 < 100`. -/
theorem comp_unmarked_counter_evaluative_exp :
    (L1 .comparative .unmarked (Real.exp_pos (-4))).fst (mkW 5 3)
      > (L1 .comparative .unmarked (Real.exp_pos (-4))).fst (mkW 5 1) := by
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
    (L1 .positive .unmarked he0).fst (mkW 5 2) > (L1 .positive .unmarked he0).fst (mkW 3 2) ∧
    (L1 .positive .marked he0).fst (mkW 3 2) > (L1 .positive .marked he0).fst (mkW 5 2) ∧
    -- Equative: Neo-Gricean says marked-only; RSA shows marked shift
    ¬ Evaluative .equative .positive ∧
    Evaluative .equative .negative ∧
    (L1 .exactEquative .marked he0).fst (mkW 4 4) > (L1 .exactEquative .marked he0).fst (mkW 4 0) ∧
    -- Comparative: both say not evaluative
    ¬ Evaluative .comparative .positive ∧
    ¬ Evaluative .comparative .negative :=
  ⟨by decide, by decide,
   pos_tall_evaluative e he0, pos_short_evaluative e he0,
   by decide, by decide,
   eq_marked_evaluative e he0,
   by decide, by decide⟩

end BumfordRett2021
