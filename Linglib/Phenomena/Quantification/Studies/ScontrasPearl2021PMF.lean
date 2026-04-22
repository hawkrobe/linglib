import Linglib.Theories.Pragmatics.RSA.Operators
import Linglib.Phenomena.Quantification.Studies.ScontrasPearl2021
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# @cite{scontras-pearl-2021} on mathlib `PMF` (Phase 2 stress test)
@cite{scontras-pearl-2021}

Fourth stress test for the Phase-2 architecture, after @cite{frank-goodman-2012},
@cite{kao-etal-2014-metaphor}, and @cite{goodman-stuhlmuller-2013}. ScontrasPearl
contributes one new ingredient that none of the previous pilots exercised:

* **Product latent variable**: the latent state is `scope × QUD` (six values
  for the EveryNot model). `PMF.bind` over the product latent prior is the
  natural marginalisation idiom — exactly mathlib's pattern for chained
  random variables.

The architecture is otherwise the @cite{kao-etal-2014-metaphor} shape:

* L0 is uniform on the extension of a Boolean meaning (`RSA.L0OfBoolMeaning`)
* S1 is `(QUD-projected L0 sum)^α` (rpow, not softmax-of-log)
* L1 is `PMF.posterior` of `marginalSpeaker = latentPrior.bind S1g`

Unlike GS2013, there is no observation kernel and no real-valued log score —
the rpow shape lifts to `ℝ≥0∞` cleanly via `ENNReal.rpow`.

## Coverage discharge

The `null` utterance has full extension (true at every world), so its L0 is
uniform on `Finset.univ` and `qudProjectE q (L0 s null) w > 0` for every
`(s, q, w)`. This single witness drives every `PMF.normalize` precondition
in the file (S1g positivity at every `(lat, w)`, marginal positivity at every
`(w, u)` for `u = .null`, and L1 marginal positivity).

The non-trivial `everyNot` utterance has narrower extension; cover at L1 for
`u = .everyNot` follows from `worldPrior` putting positive mass on `.zero`
(true under both scopes) plus the L0 of either scope being non-zero there.

## Scope of this file

EveryNot model only. The TwoNot variant (10 latents = 2 scopes × 5 QUDs,
5-world domain) follows the same pattern; deferring it keeps this file
focused on demonstrating the product-latent `bind` pattern is well-formed.

The 8 paper findings (S2 endorsement orderings) become L1/S2 inequalities
left as `sorry` pending the PMF-shaped `rsa_predict` tactic (Task #36).

## Reused from `ScontrasPearl2021.lean`

* `JumpOutcome`, `ScopeReading`, `EveryNot.Utt`, `EveryNot.QUD`,
  `EveryNot.Latent`, `EveryNot.uttMeaning`, `EveryNot.Latent.scope`/`.qud`
-/

set_option autoImplicit false

namespace ScontrasPearl2021.EveryNot.PMF

open scoped ENNReal
open ScontrasPearl2021 ScontrasPearl2021.EveryNot

/-! ## §1. World prior — uniform on `JumpOutcome` -/

noncomputable def worldPrior : PMF JumpOutcome := PMF.uniformOfFintype JumpOutcome

theorem worldPrior_ne_zero (w : JumpOutcome) : worldPrior w ≠ 0 :=
  (worldPrior.mem_support_iff w).mp (PMF.mem_support_uniformOfFintype w)

/-! ## §2. L0 — literal listener as `RSA.L0OfBoolMeaning`

`uttMeaning lat.scope u w` is `Bool`-valued, so L0 is uniform on the
extension. Each scope reading induces its own L0 distribution (the meaning
function's first argument is `ScopeReading`, not just `Utt`). -/

/-- Extension of `uttMeaning s u`: the worlds where `u` is true under scope `s`. -/
abbrev extension (s : ScopeReading) (u : Utt) : Finset JumpOutcome :=
  RSA.extensionOf (uttMeaning s) u

theorem extension_nonempty (s : ScopeReading) (u : Utt) : (extension s u).Nonempty := by
  -- `.zero` is true under every (s, u) pair: null is universally true, and
  -- both surface and inverse readings of everyNot are true at `.zero`.
  refine ⟨.zero, ?_⟩
  rw [RSA.mem_extensionOf]
  cases s <;> cases u <;> rfl

/-- Literal listener: uniform on the extension of `uttMeaning lat.scope u`. -/
noncomputable def L0 (s : ScopeReading) (u : Utt) : PMF JumpOutcome :=
  RSA.L0OfBoolMeaning (uttMeaning s) u (extension_nonempty s u)

@[simp] theorem mem_support_L0_iff (s : ScopeReading) (u : Utt) (w : JumpOutcome) :
    w ∈ (L0 s u).support ↔ uttMeaning s u w = true :=
  RSA.mem_support_L0OfBoolMeaning_iff _ _

theorem L0_apply_of_true {s : ScopeReading} {u : Utt} {w : JumpOutcome}
    (h : uttMeaning s u w = true) :
    L0 s u w = ((extension s u).card : ℝ≥0∞)⁻¹ :=
  RSA.L0OfBoolMeaning_apply_of_mem _ h

theorem L0_apply_of_false {s : ScopeReading} {u : Utt} {w : JumpOutcome}
    (h : uttMeaning s u w ≠ true) :
    L0 s u w = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ h

/-! ## §3. QUD projection (ENNReal version)

ENNReal lift of `qudProjectInline`: sums L0 mass over the equivalence class
of `w` under QUD `q`. Returns `ℝ≥0∞` so that the rpow speaker score lives
in `ℝ≥0∞` end-to-end. -/

/-- QUD projection on `ℝ≥0∞`-valued functions. -/
noncomputable def qudProjectE (q : QUD) (f : JumpOutcome → ℝ≥0∞) (w : JumpOutcome) : ℝ≥0∞ :=
  match q, w with
  | .howMany, .zero => f .zero
  | .howMany, .one  => f .one
  | .howMany, .two  => f .two
  | .all_,    .zero => f .zero + f .one
  | .all_,    .one  => f .zero + f .one
  | .all_,    .two  => f .two
  | .none_,   .zero => f .zero
  | .none_,   .one  => f .one + f .two
  | .none_,   .two  => f .one + f .two

/-- The projection at `w` under QUD `q` is bounded above by the total mass
of `f` (a finite sum of pieces of `Σ f`). Used to discharge `≠ ∞`. -/
theorem qudProjectE_ne_top {q : QUD} {f : JumpOutcome → ℝ≥0∞} {w : JumpOutcome}
    (hf : ∀ w, f w ≠ ∞) : qudProjectE q f w ≠ ∞ := by
  cases q <;> cases w <;> simp only [qudProjectE] <;>
    first
    | exact hf _
    | exact ENNReal.add_ne_top.mpr ⟨hf _, hf _⟩

/-- The projection of L0 includes the mass at `w` itself (since `w` is in
its own equivalence class for every QUD). Used to derive positivity of the
rpow speaker score at the witness world. -/
theorem qudProjectE_self_ge {q : QUD} {f : JumpOutcome → ℝ≥0∞} (w : JumpOutcome) :
    f w ≤ qudProjectE q f w := by
  cases q <;> cases w <;> simp only [qudProjectE] <;>
    first
    | exact le_refl _
    | exact le_self_add
    | exact le_add_self

/-- If L0 is non-zero at `w`, the QUD-projected sum is non-zero at `w`. -/
theorem qudProjectE_ne_zero_of_self {q : QUD} {f : JumpOutcome → ℝ≥0∞} {w : JumpOutcome}
    (h : f w ≠ 0) : qudProjectE q f w ≠ 0 := by
  intro hp
  exact h (le_antisymm (hp ▸ qudProjectE_self_ge w) (zero_le _))

/-! ## §4. S1g — speaker conditional on (latent, world)

`S1g lat w u ∝ (qudProjectE lat.qud (L0 lat.scope u) w)^α`. The cover witness
is the `null` utterance: its L0 is uniform on `Finset.univ`, so the projection
is positive at every `w` (every QUD class contains some world where `null`'s
L0 is positive — and `null`'s L0 is positive everywhere). -/

/-- The unnormalised score: `(qudProjectE lat.qud (L0 lat.scope u) w)^α`. -/
noncomputable def s1Score (α : ℝ) (lat : Latent) (w : JumpOutcome) (u : Utt) : ℝ≥0∞ :=
  (qudProjectE lat.qud (fun w' => L0 lat.scope u w') w) ^ α

theorem L0_null_ne_zero (s : ScopeReading) (w : JumpOutcome) :
    L0 s .null w ≠ 0 := by
  rw [← PMF.mem_support_iff, mem_support_L0_iff]
  cases s <;> rfl

theorem s1Score_null_ne_zero {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) :
    s1Score α lat w .null ≠ 0 := by
  refine (not_congr (ENNReal.rpow_eq_zero_iff_of_pos hα)).mpr ?_
  exact qudProjectE_ne_zero_of_self (L0_null_ne_zero _ _)

theorem L0_ne_top (s : ScopeReading) (u : Utt) (w : JumpOutcome) : L0 s u w ≠ ∞ :=
  PMF.apply_ne_top _ _

theorem s1Score_ne_top {α : ℝ} (hα : 0 ≤ α) (lat : Latent) (w : JumpOutcome) (u : Utt) :
    s1Score α lat w u ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg hα (qudProjectE_ne_top (L0_ne_top _ _))

theorem s1Score_tsum_ne_zero {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) :
    ∑' u, s1Score α lat w u ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.null, s1Score_null_ne_zero hα lat w⟩

theorem s1Score_tsum_ne_top {α : ℝ} (hα : 0 ≤ α) (lat : Latent) (w : JumpOutcome) :
    ∑' u, s1Score α lat w u ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype fun u => s1Score_ne_top hα lat w u

/-- Pragmatic speaker conditioned on (latent, world). -/
noncomputable def S1g {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) : PMF Utt :=
  PMF.normalize (s1Score α lat w) (s1Score_tsum_ne_zero hα lat w)
    (s1Score_tsum_ne_top hα.le lat w)

theorem mem_support_S1g_iff {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) (u : Utt) :
    u ∈ (S1g hα lat w).support ↔ s1Score α lat w u ≠ 0 := by
  rw [S1g, PMF.mem_support_normalize_iff]

theorem S1g_null_ne_zero {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) :
    S1g hα lat w .null ≠ 0 := by
  rw [← PMF.mem_support_iff, mem_support_S1g_iff]
  exact s1Score_null_ne_zero hα lat w

/-! ## §5. Marginal speaker — `PMF.bind` over the latent prior

The product latent is `scope × QUD` (flattened to `Latent`). `PMF.bind`
against a `latentPrior : PMF Latent` is mathlib's idiom for marginalising
over a chained random variable — exactly what's needed here. -/

/-- Speaker marginalised over latent state. -/
noncomputable def marginalSpeaker {α : ℝ} (hα : 0 < α) (latentPrior : PMF Latent)
    (w : JumpOutcome) : PMF Utt :=
  latentPrior.bind (fun lat => S1g hα lat w)

/-- The cover witness lifts to the marginal speaker: if any latent has
positive prior mass and S1g is non-zero on `null`, the marginal speaker is
non-zero on `null`. Used to discharge `marginal ≠ 0` for L1 at `u = null`. -/
theorem marginalSpeaker_null_ne_zero {α : ℝ} (hα : 0 < α)
    {latentPrior : PMF Latent} {lat : Latent} (hlat : latentPrior lat ≠ 0)
    (w : JumpOutcome) :
    marginalSpeaker hα latentPrior w .null ≠ 0 := by
  unfold marginalSpeaker
  rw [PMF.bind_apply]
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨lat, mul_ne_zero hlat ?_⟩
  exact S1g_null_ne_zero hα lat w

/-! ## §6. L1 — Bayesian inversion via `PMF.posterior` -/

theorem L1_marginal_null_ne_zero {α : ℝ} (hα : 0 < α)
    {latentPrior : PMF Latent} {lat : Latent} (hlat : latentPrior lat ≠ 0) :
    PMF.marginal (marginalSpeaker hα latentPrior) worldPrior Utt.null ≠ 0 :=
  PMF.marginal_ne_zero _ worldPrior Utt.null
    (worldPrior_ne_zero .zero) (marginalSpeaker_null_ne_zero hα hlat .zero)

/-- The everyNot utterance also has L1-marginal cover: at world `.zero`,
both scope readings make `everyNot` true, so L0 puts positive mass there,
S1g(everyNot|lat,.zero) > 0 for every lat (since qudProject ≥ L0(.zero) > 0),
and the marginal speaker is positive on everyNot at `.zero`. -/
theorem marginalSpeaker_everyNot_at_zero_ne_zero {α : ℝ} (hα : 0 < α)
    {latentPrior : PMF Latent} {lat : Latent} (hlat : latentPrior lat ≠ 0) :
    marginalSpeaker hα latentPrior .zero .everyNot ≠ 0 := by
  unfold marginalSpeaker
  rw [PMF.bind_apply]
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨lat, mul_ne_zero hlat ?_⟩
  rw [← PMF.mem_support_iff, S1g, PMF.mem_support_normalize_iff]
  refine (not_congr (ENNReal.rpow_eq_zero_iff_of_pos hα)).mpr ?_
  refine qudProjectE_ne_zero_of_self ?_
  rw [← PMF.mem_support_iff, mem_support_L0_iff]
  cases lat.scope <;> rfl

theorem L1_marginal_everyNot_ne_zero {α : ℝ} (hα : 0 < α)
    {latentPrior : PMF Latent} {lat : Latent} (hlat : latentPrior lat ≠ 0) :
    PMF.marginal (marginalSpeaker hα latentPrior) worldPrior Utt.everyNot ≠ 0 :=
  PMF.marginal_ne_zero _ worldPrior Utt.everyNot
    (worldPrior_ne_zero .zero) (marginalSpeaker_everyNot_at_zero_ne_zero hα hlat)

/-- Pragmatic listener: `PMF.posterior` of the latent-marginalised speaker
against the world prior. The "L1 = Bayesian inversion" claim is true by
construction (`PMF.posterior` IS Bayes' rule). -/
noncomputable def L1 {α : ℝ} (hα : 0 < α) (latentPrior : PMF Latent) (u : Utt)
    (hMarg : PMF.marginal (marginalSpeaker hα latentPrior) worldPrior u ≠ 0) :
    PMF JumpOutcome :=
  PMF.posterior (marginalSpeaker hα latentPrior) worldPrior u hMarg

theorem mem_support_L1_iff {α : ℝ} (hα : 0 < α) (latentPrior : PMF Latent) (u : Utt)
    (hMarg : PMF.marginal (marginalSpeaker hα latentPrior) worldPrior u ≠ 0)
    (w : JumpOutcome) :
    w ∈ (L1 hα latentPrior u hMarg).support ↔
      worldPrior w ≠ 0 ∧ marginalSpeaker hα latentPrior w u ≠ 0 :=
  PMF.mem_support_posterior_iff _ _ _ _ _

/-! ## §7. Findings — paper's S2 endorsement orderings

The paper's central claims (Figure 2) are S2 endorsement orderings at the
partial world `.one`, robust across prior configurations. Each is an L1
inequality discharged via the Bayes identity (S2(u|w) ∝ L1(w|u) over u).

Stated below as `L1` apply inequalities with `sorry` per CLAUDE.md "Prefer
`sorry` over weakening theorem statements". The PMF-shaped `rsa_predict`
tactic (Task #36) will discharge these as finite ℝ≥0∞ arithmetic. -/

namespace Findings

/-! ### Baseline (b_suc = 0.1, uniform scope and QUD)

These mirror `baseline_L1_w0_gt_w1` and `baseline_L1_w1_gt_w2` from the
non-PMF file. Take any `latentPrior` with positive mass everywhere — the
uniform on `Latent` works. -/

/-- Surface-scope-favored latent prior: every latent has positive mass.
Used as the default `latentPrior` for the findings below. -/
noncomputable def uniformLatentPrior : PMF Latent := PMF.uniformOfFintype Latent

theorem uniformLatentPrior_ne_zero (lat : Latent) : uniformLatentPrior lat ≠ 0 :=
  (uniformLatentPrior.mem_support_iff lat).mp (PMF.mem_support_uniformOfFintype lat)

/-- Baseline L1 ordering at the partial world: `L1(zero | everyNot) > L1(one | everyNot)`.
Both scopes agree `.zero` is true; only inverse scope makes `.one` true. -/
theorem baseline_L1_zero_gt_one {α : ℝ} (hα : 0 < α) :
    (L1 hα uniformLatentPrior .everyNot
        (L1_marginal_everyNot_ne_zero hα (uniformLatentPrior_ne_zero .surfHowMany))) .zero >
      (L1 hα uniformLatentPrior .everyNot
        (L1_marginal_everyNot_ne_zero hα (uniformLatentPrior_ne_zero .surfHowMany))) .one := by
  sorry

/-- Baseline L1 ordering: `L1(one | everyNot) > L1(two | everyNot)`.
Inverse scope makes `.one` true; neither scope makes `.two` true. -/
theorem baseline_L1_one_gt_two {α : ℝ} (hα : 0 < α) :
    (L1 hα uniformLatentPrior .everyNot
        (L1_marginal_everyNot_ne_zero hα (uniformLatentPrior_ne_zero .surfHowMany))) .one >
      (L1 hα uniformLatentPrior .everyNot
        (L1_marginal_everyNot_ne_zero hα (uniformLatentPrior_ne_zero .surfHowMany))) .two := by
  sorry

end Findings

end ScontrasPearl2021.EveryNot.PMF
