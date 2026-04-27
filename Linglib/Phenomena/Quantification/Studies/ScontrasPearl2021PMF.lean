import Linglib.Theories.Pragmatics.RSA.Operators
import Linglib.Phenomena.Quantification.Studies.ScontrasPearl2021
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Binomial

/-!
# @cite{scontras-pearl-2021} on mathlib `PMF` — chained-RSA + S2 substrate

@cite{scontras-pearl-2021} ("When pragmatics matters more for truth-value
judgments: An investigation of quantifier scope ambiguity",
*Glossa* 6(1):110, 2021) presents a parameterized RSA model for
quantifier scope ambiguity. This file formalises the structural skeleton.

## Scope (honest reckoning, post-audit 0.230.x)

The §1-§7 sections build L0/S1/L1 against a **uniform** `worldPrior` and
**uniform** `latentPrior` — a simplification not matching the paper. §8
("Phase 1 substrate") adds the paper-faithful **parameterized** versions
(binomial worldPrior, favored-QUD latentPrior) and the **S2 layer** (which
§1-§7 omits despite the paper p.15 stating S2 is the layer that maps to
truth-value judgments).

Three documented fidelity gaps between §1-§7 and the paper:

1. **`worldPrior` (§1) is uniform; paper p.15-16 uses binomial(2, b_suc).**
   At b_suc=0.5 (paper default): binomial gives (1/4, 1/2, 1/4), NOT uniform
   (1/3, 1/3, 1/3). The paper-faithful version is `worldPriorAt b_suc` (§8.1).
2. **`L1` (§6) returns `PMF JumpOutcome`** — the world marginal of the paper's
   joint L1. Paper p.14: `P_{L_1}(w, i, q | u)` is over `(w, i, q)` jointly.
   Operationally fine because S2 only consumes the world marginal; named
   accordingly: `L1` = world marginal, paper's notation = joint L1.
3. **S2 layer absent in §1-§7.** Paper p.15: S2 is the truth-value-judgment
   layer (production speaker mapping observed world to utterance). §8.6
   adds `S2 := PMF.normalize over u of L1At u w`, the paper's
   `P_{S_2}(u | w) ∝ exp(log Σ_{i,q} P_{L_1}(w, i, q | u))` simplified
   to `∝ L1_marginal(w | u)` (since exp ∘ log = id and the sum is the marginal).

The §7 baseline findings (`baseline_L1_zero_gt_one`, `baseline_L1_one_gt_two`)
are at the SIMPLIFIED uniform world prior, not the paper's binomial. They
remain valid as structural-decomposition demonstrations but are not
paper-faithful claims.

## Architecture (mathlib-faithful)

* L0 is uniform on the extension of a Boolean meaning (`RSA.L0OfBoolMeaning`)
* S1 is `(QUD-projected L0 sum)^α` (rpow, not softmax-of-log)
* L1 is `PMF.posterior` of `marginalSpeaker = latentPrior.bind S1g`
* S2 is `PMF.normalize` over u of `L1At u w` for each fixed w
* All construction goes through `PMF.normalizeOfFintype` (Core helper)
* Real-valued parameters with explicit `0 < · < 1` hypotheses,
  cf. mathlib's `PMF.binomial` `unitInterval` pattern

## Cross-framework positioning

This file's RSA chain is the L&G-derived Bayesian inversion architecture
(cf. `LassiterGoodman2017PMF.lean`). The paper §3.1 explicitly adopts
@cite{goodman-frank-2016}'s framework. Sibling models on quantifier-negation
scope ambiguity exist in linglib's `Phenomena/Quantification/Studies/` but
none have been audit-cleaned to PMF; this file's parameterized substrate
(§8) is the first.

## Path to deep results (per audit 0.230.x)

The paper's "deep results" are:
- **D1 (headline)**: pragmatic dominance — at b_suc≈0.9, P(all?)≈0.9, the
  scope prior P(inverse) becomes nearly irrelevant for S2(amb)
- **D2**: cross-prior effect-size (Lipschitz)
- **D3**: world-state monotonicity (b_suc ↑ ⟹ S2(amb) ↑)
- **D4**: QUD ordering (S2 under all? > how-many? > none?)
- **D7** (per semantics audit): "either-scope-serves-listener" structural lemma

D1-D4 are stated as future theorem signatures; D7 is the recommended
first-stage win (structural, no real arithmetic). Mathlib infrastructure
audit (verified): no `Continuous`/`Tendsto`/`Lipschitz` lemmas on PMF in
mathlib; the canonical pattern for parameterized PMF families is
**pointwise `Tendsto` at a fixed application point** (cf.
`Mathlib.Probability.Distributions.Poisson.PoissonLimitThm`'s
`binomial_tendsto_poissonPMFReal_atTop`). D1 should follow this pattern.

## Coverage discharge (§1-§7 reference)

The `null` utterance has full extension (true at every world), so its L0 is
uniform on `Finset.univ` and `qudProjectE q (L0 s null) w > 0` for every
`(s, q, w)`. This single witness drives every `PMF.normalize` precondition
in §1-§7 (S1g positivity at every `(lat, w)`, marginal positivity at every
`(w, u)` for `u = .null`, and L1 marginal positivity).

## Reused from `ScontrasPearl2021.lean`

* `JumpOutcome`, `ScopeReading`, `EveryNot.Utt`, `EveryNot.QUD`,
  `EveryNot.Latent`, `EveryNot.uttMeaning`, `EveryNot.Latent.scope`/`.qud`
-/

set_option autoImplicit false

namespace ScontrasPearl2021.EveryNot.PMF

open scoped ENNReal NNReal
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

/-! ### Structural-shell decomposition

The two baseline findings below admit a clean structural decomposition via
the inequality lemma library (0.230.387-389):

  `posterior_lt_iff_score_lt` cancels the L1 marginal denominator, reducing
  to a `worldPrior · marginalSpeaker` score comparison. `worldPrior` is
  uniform, so it cancels via `mul_lt_mul_iff_right`. The remainder is a
  pure `marginalSpeaker` comparison — itself a `PMF.bind` over the latent
  prior, decomposable per-latent via `marginal_lt_marginal`.

The per-latent comparison is the natural "leaf" obligation: a finite
case-bash over `Latent` that compares S1g speaker outputs at the two
worlds being contrasted. It bottoms out in `ENNReal.rpow_lt_rpow` (rpow
is strictly increasing in its base) — *structural* but specific to the
S1g internals. Bundled here as a single sorry'd helper per finding. -/

/-! ### Per-latent leaf computations

The structural shell reduces the headline to per-latent S1g comparisons.
For each latent, both sides are `(qudProjectE q (L0 s .everyNot) w)^α / Z(lat, w)`
with `Z` and the projection depending only on `lat` and `w`. The pointwise
comparison breaks into 6 cases over `Latent`, each computable from the
truth table of `uttMeaning` plus rpow monotonicity.

The strict-witness case (`.surfHowMany`) is fully discharged: at world
`.one`, surface scope makes `.everyNot` false, the L0 numerator is zero,
and the speaker score collapses. The full pointwise ≤ is sorry'd because
4 of the remaining 5 cases collapse to equality (4 require computing that
both sides have identical numerators and partition functions) and the 6th
(`.invNone`) requires `(1/3)^α < (2/3)^α` via `ENNReal.rpow_lt_rpow_of_exponent_pos`. -/

/-- The strict-witness case: at `.surfHowMany`, surface scope makes
`.everyNot` false at world `.one`, so the speaker score is zero.

Refactored 0.230.397 to use `PMF.normalize_lt_of_apply_zero_pos` (the
canonical vacuous-zero cross-base lemma) — score-zero proof + score-nonzero
proof are the only model-specific ingredients. -/
theorem S1g_surfHowMany_strict {α : ℝ} (hα : 0 < α) :
    S1g hα .surfHowMany .one .everyNot < S1g hα .surfHowMany .zero .everyNot := by
  apply PMF.normalize_lt_of_apply_zero_pos
  · -- LHS score = 0: qudProjectE .howMany at .one = L0 .surface .everyNot .one = 0
    show (qudProjectE .howMany (fun w' => L0 .surface .everyNot w') .one) ^ α = 0
    rw [show qudProjectE .howMany (fun w' => L0 .surface .everyNot w') .one
            = L0 .surface .everyNot .one from rfl,
        L0_apply_of_false (by decide)]
    exact ENNReal.zero_rpow_of_pos hα
  · -- RHS score ≠ 0: qudProjectE .howMany at .zero = L0 .surface .everyNot .zero = 1
    show (qudProjectE .howMany (fun w' => L0 .surface .everyNot w') .zero) ^ α ≠ 0
    rw [show qudProjectE .howMany (fun w' => L0 .surface .everyNot w') .zero
            = L0 .surface .everyNot .zero from rfl,
        L0_apply_of_true (by decide : uttMeaning .surface .everyNot .zero = true),
        show extension .surface .everyNot = {JumpOutcome.zero} from rfl]
    simp

/-- Companion vacuous-zero strict case at `.surfNone`: same shape as
`.surfHowMany`. Surface scope makes `.everyNot` false at `.one`, and the
QUD .none_ doesn't help — its projection at `.one` is `L0 .one + L0 .two = 0`. -/
theorem S1g_surfNone_strict {α : ℝ} (hα : 0 < α) :
    S1g hα .surfNone .one .everyNot < S1g hα .surfNone .zero .everyNot := by
  apply PMF.normalize_lt_of_apply_zero_pos
  · -- LHS score = 0: qudProjectE .none_ at .one = L0 .one + L0 .two = 0 + 0 = 0
    show (qudProjectE .none_ (fun w' => L0 .surface .everyNot w') .one) ^ α = 0
    rw [show qudProjectE .none_ (fun w' => L0 .surface .everyNot w') .one
            = L0 .surface .everyNot .one + L0 .surface .everyNot .two from rfl,
        L0_apply_of_false (by decide : uttMeaning .surface .everyNot .one ≠ true),
        L0_apply_of_false (by decide : uttMeaning .surface .everyNot .two ≠ true), add_zero]
    exact ENNReal.zero_rpow_of_pos hα
  · -- RHS score ≠ 0: at .zero, qudProjectE .none_ = L0 .zero ≠ 0
    show (qudProjectE .none_ (fun w' => L0 .surface .everyNot w') .zero) ^ α ≠ 0
    rw [show qudProjectE .none_ (fun w' => L0 .surface .everyNot w') .zero
            = L0 .surface .everyNot .zero from rfl,
        L0_apply_of_true (by decide : uttMeaning .surface .everyNot .zero = true),
        show extension .surface .everyNot = {JumpOutcome.zero} from rfl]
    simp

/-- Per-latent comparison: at every latent, the S1g speaker assigns no more
mass to `.everyNot` at world `.one` than at world `.zero`, with strict
preference at `.surfHowMany`.

Per-latent breakdown:
- `.surfHowMany`, `.surfNone` (vacuous-zero): LHS = 0, ≤ via `le_of_lt` from
  the strict witnesses `S1g_surfHowMany_strict` / `S1g_surfNone_strict`.
- `.surfAll`, `.invHowMany`, `.invAll` (equality): both sides have the same
  numerator AND same partition function (verified by symmetric structure).
- `.invNone` (strict via rpow monotonicity): `(1/3)^α < (2/3)^α` makes the
  partition function smaller at `.zero`, so the quotient is larger.

The 4 remaining cases are mechanical computation but require ENNReal
arithmetic infrastructure (or a `pmf_score_compare` tactic). -/
theorem S1g_zero_gt_one_for_some_latent {α : ℝ} (hα : 0 < α) :
    (∀ lat, S1g hα lat .one .everyNot ≤ S1g hα lat .zero .everyNot) ∧
    S1g hα .surfHowMany .one .everyNot < S1g hα .surfHowMany .zero .everyNot := by
  refine ⟨?_, S1g_surfHowMany_strict hα⟩
  -- Helper: equality cases reduce to "score functions are equal pointwise"
  have h_eq_via : ∀ (lat : Latent),
      (∀ u, s1Score α lat .one u = s1Score α lat .zero u) →
      S1g hα lat .one .everyNot ≤ S1g hα lat .zero .everyNot := fun lat hScore =>
    le_of_eq <| PMF.normalize_eq_of_apply_eq_and_sum_eq _ _ _ _ _ _ _
      (hScore .everyNot) (tsum_congr hScore)
  intro lat
  cases lat
  · exact (S1g_surfHowMany_strict hα).le  -- surfHowMany: vacuous-zero LHS
  · -- surfAll: scores equal at .one and .zero (qudProjectE .all_ groups {.zero, .one})
    refine h_eq_via .surfAll fun u => ?_
    show (qudProjectE .all_ (fun w' => L0 .surface u w') .one) ^ α =
         (qudProjectE .all_ (fun w' => L0 .surface u w') .zero) ^ α
    rfl
  · exact (S1g_surfNone_strict hα).le  -- surfNone: vacuous-zero LHS
  · -- invHowMany: scores equal at .one and .zero because L0 .inverse u is symmetric
    -- between .zero and .one for all u (uttMeaning .inverse u .zero = uttMeaning .inverse u .one)
    refine h_eq_via .invHowMany fun u => ?_
    show (qudProjectE .howMany (fun w' => L0 .inverse u w') .one) ^ α =
         (qudProjectE .howMany (fun w' => L0 .inverse u w') .zero) ^ α
    -- qudProjectE .howMany is identity, so need L0 .inverse u .one = L0 .inverse u .zero
    have hL0_eq : L0 .inverse u .one = L0 .inverse u .zero := by
      cases u
      · -- u = .null: both true (L0 = 1/3)
        rw [L0_apply_of_true (by decide), L0_apply_of_true (by decide)]
      · -- u = .everyNot: both true under .inverse (L0 = 1/2)
        rw [L0_apply_of_true (by decide), L0_apply_of_true (by decide)]
    show L0 .inverse u .one ^ α = L0 .inverse u .zero ^ α
    rw [hL0_eq]
  · -- invAll: scores equal at .one and .zero (same QUD groups {.zero, .one})
    refine h_eq_via .invAll fun u => ?_
    show (qudProjectE .all_ (fun w' => L0 .inverse u w') .one) ^ α =
         (qudProjectE .all_ (fun w' => L0 .inverse u w') .zero) ^ α
    rfl
  · -- invNone: numerators equal at .everyNot, partition larger at .one
    apply PMF.normalize_le_of_apply_eq_and_sum_ge
    · -- Numerator equality at .everyNot:
      -- qudProjectE .none_ (L0 .inverse .everyNot) .one = L0 .one + L0 .two = L0 .one + 0 = L0 .one
      -- qudProjectE .none_ (L0 .inverse .everyNot) .zero = L0 .zero
      -- L0 .inverse .everyNot .zero = L0 .inverse .everyNot .one (both =((extension).card)⁻¹)
      have h_two : L0 .inverse .everyNot .two = 0 := L0_apply_of_false (by decide)
      have h_eq_zero_one : L0 .inverse .everyNot .zero = L0 .inverse .everyNot .one := by
        rw [L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .zero = true),
            L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .one = true)]
      show (L0 .inverse .everyNot .one + L0 .inverse .everyNot .two) ^ α =
           L0 .inverse .everyNot .zero ^ α
      rw [h_two, add_zero, h_eq_zero_one]
    · -- Partition sum monotonicity: per-u, qudProj at .zero ≤ qudProj at .one
      apply ENNReal.tsum_le_tsum
      intro u
      cases u
      · -- u = .null: qudProj at .zero = L0 .zero; at .one = L0 .one + L0 .two
        -- L0 .inverse .null = uniform (all true), so L0 .zero = L0 .one = L0 .two = 1/3
        -- So L0 .zero ≤ L0 .one + L0 .two via le_add_right + h_eq
        show L0 .inverse .null .zero ^ α ≤
             (L0 .inverse .null .one + L0 .inverse .null .two) ^ α
        have h_zero_le_one : L0 .inverse .null .zero ≤ L0 .inverse .null .one := by
          rw [L0_apply_of_true (by decide : uttMeaning .inverse .null .zero = true),
              L0_apply_of_true (by decide : uttMeaning .inverse .null .one = true)]
        apply ENNReal.rpow_le_rpow _ hα.le
        exact h_zero_le_one.trans le_self_add
      · -- u = .everyNot: qudProj at .zero = L0 .zero; at .one = L0 .one + L0 .two = L0 .one + 0 = L0 .one = L0 .zero
        show L0 .inverse .everyNot .zero ^ α ≤
             (L0 .inverse .everyNot .one + L0 .inverse .everyNot .two) ^ α
        have h_two : L0 .inverse .everyNot .two = 0 := L0_apply_of_false (by decide)
        have h_eq : L0 .inverse .everyNot .zero = L0 .inverse .everyNot .one := by
          rw [L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .zero = true),
              L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .one = true)]
        rw [h_two, add_zero, h_eq]

/-- Baseline L1 ordering at the partial world: `L1(zero | everyNot) > L1(one | everyNot)`.
Both scopes agree `.zero` is true; only inverse scope makes `.one` true.

**Structural discharge** (2 lemma applications, post-API extension):
1. `posterior_lt_iff_kernel_lt_of_uniform`: cancels L1 marginal AND uniform world prior.
2. `PMF.bind_lt_bind`: reduces marginalSpeaker = bind to per-latent comparison.

The pre-API-extension version of this proof took 4 explicit rewrite steps;
the new lemmas (added 0.230.391) collapse it to 2 single-line tactics. -/
theorem baseline_L1_zero_gt_one {α : ℝ} (hα : 0 < α) :
    (L1 hα uniformLatentPrior .everyNot
        (L1_marginal_everyNot_ne_zero hα (uniformLatentPrior_ne_zero .surfHowMany))) .zero >
      (L1 hα uniformLatentPrior .everyNot
        (L1_marginal_everyNot_ne_zero hα (uniformLatentPrior_ne_zero .surfHowMany))) .one := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  obtain ⟨h_le, h_strict⟩ := S1g_zero_gt_one_for_some_latent hα
  exact PMF.bind_lt_bind uniformLatentPrior _ _ Utt.everyNot
    (uniformLatentPrior_ne_zero .surfHowMany) h_le h_strict

/-- Strict-witness case for the .one-vs-.two ordering: at `.invHowMany`,
inverse scope makes `.everyNot` false at `.two` (only `.zero` and `.one`
are in extension), so the speaker score at `.two` is zero. -/
theorem S1g_invHowMany_strict_one_two {α : ℝ} (hα : 0 < α) :
    S1g hα .invHowMany .two .everyNot < S1g hα .invHowMany .one .everyNot := by
  apply PMF.normalize_lt_of_apply_zero_pos
  · -- LHS score = 0: L0 .inverse .everyNot .two = 0 (.two ∉ extension {.zero, .one})
    show (qudProjectE .howMany (fun w' => L0 .inverse .everyNot w') .two) ^ α = 0
    rw [show qudProjectE .howMany (fun w' => L0 .inverse .everyNot w') .two
            = L0 .inverse .everyNot .two from rfl,
        L0_apply_of_false (by decide)]
    exact ENNReal.zero_rpow_of_pos hα
  · -- RHS score ≠ 0: L0 .inverse .everyNot .one ≠ 0 (.one ∈ extension)
    show (qudProjectE .howMany (fun w' => L0 .inverse .everyNot w') .one) ^ α ≠ 0
    rw [show qudProjectE .howMany (fun w' => L0 .inverse .everyNot w') .one
            = L0 .inverse .everyNot .one from rfl,
        L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .one = true)]
    -- L0 = ((extension .inverse .everyNot).card)⁻¹ ≠ 0
    rw [show extension .inverse .everyNot = {JumpOutcome.zero, JumpOutcome.one} from rfl]
    simp

/-- Per-latent comparison: at every latent, the S1g speaker assigns no more
mass to `.everyNot` at world `.two` than at world `.one`. Strict witness at
`.invHowMany`.

5 of 6 cases are vacuous-zero (LHS = 0 because `.two ∉ extension` for both
scopes — surface scope: extension = {.zero}; inverse scope: extension = {.zero, .one}).
The remaining case (.invNone) is an equality. -/
theorem S1g_one_gt_two_for_some_latent {α : ℝ} (hα : 0 < α) :
    (∀ lat, S1g hα lat .two .everyNot ≤ S1g hα lat .one .everyNot) ∧
    S1g hα .invHowMany .two .everyNot < S1g hα .invHowMany .one .everyNot := by
  refine ⟨?_, S1g_invHowMany_strict_one_two hα⟩
  -- Helper for vacuous-zero cases: if score at .two is 0, S1g is 0 ≤ X
  have h_zero_le : ∀ (lat : Latent),
      s1Score α lat .two .everyNot = 0 →
      S1g hα lat .two .everyNot ≤ S1g hα lat .one .everyNot := by
    intro lat hScore
    have : S1g hα lat .two .everyNot = 0 := by
      rw [S1g, PMF.normalize_apply, hScore, zero_mul]
    rw [this]; exact zero_le _
  -- Helper for equality cases (parallel to S1g_zero_gt_one)
  have h_eq_via : ∀ (lat : Latent),
      (∀ u, s1Score α lat .two u = s1Score α lat .one u) →
      S1g hα lat .two .everyNot ≤ S1g hα lat .one .everyNot := fun lat hScore =>
    le_of_eq <| PMF.normalize_eq_of_apply_eq_and_sum_eq _ _ _ _ _ _ _
      (hScore .everyNot) (tsum_congr hScore)
  intro lat
  cases lat
  · -- surfHowMany: vacuous-zero (L0 .surface .everyNot .two = 0)
    refine h_zero_le .surfHowMany ?_
    show (qudProjectE .howMany (fun w' => L0 .surface .everyNot w') .two) ^ α = 0
    rw [show qudProjectE .howMany (fun w' => L0 .surface .everyNot w') .two
            = L0 .surface .everyNot .two from rfl,
        L0_apply_of_false (by decide)]
    exact ENNReal.zero_rpow_of_pos hα
  · -- surfAll: vacuous-zero (qudProjectE .all_ at .two = L0 .two = 0 for surface .everyNot)
    refine h_zero_le .surfAll ?_
    show (qudProjectE .all_ (fun w' => L0 .surface .everyNot w') .two) ^ α = 0
    rw [show qudProjectE .all_ (fun w' => L0 .surface .everyNot w') .two
            = L0 .surface .everyNot .two from rfl,
        L0_apply_of_false (by decide)]
    exact ENNReal.zero_rpow_of_pos hα
  · -- surfNone: vacuous-zero (qudProjectE .none_ at .two = L0 .one + L0 .two = 0 + 0)
    refine h_zero_le .surfNone ?_
    show (qudProjectE .none_ (fun w' => L0 .surface .everyNot w') .two) ^ α = 0
    rw [show qudProjectE .none_ (fun w' => L0 .surface .everyNot w') .two
            = L0 .surface .everyNot .one + L0 .surface .everyNot .two from rfl,
        L0_apply_of_false (by decide), L0_apply_of_false (by decide), add_zero]
    exact ENNReal.zero_rpow_of_pos hα
  · exact (S1g_invHowMany_strict_one_two hα).le  -- invHowMany: strict, take .le
  · -- invAll: vacuous-zero (qudProjectE .all_ at .two = L0 .two = 0 for inverse .everyNot)
    refine h_zero_le .invAll ?_
    show (qudProjectE .all_ (fun w' => L0 .inverse .everyNot w') .two) ^ α = 0
    rw [show qudProjectE .all_ (fun w' => L0 .inverse .everyNot w') .two
            = L0 .inverse .everyNot .two from rfl,
        L0_apply_of_false (by decide)]
    exact ENNReal.zero_rpow_of_pos hα
  · -- invNone: equality (qudProjectE .none_ at .two = L0 .one + L0 .two = qudProjectE .none_ at .one)
    refine h_eq_via .invNone fun u => ?_
    show (qudProjectE .none_ (fun w' => L0 .inverse u w') .two) ^ α =
         (qudProjectE .none_ (fun w' => L0 .inverse u w') .one) ^ α
    rfl

/-- Baseline L1 ordering: `L1(one | everyNot) > L1(two | everyNot)`.
Inverse scope makes `.one` true; neither scope makes `.two` true.

Same 2-lemma discharge as `baseline_L1_zero_gt_one`. -/
theorem baseline_L1_one_gt_two {α : ℝ} (hα : 0 < α) :
    (L1 hα uniformLatentPrior .everyNot
        (L1_marginal_everyNot_ne_zero hα (uniformLatentPrior_ne_zero .surfHowMany))) .one >
      (L1 hα uniformLatentPrior .everyNot
        (L1_marginal_everyNot_ne_zero hα (uniformLatentPrior_ne_zero .surfHowMany))) .two := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  obtain ⟨h_le, h_strict⟩ := S1g_one_gt_two_for_some_latent hα
  exact PMF.bind_lt_bind uniformLatentPrior _ _ Utt.everyNot
    (uniformLatentPrior_ne_zero .invHowMany) h_le h_strict

end Findings

/-! ## §8. Phase 1 substrate — paper-faithful parameterization (2026-04-26)

The §1-§7 above use a *uniform* `worldPrior` and *uniform* `latentPrior` —
a simplification not matching the paper. This section adds the paper-faithful
**parameterized** versions and the **S2 layer** (which §1-§7 omits entirely
despite the paper p.15 stating S2 is the layer that maps to truth-value
judgments).

Paper-faithful parameters (paper p.15-16):
- `b_suc ∈ (0, 1)` — per-horse success rate; `worldPrior = binomial(2, b_suc)`
- `p_all ∈ (0, 1)` — favored-QUD weight; uniform over the other two
- `p_inv ∈ (0, 1)` — favored-scope weight (inverse); 1 - p_inv on surface
- Default: `b_suc = 0.5`, `p_all = 1/3`, `p_inv = 0.5`

At `b_suc = 0.5`: binomial(2, 0.5) = (1/4, 1/2, 1/4) — NOT uniform (1/3, 1/3, 1/3).
The §1 `worldPrior := PMF.uniformOfFintype` is a paper-fidelity bug; §1-§7's
findings are thus at the SIMPLIFIED uniform world prior, not the paper's.

This section follows mathlib's pattern for parameterized PMF families: real-
valued parameters with explicit `0 < · < 1` hypotheses (cf. `PMF.binomial`'s
`unitInterval`-typed parameter). All construction goes through
`PMF.normalizeOfFintype` (the recently-added Core helper). -/

/-! ### §8.1 World prior — binomial in `b_suc` (via mathlib `PMF.binomial`)

**Refactored 0.230.439** to use mathlib's `PMF.binomial` (per "check mathlib first"
discipline; see `project_pmf_check_mathlib_first.md`). The previous version
hand-rolled a 3-case `worldPriorENN` + `normalizeOfFintype` construction,
duplicating mathlib's `Mathlib.Probability.ProbabilityMassFunction.Binomial`. -/

/-- Identification of `JumpOutcome` with `Fin 3` (number of horses succeeding,
out of 2). Required to lift `PMF.binomial _ _ 2 : PMF (Fin 3)` to `PMF JumpOutcome`. -/
def JumpOutcome.equivFin3 : JumpOutcome ≃ Fin 3 where
  toFun
    | .zero => 0
    | .one => 1
    | .two => 2
  invFun
    | ⟨0, _⟩ => .zero
    | ⟨1, _⟩ => .one
    | ⟨2, _⟩ => .two
  left_inv := fun w => by cases w <;> rfl
  right_inv := fun ⟨n, h⟩ => by interval_cases n <;> rfl

/-- Binomial world prior, parameterized on per-horse success rate `b_suc : ℝ≥0`.
Paper-faithful (vs the §1 uniform simplification). Wraps mathlib's `PMF.binomial`
with the `JumpOutcome ≃ Fin 3` identification.

Allows `b_suc = 0` and `b_suc = 1` (degenerate Diracs at `.zero` / `.two`
respectively); paper's range is `[0.1, 0.9]` but no positivity-strict bound
needed for the construction itself. -/
noncomputable def worldPriorAt (b_suc : ℝ≥0) (h_le_one : b_suc ≤ 1) :
    PMF JumpOutcome :=
  (PMF.binomial b_suc h_le_one 2).map JumpOutcome.equivFin3.symm

/-! ### §8.2 QUD prior — favored-QUD weight `p_all` -/

/-- Unnormalized QUD weights with `p_all` favoring the `all?` QUD. -/
noncomputable def qudPriorENN (p_all : ℝ) : QUD → ℝ≥0∞
  | .all_ => ENNReal.ofReal p_all
  | .howMany => ENNReal.ofReal ((1 - p_all) / 2)
  | .none_ => ENNReal.ofReal ((1 - p_all) / 2)

theorem qudPriorENN_finite (p_all : ℝ) (q : QUD) : qudPriorENN p_all q ≠ ⊤ := by
  cases q <;> exact ENNReal.ofReal_ne_top

theorem qudPriorENN_all_pos {p_all : ℝ} (h_lo : 0 < p_all) :
    qudPriorENN p_all .all_ ≠ 0 := by
  show ENNReal.ofReal p_all ≠ 0
  rw [ENNReal.ofReal_ne_zero_iff]; exact h_lo

/-- QUD prior, parameterized on favored-QUD weight `p_all`.
Only `0 < p_all` is needed for positivity; `p_all ≤ 1` doesn't appear in the
proof (the unfavored components use `(1 - p_all)/2` but their positivity
isn't required for this construction — only the witness `.all_` is). -/
noncomputable def qudPriorAt (p_all : ℝ) (h_lo : 0 < p_all) :
    PMF QUD :=
  PMF.normalizeOfFintype (qudPriorENN p_all) .all_
    (qudPriorENN_all_pos h_lo)
    (qudPriorENN_finite p_all)

/-! ### §8.3 Scope prior — `p_inv` favors inverse, `1 - p_inv` favors surface -/

/-- Unnormalized scope weights. -/
noncomputable def scopePriorENN (p_inv : ℝ) : ScopeReading → ℝ≥0∞
  | .inverse => ENNReal.ofReal p_inv
  | .surface => ENNReal.ofReal (1 - p_inv)

theorem scopePriorENN_finite (p_inv : ℝ) (s : ScopeReading) :
    scopePriorENN p_inv s ≠ ⊤ := by
  cases s <;> exact ENNReal.ofReal_ne_top

theorem scopePriorENN_inverse_pos {p_inv : ℝ} (h_lo : 0 < p_inv) :
    scopePriorENN p_inv .inverse ≠ 0 := by
  show ENNReal.ofReal p_inv ≠ 0
  rw [ENNReal.ofReal_ne_zero_iff]; exact h_lo

/-- Scope prior, parameterized on inverse-scope weight `p_inv`.
Only `0 < p_inv` is needed for positivity (witness `.inverse`); `p_inv ≤ 1`
unused in this construction. -/
noncomputable def scopePriorAt (p_inv : ℝ) (h_lo : 0 < p_inv) :
    PMF ScopeReading :=
  PMF.normalizeOfFintype (scopePriorENN p_inv) .inverse
    (scopePriorENN_inverse_pos h_lo)
    (scopePriorENN_finite p_inv)

/-! ### §8.4 Latent prior — independent product `scopePrior × qudPrior` -/

/-- Unnormalized latent weight as the per-component product. -/
noncomputable def latentPriorENN (p_inv p_all : ℝ) : Latent → ℝ≥0∞
  | .surfHowMany => scopePriorENN p_inv .surface * qudPriorENN p_all .howMany
  | .surfAll => scopePriorENN p_inv .surface * qudPriorENN p_all .all_
  | .surfNone => scopePriorENN p_inv .surface * qudPriorENN p_all .none_
  | .invHowMany => scopePriorENN p_inv .inverse * qudPriorENN p_all .howMany
  | .invAll => scopePriorENN p_inv .inverse * qudPriorENN p_all .all_
  | .invNone => scopePriorENN p_inv .inverse * qudPriorENN p_all .none_

theorem latentPriorENN_finite (p_inv p_all : ℝ) (lat : Latent) :
    latentPriorENN p_inv p_all lat ≠ ⊤ := by
  cases lat <;> exact ENNReal.mul_ne_top
    (scopePriorENN_finite _ _) (qudPriorENN_finite _ _)

theorem latentPriorENN_invAll_pos {p_inv p_all : ℝ}
    (h_inv : 0 < p_inv) (h_all : 0 < p_all) :
    latentPriorENN p_inv p_all .invAll ≠ 0 :=
  mul_ne_zero (scopePriorENN_inverse_pos h_inv) (qudPriorENN_all_pos h_all)

/-- Latent prior, parameterized on `(p_inv, p_all)` as the independent product
of `scopePriorAt p_inv × qudPriorAt p_all`. Only the per-component lower
bounds (`h_inv_lo`, `h_all_lo`) are needed (witness `.invAll`); upper bounds
unused. -/
noncomputable def latentPriorAt (p_inv p_all : ℝ)
    (h_inv_lo : 0 < p_inv) (h_all_lo : 0 < p_all) : PMF Latent :=
  PMF.normalizeOfFintype (latentPriorENN p_inv p_all) .invAll
    (latentPriorENN_invAll_pos h_inv_lo h_all_lo)
    (latentPriorENN_finite p_inv p_all)

/-! ### §8.5 L1 — paper-faithful Bayesian inversion (parameterized prior)

This is the paper's L1 (marginalized over `(i, q)`) under the parameterized
priors. The §6 `L1` uses the §1 uniform `worldPrior`; this version uses
`worldPriorAt b_suc` and `latentPriorAt p_inv p_all`.

Note on naming: the paper's joint L1 is `PMF (Latent × JumpOutcome)`; this
file's L1 is the world marginal `PMF JumpOutcome` — the variable that S2
consumes. -/

/-- Paper-faithful pragmatic listener (world marginal of joint L1). -/
noncomputable def L1At {α : ℝ} (hα : 0 < α)
    (worldPrior : PMF JumpOutcome) (latentPrior : PMF Latent) (u : Utt)
    (hMarg : PMF.marginal (marginalSpeaker hα latentPrior) worldPrior u ≠ 0) :
    PMF JumpOutcome :=
  PMF.posterior (marginalSpeaker hα latentPrior) worldPrior u hMarg

/-! ### §8.6 S2 — production speaker for truth-value judgment (paper p.15)

`P_S2(u | w) ∝ exp(log Σ_{i,q} P_L1(w, i, q | u))`. Since `Σ_{i,q} P_L1 = L1_marginal`
(the file's `L1At`), this is `S2(u | w) ∝ L1At u w` — re-normalize the L1 values
across u for each fixed w.

Cover witness for the normalization: `.null` is universally applicable, so
`L1At _ .null _ w ≠ 0` for every `w` with positive `worldPrior` mass. We
encode this via the `dite` pattern: `S2Score = L1At u h w` if h holds, else 0.

Implementation note: this S2 is paper-specific (intersective truth-value-judgment
production), not a generic RSA layer — keep in study file rather than
promoting to `Theories/Pragmatics/RSA/`. -/

/-- The unnormalized S2 score at `(w, u)`: the L1 posterior at `w` given `u`,
or 0 if the L1 marginal at `u` is degenerate. -/
noncomputable def S2Score {α : ℝ} (hα : 0 < α)
    (worldPrior : PMF JumpOutcome) (latentPrior : PMF Latent)
    (w : JumpOutcome) (u : Utt) : ℝ≥0∞ :=
  if h : PMF.marginal (marginalSpeaker hα latentPrior) worldPrior u ≠ 0
  then L1At hα worldPrior latentPrior u h w
  else 0

theorem S2Score_finite {α : ℝ} (hα : 0 < α)
    (worldPrior : PMF JumpOutcome) (latentPrior : PMF Latent)
    (w : JumpOutcome) (u : Utt) :
    S2Score hα worldPrior latentPrior w u ≠ ⊤ := by
  unfold S2Score
  split <;> [exact PMF.apply_ne_top _ _; exact ENNReal.zero_ne_top]

/-! Production speaker S2: for each world `w`, `S2 w` is a `PMF Utt` distributed
proportional to `L1At u w` over `u`.

The cover witness for `S2`'s normalization comes from `u = .null` at any
world `w` with positive prior mass: `null` is universally true, so
`marginalSpeaker hα latentPrior w .null > 0` (via `S1g_null_ne_zero`),
giving `marginal κ μ .null > 0` and thus `L1At hα _ _ .null h w > 0`.

For brevity (and since we don't yet have the full positivity machinery for
`L1At` at general parameter values), `S2` is stated with explicit positivity
hypotheses rather than self-discharging. -/

/-- Production speaker for truth-value judgment (paper p.15).

The positivity hypothesis `h_score_pos` is per-world; in practice it is
discharged via the `.null`-utterance cover witness (always applies, so the
L1 marginal at `.null` is positive at every world with positive prior). -/
noncomputable def S2 {α : ℝ} (hα : 0 < α)
    (worldPrior : PMF JumpOutcome) (latentPrior : PMF Latent)
    (w : JumpOutcome)
    (h_score_pos : ∑' u, S2Score hα worldPrior latentPrior w u ≠ 0) :
    PMF Utt :=
  PMF.normalize (S2Score hα worldPrior latentPrior w) h_score_pos
    (ENNReal.tsum_ne_top_of_fintype (S2Score_finite hα worldPrior latentPrior w))

/-! ## §9. D7 — structural scope-collapse under QUD = all? (paper §3.2 last paragraph; restated §5.1)

The paper's central explanatory move (p. 17, 29-30): when QUD = `all?` is
favored, BOTH scope readings of "every horse didn't jump" answer the QUD
identically with "no, not all succeeded". This collapses the scope distinction
at the speaker layer — providing the structural mechanism behind D1 (pragmatic
dominance, where scope prior becomes nearly irrelevant).

Formalized at three layers:
- **D7-L0**: `qudProjectE .all_` is independent of scope reading, for every utterance and world.
- **D7-S1**: `S1g hα .surfAll = S1g hα .invAll` as PMFs — corollary at speaker layer.
- **D7-application**: scope prior `P(inverse)` doesn't affect S2 mass at `.everyNot` when
  QUD = `all?`. Stated as future theorem; proof would compose D7-S1 through `marginalSpeaker`.

By-construction provable; no real arithmetic, no parameter sensitivity. The
mechanism behind D1's headline pragmatic-dominance statement. -/

/-- `extension X .null = Finset.univ` for both scopes — `null` is true everywhere.
Promoted from `private` (audit feedback): structurally generic and likely
useful by other PMF consumers that need to construct cover witnesses for
universal-extension utterances. -/
theorem extension_null_eq_univ (s : ScopeReading) :
    extension s .null = Finset.univ := by
  ext w; simp [extension, RSA.mem_extensionOf]; cases s <;> cases w <;> rfl

/-- **D7-L0**: under QUD = all?, the projected L0 mass is the same for surface
and inverse scope readings of any utterance, at every world.

Two cases by utterance:
- `u = .null`: L0 distributions are pointwise equal (both uniform on Finset.univ
  since extension of null = univ for both scopes).
- `u = .everyNot`: L0 distributions DIFFER pointwise (surface puts all mass on
  `.zero`; inverse splits between `.zero` and `.one`). But QUD `.all_` partitions
  worlds as {.zero, .one} vs {.two}, summing surface's (1, 0) → 1 and inverse's
  (1/2, 1/2) → 1 in the first cell. Equal projected behavior despite different
  raw L0. -/
theorem qudProjectE_all_scope_invariant (u : Utt) (w : JumpOutcome) :
    qudProjectE .all_ (fun w' => L0 .surface u w') w =
      qudProjectE .all_ (fun w' => L0 .inverse u w') w := by
  cases u
  case null =>
    -- L0 .surface .null = L0 .inverse .null pointwise (both uniform on univ).
    have h_eq : ∀ w', L0 .surface .null w' = L0 .inverse .null w' := fun w' => by
      rw [L0_apply_of_true (by cases w' <;> rfl), L0_apply_of_true (by cases w' <;> rfl),
          extension_null_eq_univ .surface, extension_null_eq_univ .inverse]
    cases w <;> simp only [qudProjectE, h_eq]
  case everyNot =>
    -- Surface: L0 .zero = 1, L0 .one = L0 .two = 0 (extension = {.zero}, card 1).
    -- Inverse: L0 .zero = L0 .one = 1/2, L0 .two = 0 (extension = {.zero, .one}, card 2).
    -- QUD .all_ at .zero/.one sums L0 .zero + L0 .one;
    -- QUD .all_ at .two = L0 .two.
    have h_surf_zero : L0 .surface .everyNot .zero = 1 := by
      rw [L0_apply_of_true (by decide : uttMeaning .surface .everyNot .zero = true),
          show extension .surface .everyNot = {JumpOutcome.zero} from rfl,
          Finset.card_singleton, Nat.cast_one, inv_one]
    have h_surf_one : L0 .surface .everyNot .one = 0 :=
      L0_apply_of_false (by decide : uttMeaning .surface .everyNot .one ≠ true)
    have h_surf_two : L0 .surface .everyNot .two = 0 :=
      L0_apply_of_false (by decide : uttMeaning .surface .everyNot .two ≠ true)
    have h_inv_zero : L0 .inverse .everyNot .zero = (2 : ℝ≥0∞)⁻¹ := by
      rw [L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .zero = true),
          show extension .inverse .everyNot = {JumpOutcome.zero, JumpOutcome.one} from rfl]
      rfl
    have h_inv_one : L0 .inverse .everyNot .one = (2 : ℝ≥0∞)⁻¹ := by
      rw [L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .one = true),
          show extension .inverse .everyNot = {JumpOutcome.zero, JumpOutcome.one} from rfl]
      rfl
    have h_inv_two : L0 .inverse .everyNot .two = 0 :=
      L0_apply_of_false (by decide : uttMeaning .inverse .everyNot .two ≠ true)
    have h_zero_one_eq :
        L0 .surface .everyNot .zero + L0 .surface .everyNot .one =
          L0 .inverse .everyNot .zero + L0 .inverse .everyNot .one := by
      rw [h_surf_zero, h_surf_one, h_inv_zero, h_inv_one, add_zero,
          ENNReal.inv_two_add_inv_two]
    cases w <;> simp only [qudProjectE]
    · exact h_zero_one_eq
    · exact h_zero_one_eq
    · rw [h_surf_two, h_inv_two]

/-- **D7-S1**: under QUD = `all?`, the speaker `S1g` is identical for surface
and inverse scope readings (at every world).

Direct corollary of D7-L0 lifted through `PMF.normalize`: the score functions
are pointwise equal (since `s1Score` only depends on `lat.qud` and `lat.scope`
through `qudProjectE` which collapses the scope distinction), so the
normalized PMFs are equal. -/
theorem S1g_all_qud_scope_invariant {α : ℝ} (hα : 0 < α) (w : JumpOutcome) :
    S1g hα .surfAll w = S1g hα .invAll w := by
  -- Both are PMF.normalize of s1Score; show s1Score is pointwise equal across u.
  have h_score_eq : ∀ u, s1Score α .surfAll w u = s1Score α .invAll w u := fun u => by
    show (qudProjectE .all_ (fun w' => L0 .surface u w') w) ^ α =
         (qudProjectE .all_ (fun w' => L0 .inverse u w') w) ^ α
    rw [qudProjectE_all_scope_invariant]
  ext u
  show PMF.normalize (s1Score α .surfAll w) _ _ u =
       PMF.normalize (s1Score α .invAll w) _ _ u
  exact PMF.normalize_eq_of_apply_eq_and_sum_eq _ _ _ _ _ _ _
    (h_score_eq u) (tsum_congr h_score_eq)

/-! ## §9'. D7-application — scope prior irrelevance under QUD = all?

The headline structural consequence of D7-S1: when the latent prior is split
between `.surfAll` and `.invAll`, the contribution of these two latents to
`marginalSpeaker` depends only on the SUM of their prior weights, not the
individual values. Direct corollary of D7-S1 (`S1g .surfAll = S1g .invAll`)
+ ENNReal distributivity (`add_mul`).

This is the structural mechanism behind D1's pragmatic-dominance claim:
shifting prior mass between `.invAll` and `.surfAll` doesn't change the
all?-QUD speaker behavior. -/

/-- **D7-application**: under QUD = `all?`, the `.surfAll` and `.invAll`
contributions to `marginalSpeaker` combine as a single sum-weighted term —
their individual prior weights don't matter, only the total.

Proof: D7-S1 (`S1g .surfAll = S1g .invAll`) + ENNReal `add_mul`. -/
theorem marginalSpeaker_surfAll_invAll_combine {α : ℝ} (hα : 0 < α)
    (latentPrior : PMF Latent) (w : JumpOutcome) (u : Utt) :
    latentPrior .surfAll * S1g hα .surfAll w u +
        latentPrior .invAll * S1g hα .invAll w u =
      (latentPrior .surfAll + latentPrior .invAll) * S1g hα .surfAll w u := by
  rw [← S1g_all_qud_scope_invariant hα w, ← add_mul]

/-! ## §10. D4 — discrete QUD ordering (paper Figure 2 center)

Paper p.16: "endorsement increase from the `none?` (0.38) to `how-many?` (0.48)
to `all?` (0.63) QUD" — at default `b_suc = 0.5`, uniform scope. The ordering
is over THREE different QUD priors (each favoring a different QUD), not over
QUD posteriors at one prior.

Formal statement: for parameters at the paper's defaults, with three QUD-prior
parameter values (`p_all = 0.05`, `p_all = 1/3`, `p_all = 0.9` representing
disfavored / uniform / favored), the S2 endorsement at world `.one` is
strictly ordered.

This requires concrete numeric arithmetic on the chained Bayesian update —
the same wall as L&G/Nouwen headlines. The structural shape decomposes via
`posterior_chained_lt_iff_score_lt` (Core); the residue is ENNReal arithmetic
on the closed-form expansion. Stated below as theorem signatures with sorry'd
numeric core; closing them is `rsa_predict_pmf` reflection territory or
manual ENNReal arithmetic. -/

/-! **D4 (deferred to numeric core)**: at fixed `b_suc = 0.5` and `p_inv = 0.5`,
the S2 endorsement at world `.one` should be HIGHER under QUD-prior favoring
`all?` (`p_all = 0.9`) than under uniform QUD prior (`p_all = 1/3`), per
paper Figure 2 center.

Structural decomposition would reduce posterior comparison to product-of-scores
via `PMF.posterior_lt_iff_score_lt`; partition functions differ (the QUD
prior changes weights), so the residue is numeric ENNReal arithmetic on the
model (binomial worldPrior + product latentPrior + S1g rpow + L1 posterior
+ S2 normalize). Same wall as LassiterGoodman2017PMF / Nouwen2024PMF headlines.

Not stated as a Lean theorem because the per-prior S2 marginal positivity
hypotheses make the signature unwieldy without a closure pattern. When
`rsa_predict_pmf` lands or a closure helper is built, the statement becomes:

```lean
example {α : ℝ} (hα : 0 < α)
    (h_marg_unif h_marg_fav : -- per-S2 marginal positivity hypotheses) :
    let wp := worldPriorAt 0.5 (by norm_num)
    let lp_unif := latentPriorAt 0.5 (1/3) (by norm_num) (by norm_num)
    let lp_fav := latentPriorAt 0.5 0.9 (by norm_num) (by norm_num)
    (S2 hα wp lp_unif .one h_marg_unif) .everyNot <
      (S2 hα wp lp_fav .one h_marg_fav) .everyNot := sorry
```
-/

/-! ## §11. D3 — REFRAMED (strategic plan correction)

The strategic planner proposed D3 as `worldPriorAt b_suc .one ≤ worldPriorAt b_suc' .one`
when `b_suc < b_suc'` (with the implication that S2(.amb|.one) is monotone
because worldPrior(.one) is monotone).

**This is incorrect.** `worldPrior b_suc .one = 2·b_suc·(1-b_suc)` is NOT
monotone in `b_suc` — it peaks at `b_suc = 0.5` (value 0.5) and is symmetric.
At `b_suc = 0.1` and `b_suc = 0.9`, both give worldPrior(.one) = 0.18.

The paper's claim (Figure 2 left, p.16) is that S2 ENDORSEMENT at world `.one`
is monotone in `b_suc` (0.29 at b_suc=0.1, 0.50 at b_suc=0.5, 0.80 at b_suc=0.9).
This is an EMERGENT property of the full chain (worldPrior → marginalSpeaker
→ L1 → S2), not a consequence of monotonicity in one factor.

Intuition for the emergent monotonicity: as `b_suc → 1`, the prior shifts
mass toward `.two`; `everyNot` at world `.one` becomes more INFORMATIVE
because it rules out the high-prior `.two`; informative utterances are
endorsed more by the rational speaker.

**D3 is therefore Phase 3 sensitivity territory**, not Phase 2 inequality-
library territory. Defer. The pointwise-Tendsto pattern from
`binomial_tendsto_poissonPMFReal_atTop` (mathlib infra audit) is the right
approach: compute the limit as `b_suc → 1` of `S2 b_suc (.amb)(.one)` and
show it exceeds the limit at `b_suc → 0`.

This reframing is the single most important strategic-plan correction from
this session.

The mathematical fact: `worldPriorAt b_suc _ .one =
((PMF.binomial b_suc h 2).map equiv.symm) .one`, which evaluates to
`2 · b_suc · (1 - b_suc)` (the binomial pmf at the middle index for n=2).
This expression peaks at `b_suc = 0.5` and is symmetric: equal at
`b_suc = 0.1` and `b_suc = 0.9`.

Encoding this as a Lean lemma requires NNReal-specific arithmetic plumbing
(literal coercions + truncated `1 - p`); the docstring captures the
mathematical content without the proof-term overhead. The strategic-plan
correction is recorded above; the §11 prose makes the refutation explicit. -/

end ScontrasPearl2021.EveryNot.PMF

/-! ## §12. D6 — exact-vs-at-least numeral semantics necessity (TwoNot, paper §4.2.2)

Per the semantics audit (post-D7 cleanup): the paper's strongest theoretical
contribution to numeral semantics literature lives at p.27 §4.2.2 + p.28 §4.3:

> "the current model requires one more ingredient to account for the 1-of-2
> vs 2-of-4 difference in adult behavior: an exact semantics for utterances
> with numerals (in contrast to an at-least semantics; for discussion, see
> e.g. Geurts 2006; Breheny 2008)."

Figure 7 (paper p.27) shows the contrast explicitly: under exact semantics
the surface scope of `twoNot` pinpoints `w=2` as the unique true world →
high S2 endorsement; under at-least semantics the surface scope is true at
multiple worlds {w0, w1, w2} → S2 dilutes across 3 worlds → low endorsement.

The paper's core empirical move: only with exact semantics can the model
reproduce adult endorsement-rate divergence between EveryNot (1-of-2) and
TwoNot (2-of-4).

**This section formalizes D6-L0**, the structural foundation: at w=2, the
surface-scope `twoNot` L0 mass is **strictly higher** under exact semantics
than under at-least semantics (because the extension is a singleton {w2}
vs a 3-element set {w0, w1, w2}). The S2 endorsement difference inherits
from this L0 mass difference.

Reuses bundled `ScontrasPearl2021.lean` data: `JumpOutcome4`, `NumeralReading`,
`TwoNot.Utt`, `TwoNot.uttMeaning`, `twoNotTruth`. Builds the L0 layer for
both numeral readings; D6 itself is a structural cross-semantics comparison. -/

namespace ScontrasPearl2021.TwoNot.PMF

open scoped ENNReal
open ScontrasPearl2021 ScontrasPearl2021.TwoNot

/-! ### §12.1 Extension of `twoNot` under each numeral reading -/

/-- Extension of `uttMeaning nr s u`: worlds where `u` is true under
numeral reading `nr` and scope `s`. -/
abbrev extension4 (nr : NumeralReading) (s : ScopeReading) (u : TwoNot.Utt) :
    Finset JumpOutcome4 :=
  RSA.extensionOf (TwoNot.uttMeaning nr s) u

/-- Under exact semantics, surface `twoNot` extension is the singleton `{w2}`
(only "exactly 2 didn't jump" is true when exactly 2 jumped). -/
theorem extension4_exact_surface_twoNot :
    extension4 .exact .surface .twoNot = {JumpOutcome4.w2} := rfl

/-- Under at-least semantics, surface `twoNot` extension is `{w0, w1, w2}`
(at least 2 didn't jump iff at most 2 jumped). -/
theorem extension4_atLeast_surface_twoNot :
    extension4 .atLeast .surface .twoNot =
      {JumpOutcome4.w0, JumpOutcome4.w1, JumpOutcome4.w2} := rfl

theorem extension4_nonempty (nr : NumeralReading) (s : ScopeReading) (u : TwoNot.Utt) :
    (extension4 nr s u).Nonempty := by
  -- For `null`: w0 always works (null is universally true).
  -- For `twoNot`: case split — exact surface is true ONLY at w2; other cases have w0.
  cases u
  case null => exact ⟨.w0, by rw [RSA.mem_extensionOf]; cases nr <;> cases s <;> rfl⟩
  case twoNot =>
    cases nr <;> cases s
    case exact.surface => exact ⟨.w2, by rw [RSA.mem_extensionOf]; rfl⟩
    case exact.inverse => exact ⟨.w0, by rw [RSA.mem_extensionOf]; rfl⟩
    case atLeast.surface => exact ⟨.w0, by rw [RSA.mem_extensionOf]; rfl⟩
    case atLeast.inverse => exact ⟨.w0, by rw [RSA.mem_extensionOf]; rfl⟩

/-! ### §12.2 L0 (literal listener) for the TwoNot model

Parameterized on numeral reading `nr` (exact vs at-least), determining the
extension's cardinality. -/

/-- TwoNot literal listener: uniform on extension under given numeral reading. -/
noncomputable def L0_4 (nr : NumeralReading) (s : ScopeReading) (u : TwoNot.Utt) :
    PMF JumpOutcome4 :=
  RSA.L0OfBoolMeaning (TwoNot.uttMeaning nr s) u (extension4_nonempty nr s u)

theorem L0_4_apply_of_true {nr : NumeralReading} {s : ScopeReading} {u : TwoNot.Utt}
    {w : JumpOutcome4} (h : TwoNot.uttMeaning nr s u w = true) :
    L0_4 nr s u w = ((extension4 nr s u).card : ℝ≥0∞)⁻¹ :=
  RSA.L0OfBoolMeaning_apply_of_mem _ h

theorem L0_4_apply_of_false {nr : NumeralReading} {s : ScopeReading} {u : TwoNot.Utt}
    {w : JumpOutcome4} (h : TwoNot.uttMeaning nr s u w ≠ true) :
    L0_4 nr s u w = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ h

/-! ### §12.3 D6-L0 — the structural foundation

At world `w2` (2 of 4 jumped), surface scope `twoNot` L0 mass is strictly
higher under exact than under at-least — because the extension cardinality
shrinks from 3 to 1. The S2 endorsement difference inherits from this. -/

/-- **D6-L0 (the structural foundation of the exact-semantics necessity claim)**:
at world `w2`, surface-scope `twoNot` L0 is strictly higher under EXACT
semantics (1) than under AT-LEAST semantics (1/3).

Proof: extension cardinality is 1 (exact) vs 3 (at-least); uniform-on-extension
gives 1/1 = 1 vs 1/3.

This single L0 fact propagates to S2 endorsement: under exact, S2 puts more
mass on `.twoNot` at w=2 (informative utterance pinpoints the world);
under at-least, the L0 dilutes across 3 worlds → less informative → lower
S2 endorsement. The structural mechanism behind paper's Figure 7. -/
theorem D6_L0_exact_gt_atLeast_at_w2 :
    L0_4 .atLeast .surface .twoNot .w2 < L0_4 .exact .surface .twoNot .w2 := by
  rw [L0_4_apply_of_true (by decide : TwoNot.uttMeaning .exact .surface .twoNot .w2 = true),
      L0_4_apply_of_true (by decide : TwoNot.uttMeaning .atLeast .surface .twoNot .w2 = true),
      extension4_exact_surface_twoNot, extension4_atLeast_surface_twoNot]
  -- Goal: ((Finset.card {w0, w1, w2} : ℕ) : ℝ≥0∞)⁻¹ < ((Finset.card {w2} : ℕ) : ℝ≥0∞)⁻¹
  -- = (3 : ℝ≥0∞)⁻¹ < (1 : ℝ≥0∞)⁻¹ = 1
  show ((3 : ℕ) : ℝ≥0∞)⁻¹ < ((1 : ℕ) : ℝ≥0∞)⁻¹
  rw [Nat.cast_one, Nat.cast_ofNat, inv_one]
  exact ENNReal.inv_lt_one.mpr (by norm_num)

/-! ### §12.4 D6-L0 — vacuous-zero contrast at the divergence worlds

The other side of the exact-vs-at-least divergence: at worlds w0 and w1
(where 0 or 1 horses jumped), surface-scope `twoNot` is FALSE under exact
("not exactly 2 didn't jump") but TRUE under at-least ("at least 2 didn't
jump"). So L0 mass under exact at these worlds is 0; L0 mass under at-least
is 1/3 (positive).

This is the "dilution" mechanism: at-least's broader extension means L0
mass spreads to "wrong" worlds. -/

/-- At worlds w0 and w1, exact L0 is zero (surface twoNot false), at-least
L0 is positive (surface twoNot true). -/
theorem D6_L0_exact_zero_atLeast_pos_at_w0 :
    L0_4 .exact .surface .twoNot .w0 = 0 ∧ L0_4 .atLeast .surface .twoNot .w0 ≠ 0 := by
  refine ⟨?_, ?_⟩
  · exact L0_4_apply_of_false (by decide : TwoNot.uttMeaning .exact .surface .twoNot .w0 ≠ true)
  · rw [L0_4_apply_of_true (by decide : TwoNot.uttMeaning .atLeast .surface .twoNot .w0 = true),
        extension4_atLeast_surface_twoNot]
    -- Goal: ((Finset.card {w0, w1, w2} : ℕ) : ℝ≥0∞)⁻¹ ≠ 0
    -- = (3 : ℝ≥0∞)⁻¹ ≠ 0; true since 3 ≠ ⊤
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

/-! ### §12.5 D6 deferred to Phase 4 continuation

The full D6 ("exact-semantics necessity for endorsement-rate divergence
between 1-of-2 and 2-of-4 contexts") requires:
1. TwoNot S1g layer (parameterized on `nr : NumeralReading`)
2. TwoNot marginalSpeaker (over Latent10)
3. TwoNot L1At + S2
4. The empirical comparison: at the 2-of-4 scenario (w=.w2), S2 endorsement of
   .twoNot is HIGHER under exact than under at-least

D6-L0 (this section) is the load-bearing structural foundation. The full
endorsement-rate inequality follows from the L0 mass difference propagating
through S1, but proving the propagation requires concrete numeric
arithmetic on the 5-world × 10-latent chain — same wall as L&G/Nouwen
headlines.

Stated D6 in this section captures the paper's structural mechanism (L0
mass concentration is what makes exact informative); the residue is the
arithmetic core. -/

end ScontrasPearl2021.TwoNot.PMF
