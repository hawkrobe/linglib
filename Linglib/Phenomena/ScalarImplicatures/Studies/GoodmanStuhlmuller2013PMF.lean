import Linglib.Theories.Pragmatics.RSA.Operators
import Linglib.Theories.Pragmatics.RSA.Silence
import Linglib.Phenomena.ScalarImplicatures.Studies.GoodmanStuhlmuller2013
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# @cite{goodman-stuhlmuller-2013} on mathlib `PMF` (Phase 2 stress test)
@cite{goodman-stuhlmuller-2013}

Third stress test for the Phase-2 architecture. GS2013 differs from
@cite{frank-goodman-2012} (FG2012) and @cite{kao-etal-2014-metaphor} on
*every* axis that mattered for those pilots:

* **Two posteriors**: the speaker has imperfect access to the world via a
  hypergeometric *observation* kernel ⇒ `PMF.posterior` enters at both the
  speaker-belief layer (obs → world) and the listener layer (utt → world).
* **Real-valued score**: `S1 ∝ exp(α · Σ_s P(s | obs) · log P_lex(s | u))` —
  log/exp arithmetic is real, lifted to `ℝ≥0∞` at the `PMF.normalize`
  boundary via `RSA.softmaxBelief`.
* **Latent-variable bind**: `L1` inverts the *obs-marginalised* speaker
  `marginalSpeaker = obsKernel.bindOnSupport S1g`.

## PMF stack

* `worldPrior : PMF WorldState` — uniform on 4 states
* `obsKernel : Access → WorldState → PMF Obs` — `PMF.normalize` of the
  unnormalised hypergeometric numerator; `PMF.normalize` absorbs `C(N, n)`
* `speakerBelief : Obs → PMF WorldState` — `PMF.posterior` of `obsKernel`
* `S1g : Obs → PMF U` — `PMF.normalize` of `RSA.softmaxBelief`
* `marginalSpeaker : Access → WorldState → PMF U` — `PMF.bindOnSupport` over
  obs; the partial `S1g` is only invoked on obs that the kernel actually
  reaches (`bindOnSupport` is mathlib's idiom for this exact pattern)
* `L1 : Access → U → PMF WorldState` — `PMF.posterior` of marginal speaker

## A real model defect surfaces under PMF

The original `gsCfg` resolves `0/0 = 0` silently at the `RSAConfig.S1` step.
PMF cannot — `PMF.normalize` requires a nonzero finite tsum. For some
`(meaning, a, w)` triples there is *no* quality-OK utterance reachable from
`(obsKernel a w).support`: e.g. `lbMeaning` at `(.a3, .s0)`, where the only
reachable obs is `.o0a3` and no numeral in `{one, two, three}` is true at
`s0`. The PMF formulation forces this to be made explicit at the
`marginalSpeaker` / `L1` call site as a cover hypothesis. The quantifier
model has full cover at full access (`qCover_a3`); the lower-bound numeral
model only has *partial* cover (`lbCover_a3_partial`, restricted to
`w ≠ .s0`) — see `lb_defect_at_o0a3` for the honest no-witness theorem.

## Scope of this file

Definitions + cover infrastructure + 4 of 11 silence-extended paper
findings proven (the `.a3` cases — paper findings 1, 4, 6, 7). Each `.a3`
case follows the structural template:

1. `unfold L1 worldPrior`
2. `rw [PMF.posterior_lt_iff_kernel_lt_of_uniform]` (or `_le_`)
3. `rw [marginalSpeaker_a3_sX_apply, marginalSpeaker_a3_sY_apply]` —
   collapse to `S1g` evaluations at the two diagonal obs
4. `apply PMF.normalize_lt_of_apply_eq_of_sum_lt` — reduce to a
   sum-of-scores comparison
5. Discharge via per-(obs, utt) `s1Score_*Lifted_o*_apply` helpers and
   per-obs `sum_s1Score_*Lifted_o*` helpers.

Remaining 7 findings (`.a1` / `.a2` cases) require non-concentrated obs
kernel + non-concentrated belief substrate; see TODO doc note at the end
of the `Findings` namespace for the substrate they need + numerical
predictions.

Grounding theorem to legacy `gsCfg` left as TODO — manual discharge
requires unfolding two normalisation chains and showing equality of
finite sums; blocked on PMF-shaped `rsa_predict`.

## Reused from `GoodmanStuhlmuller2013.lean`

* `WorldState`, `Access`, `Obs`, `Finding` — domain types and findings list
* `obsCompatible`, `qualityOk` — combinatorial constraints
* `qMeaning`, `lbMeaning`, `QUtt`, `NumUtt` — utterance alphabets and semantics
-/

set_option autoImplicit false

namespace Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013.PMF

open scoped ENNReal
open Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013

/-! ## §1. World prior — uniform on `WorldState` -/

noncomputable def worldPrior : PMF WorldState := PMF.uniformOfFintype WorldState

theorem worldPrior_ne_zero (w : WorldState) : worldPrior w ≠ 0 :=
  (worldPrior.mem_support_iff w).mp (PMF.mem_support_uniformOfFintype w)

/-- The uniform world prior assigns `ENNReal.ofReal (1/4)` to every world. -/
theorem worldPrior_apply (s : WorldState) :
    worldPrior s = ENNReal.ofReal (1/4 : ℝ) := by
  unfold worldPrior
  rw [PMF.uniformOfFintype_apply]
  show ((4 : ℕ) : ℝ≥0∞)⁻¹ = _
  rw [show ((4 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 4 from by simp,
      ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  congr 1; norm_num

/-! ## §2. Hypergeometric observation kernel

For access `a` and world `w` (with `K = w.toNat` successes among `N = 3`),
`obsKernelRaw a w obs = C(K, k) · C(N−K, n−k)` is the unnormalised
hypergeometric numerator. `PMF.normalize` absorbs the `C(N, n)` denominator.
Off-access obs get `0` (the kernel for access `a` only puts mass on obs at
access `a`). -/

noncomputable def obsKernelRaw (a : Access) (w : WorldState) (obs : Obs) : ℝ≥0∞ :=
  if obs.access = a then
    (Nat.choose w.toNat obs.count *
      Nat.choose (3 - w.toNat) (obs.sampleSize - obs.count) : ℕ)
  else 0

/-- Diagonal-witness obs for `(a, w)`: the obs at access `a` with `count`
clipped to `min(w.toNat, a.toNat)`. Drives `C(K, k) · C(N−K, n−k) > 0`. -/
def diagObs : Access → WorldState → Obs
  | .a1, .s0 => .o0a1 | .a1, .s1 => .o1a1 | .a1, .s2 => .o1a1 | .a1, .s3 => .o1a1
  | .a2, .s0 => .o0a2 | .a2, .s1 => .o1a2 | .a2, .s2 => .o2a2 | .a2, .s3 => .o2a2
  | .a3, .s0 => .o0a3 | .a3, .s1 => .o1a3 | .a3, .s2 => .o2a3 | .a3, .s3 => .o3a3

theorem obsKernelRaw_diagObs_ne_zero (a : Access) (w : WorldState) :
    obsKernelRaw a w (diagObs a w) ≠ 0 := by
  cases a <;> cases w <;>
    (unfold obsKernelRaw diagObs Obs.access Obs.count Obs.sampleSize WorldState.toNat
     simp)

theorem obsKernelRaw_tsum_ne_zero (a : Access) (w : WorldState) :
    ∑' obs, obsKernelRaw a w obs ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨diagObs a w, obsKernelRaw_diagObs_ne_zero a w⟩

theorem obsKernelRaw_tsum_ne_top (a : Access) (w : WorldState) :
    ∑' obs, obsKernelRaw a w obs ≠ ∞ := by
  refine ENNReal.tsum_ne_top_of_fintype fun obs => ?_
  unfold obsKernelRaw
  split
  · exact ENNReal.natCast_ne_top _
  · exact ENNReal.zero_ne_top

/-- Hypergeometric observation kernel `P(obs | a, w)`. -/
noncomputable def obsKernel (a : Access) (w : WorldState) : PMF Obs :=
  PMF.normalize (obsKernelRaw a w)
    (obsKernelRaw_tsum_ne_zero a w) (obsKernelRaw_tsum_ne_top a w)

theorem obsKernel_apply_ne_zero {a : Access} {w : WorldState} {obs : Obs}
    (h : obsKernelRaw a w obs ≠ 0) : obsKernel a w obs ≠ 0 := by
  rw [obsKernel, ← PMF.mem_support_iff, PMF.mem_support_normalize_iff]
  exact h

theorem mem_support_obsKernel_iff {a : Access} {w : WorldState} {obs : Obs} :
    obs ∈ (obsKernel a w).support ↔ obsKernelRaw a w obs ≠ 0 := by
  rw [obsKernel, PMF.mem_support_normalize_iff]

/-- Obs in the support of `obsKernel a w` necessarily have `obs.access = a`
— off-access obs have raw mass `0` by construction. -/
theorem obsKernel_support_access {a : Access} {w : WorldState} {obs : Obs}
    (h : obs ∈ (obsKernel a w).support) : obs.access = a := by
  rw [mem_support_obsKernel_iff] at h
  unfold obsKernelRaw at h
  by_contra hne
  rw [if_neg hne] at h
  exact h rfl

/-! ## §3. Speaker belief — `PMF.posterior` of `obsKernel`

Given an observation, the speaker infers a posterior over worlds via Bayes'
rule. With a uniform world prior this is the row-normalised hypergeometric. -/

/-- Inverse-of-diagonal witness: for any obs, the world matching its count is
obs-compatible. -/
def obsToWorld : Obs → WorldState
  | .o0a1 | .o0a2 | .o0a3 => .s0
  | .o1a1 | .o1a2 | .o1a3 => .s1
  | .o2a2 | .o2a3 => .s2
  | .o3a3 => .s3

theorem obsKernelRaw_obsToWorld_ne_zero (obs : Obs) :
    obsKernelRaw obs.access (obsToWorld obs) obs ≠ 0 := by
  cases obs <;>
    (unfold obsKernelRaw obsToWorld Obs.access Obs.count Obs.sampleSize WorldState.toNat
     simp)

theorem obsMarginal_ne_zero (obs : Obs) :
    PMF.marginal (obsKernel obs.access) worldPrior obs ≠ 0 :=
  PMF.marginal_ne_zero _ worldPrior obs
    (worldPrior_ne_zero (obsToWorld obs))
    (obsKernel_apply_ne_zero (obsKernelRaw_obsToWorld_ne_zero obs))

/-- Speaker's posterior over worlds given an observation. -/
noncomputable def speakerBelief (obs : Obs) : PMF WorldState :=
  PMF.posterior (obsKernel obs.access) worldPrior obs (obsMarginal_ne_zero obs)

/-! ## §4. Score function — instantiates `RSA.softmaxBelief`

`s1Score` is `RSA.softmaxBelief` applied with:
* `lex u s` — uniform-on-extension lit prob (Real-valued for `Real.log`)
* `belief s` — posterior over worlds (Real-projected from `speakerBelief obs`)
* `qOk u` — quality filter at `obs`

Cover lemmas in §8 supply the `∃ u, qualityOk meaning obs u` witness; via
`RSA.softmaxBelief_tsum_ne_zero_of_witness` this discharges the
`PMF.normalize` precondition. -/

/-- Real-valued literal probability: uniform on the extension. -/
noncomputable def lexReal {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool) (u : U) (s : WorldState) : ℝ :=
  if meaning u s then ((RSA.extensionOf meaning u).card : ℝ)⁻¹ else 0

/-- Real-valued speaker belief, projected from `speakerBelief` PMF. -/
noncomputable def beliefReal (obs : Obs) (s : WorldState) : ℝ :=
  (speakerBelief obs s).toReal

/-- The Goodman-family speaker score, instantiating `RSA.softmaxBelief`.

The Bool predicate `qualityOk meaning obs ·` is wrapped as the Prop
`qualityOk meaning obs · = true` to match `RSA.softmaxBelief`'s
`qOk : U → Prop` signature. Decidability is automatic (`Bool` equality
is decidable). -/
noncomputable abbrev s1Score {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool) (α : ℝ) (obs : Obs) (u : U) : ℝ≥0∞ :=
  RSA.softmaxBelief (lexReal meaning) (beliefReal obs) α
    (fun u' => qualityOk meaning obs u' = true) u

/-! ## §5. `S1g` — speaker conditional on observation -/

noncomputable def S1g {U : Type*} [Fintype U] (meaning : U → WorldState → Bool)
    (α : ℝ) (obs : Obs) (h0 : ∑' u, s1Score meaning α obs u ≠ 0) : PMF U :=
  PMF.normalize (s1Score meaning α obs ·) h0
    (RSA.softmaxBelief_tsum_ne_top _ _ _ _)

theorem mem_support_S1g_iff {U : Type*} [Fintype U]
    {meaning : U → WorldState → Bool} {α : ℝ} {obs : Obs}
    (h0 : ∑' u, s1Score meaning α obs u ≠ 0) (u : U) :
    u ∈ (S1g meaning α obs h0).support ↔ s1Score meaning α obs u ≠ 0 := by
  rw [S1g, PMF.mem_support_normalize_iff]

/-! ## §6. Marginal speaker — `PMF.bindOnSupport` over the obs kernel

`bindOnSupport` is mathlib's idiom for binding to a kernel that is partial
on the prior's support. The cover hypothesis only needs to provide a
quality-OK witness for obs that `obsKernel a w` actually reaches — no
junk-PMF fallback, no subtype gymnastics, no off-access bookkeeping. -/

noncomputable def marginalSpeaker {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool) (α : ℝ) (a : Access) (w : WorldState)
    (hCov : ∀ obs ∈ (obsKernel a w).support, ∃ u : U, qualityOk meaning obs u) :
    PMF U :=
  (obsKernel a w).bindOnSupport fun obs hObs =>
    S1g meaning α obs
      (RSA.softmaxBelief_tsum_ne_zero_of_witness (hCov obs hObs).choose_spec)

/-! ## §7. `L1` — Bayesian inversion of the marginal speaker

The cover hypothesis here is `∀ w, marginalSpeaker-cover at w` since L1's
`PMF.marginal` integrates `marginalSpeaker w u` over the world prior. -/

noncomputable def L1 {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool) (α : ℝ) (a : Access)
    (hCov : ∀ w : WorldState, ∀ obs ∈ (obsKernel a w).support,
              ∃ u : U, qualityOk meaning obs u) (u : U)
    (hMarg : PMF.marginal (fun w => marginalSpeaker meaning α a w (hCov w))
                worldPrior u ≠ 0) : PMF WorldState :=
  PMF.posterior (fun w => marginalSpeaker meaning α a w (hCov w)) worldPrior u hMarg

theorem mem_support_L1_iff {U : Type*} [Fintype U]
    {meaning : U → WorldState → Bool} {α : ℝ} {a : Access}
    {hCov : ∀ w : WorldState, ∀ obs ∈ (obsKernel a w).support,
              ∃ u : U, qualityOk meaning obs u} {u : U}
    (hMarg : PMF.marginal (fun w => marginalSpeaker meaning α a w (hCov w))
                worldPrior u ≠ 0) (w : WorldState) :
    w ∈ (L1 meaning α a hCov u hMarg).support ↔
      worldPrior w ≠ 0 ∧ marginalSpeaker meaning α a w (hCov w) u ≠ 0 :=
  PMF.mem_support_posterior_iff _ _ _ _ _

/-! ## §8. Cover lemmas

At full access (`.a3`), the hypergeometric is deterministic: `obsKernel .a3 w`
puts all mass on `diagObs .a3 w`. Cover therefore reduces to "`diagObs .a3 w`
has a quality-OK utterance for every world".

For quantifiers: `.none_`/`.some_`/`.all` cover all four worlds. ✓
For lower-bound numerals: `.o0a3` (the diag at `.s0`) has *no* quality-OK
numeral — every numeral requires `≥ 1`. The paper sidesteps this by
restricting the empirical experiment to `(word, sample)` pairs where the
word's lower bound does not exceed the number observed (page 180,
"sensible situations"). -/

theorem qCover_a3 (w : WorldState) :
    ∀ obs ∈ (obsKernel .a3 w).support, ∃ u : QUtt, qualityOk qMeaning obs u := by
  intro obs hObs
  have hAcc : obs.access = .a3 := obsKernel_support_access hObs
  cases obs
  · exact absurd hAcc (by decide)  -- .o0a1
  · exact absurd hAcc (by decide)  -- .o1a1
  · exact absurd hAcc (by decide)  -- .o0a2
  · exact absurd hAcc (by decide)  -- .o1a2
  · exact absurd hAcc (by decide)  -- .o2a2
  · exact ⟨.none_, by decide⟩      -- .o0a3 — n=0 of 3, .none_ is true at s0
  · exact ⟨.some_, by decide⟩      -- .o1a3
  · exact ⟨.some_, by decide⟩      -- .o2a3
  · exact ⟨.all,   by decide⟩      -- .o3a3

/-- Defect for the quantifier model at minimal access: at `.o0a1`, the only
compatible worlds are `{s0, s1, s2}`, and no element of `{none_, some_, all}`
holds at all three (they require `=0`, `≥1`, `=3` respectively). The same
applies for `.o0a2` (compatible with `{s0, s1}`). Hence there is no
fully-quantified `qCover` at `.a1` / `.a2`; consumers thread the cover
hypothesis through `marginalSpeaker` / `L1` directly. -/
theorem qMeaning_no_witness_at_o0a1 :
    ¬ ∃ u : QUtt, qualityOk qMeaning .o0a1 u := by
  rintro ⟨u, hu⟩
  cases u <;> exact absurd hu (by decide)

/-- The lb defect: at `.o0a3`, no LB numeral is true at the (only) compatible
world `.s0`. -/
theorem lb_defect_at_o0a3 :
    ¬ ∃ u : NumUtt, qualityOk lbMeaning .o0a3 u := by
  rintro ⟨u, hu⟩
  cases u <;> exact absurd hu (by decide)

/-- Partial cover: `lbMeaning` at `.a3` has a quality-OK numeral for every
obs reachable from a world `w ≠ .s0`. Use as `hCov w hw` then `lbCover_a3_partial w hw`
at `marginalSpeaker` / `L1` call sites. -/
theorem lbCover_a3_partial (w : WorldState) (hw : w ≠ .s0) :
    ∀ obs ∈ (obsKernel .a3 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u := by
  intro obs hObs
  have hAcc : obs.access = .a3 := obsKernel_support_access hObs
  -- At `.a3` the support is exactly `{diagObs .a3 w}`. We split on obs and
  -- discharge wrong-access cases via `hAcc`, the `.o0a3` case via `hw` (we
  -- show `obsKernelRaw .a3 w .o0a3 = 0` for `w ≠ .s0`), and the rest by
  -- `.one`.
  cases obs
  · exact absurd hAcc (by decide)
  · exact absurd hAcc (by decide)
  · exact absurd hAcc (by decide)
  · exact absurd hAcc (by decide)
  · exact absurd hAcc (by decide)
  · -- .o0a3: requires obsKernelRaw .a3 w .o0a3 ≠ 0; for w ≠ s0 this is false
    exfalso
    rw [mem_support_obsKernel_iff] at hObs
    apply hObs
    cases w
    · exact absurd rfl hw
    all_goals (unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat; simp)
  · exact ⟨.one, by decide⟩
  · exact ⟨.one, by decide⟩
  · exact ⟨.one, by decide⟩

/-! ## §9. Grounding theorem to legacy `gsCfg`

The two file's `L1`s should agree pointwise (both compute the same Bayesian
posterior of the same Goodman-family score). Proof deferred until the
PMF-shaped `rsa_predict` tactic ships — manual discharge requires
unfolding two normalisation chains and showing equality of finite sums. -/

-- TODO: state and prove the grounding theorem
--   `(L1 qMeaning α .a3 (qCover_a3) u hMarg s).toReal = (gsCfg qMeaning .a3).L1 ... s`.
-- The two file's `L1`s should agree pointwise (both compute the same Bayesian
-- posterior of the same Goodman-family score). Blocked on PMF-shaped
-- `rsa_predict` — manual discharge requires unfolding two normalisation chains
-- and showing equality of finite sums.

/-! ## §10. Silence-extended utterance types

`RSA.WithSilence`, `RSA.liftMeaning`, and the simp lemmas live in
`Theories/Pragmatics/RSA/Silence.lean` (generic substrate). Each consumer
paper proves its own `cover_silent` from the generic `liftMeaning_none`
simp lemma — the cover proof is paper-specific because `qualityOk`
depends on the paper's observation type.

Following @cite{bergen-levy-goodman-2016}, silence has universal extension
(`liftMeaning` makes it true at every world), giving it the smallest lex
value (`1/4` for our 4-world setting). This dissolves the "no `qOk`
witness" defect that made the paper's `(access, word) ∉ {1/1, 2/1, 2/2,
3/1, 3/2, 3/3}` cases vacuous. -/

open RSA (WithSilence liftMeaning)

/-- Universal cover: silence (`none`) is `qOk` at every obs because
`liftMeaning m none _ = true` at every world. The cover hypothesis is
automatically discharged for any `liftMeaning`-lifted model — paper-specific
because `qualityOk` depends on `obsCompatible`. -/
theorem cover_silent {U : Type*} (m : U → WorldState → Bool) (a : Access) (w : WorldState) :
    ∀ obs ∈ (obsKernel a w).support,
      ∃ u : WithSilence U, qualityOk (liftMeaning m) obs u := by
  intro obs _
  refine ⟨none, ?_⟩
  simp only [qualityOk, RSA.liftMeaning_none, Bool.or_true, List.all_cons, List.all_nil,
             Bool.and_true]

/-! ## §10.1. Per-obs/per-world structural collapses

These helpers express the deterministic-at-`.a3` structure of the obsKernel
and speakerBelief as `pure` PMFs — enabling `marginalSpeaker` to collapse
to a single `S1g` evaluation. They're independent of the meaning function. -/

private theorem obsKernel_a3_s0_eq_pure : obsKernel .a3 .s0 = PMF.pure .o0a3 := by
  apply PMF.normalize_eq_pure_of_singleton_support
  intro y hy
  cases y <;>
    first
      | exact absurd rfl hy
      | (unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat; simp)

private theorem obsKernel_a3_s1_eq_pure : obsKernel .a3 .s1 = PMF.pure .o1a3 := by
  apply PMF.normalize_eq_pure_of_singleton_support
  intro y hy
  cases y <;>
    first
      | exact absurd rfl hy
      | (unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat; simp)

private theorem obsKernel_a3_s2_eq_pure : obsKernel .a3 .s2 = PMF.pure .o2a3 := by
  apply PMF.normalize_eq_pure_of_singleton_support
  intro y hy
  cases y <;>
    first
      | exact absurd rfl hy
      | (unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat; simp)

private theorem obsKernel_a3_s3_eq_pure : obsKernel .a3 .s3 = PMF.pure .o3a3 := by
  apply PMF.normalize_eq_pure_of_singleton_support
  intro y hy
  cases y <;>
    first
      | exact absurd rfl hy
      | (unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat; simp)

private theorem obsKernel_apply_zero_of_raw_zero {a : Access} {w : WorldState} {obs : Obs}
    (h : obsKernelRaw a w obs = 0) : obsKernel a w obs = 0 := by
  rw [obsKernel, PMF.normalize_apply, h, zero_mul]

private theorem speakerBelief_o0a3_eq_pure :
    speakerBelief .o0a3 = PMF.pure .s0 := by
  apply PMF.posterior_eq_pure_of_singleton_score_support
  intro s' hs'
  right
  refine obsKernel_apply_zero_of_raw_zero ?_
  cases s' <;>
    first
      | exact absurd rfl hs'
      | (unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat; simp)

private theorem speakerBelief_o1a3_eq_pure :
    speakerBelief .o1a3 = PMF.pure .s1 := by
  apply PMF.posterior_eq_pure_of_singleton_score_support
  intro s' hs'
  right
  refine obsKernel_apply_zero_of_raw_zero ?_
  cases s' <;>
    first
      | exact absurd rfl hs'
      | (unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat; simp)

private theorem speakerBelief_o2a3_eq_pure :
    speakerBelief .o2a3 = PMF.pure .s2 := by
  apply PMF.posterior_eq_pure_of_singleton_score_support
  intro s' hs'
  right
  refine obsKernel_apply_zero_of_raw_zero ?_
  cases s' <;>
    first
      | exact absurd rfl hs'
      | (unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat; simp)

private theorem speakerBelief_o3a3_eq_pure :
    speakerBelief .o3a3 = PMF.pure .s3 := by
  apply PMF.posterior_eq_pure_of_singleton_score_support
  intro s' hs'
  right
  refine obsKernel_apply_zero_of_raw_zero ?_
  cases s' <;>
    first
      | exact absurd rfl hs'
      | (unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat; simp)

private theorem beliefReal_o0a3 (s : WorldState) :
    beliefReal .o0a3 s = if s = .s0 then 1 else 0 := by
  unfold beliefReal
  rw [speakerBelief_o0a3_eq_pure, PMF.pure_apply]
  split_ifs with h <;> simp

private theorem beliefReal_o1a3 (s : WorldState) :
    beliefReal .o1a3 s = if s = .s1 then 1 else 0 := by
  unfold beliefReal
  rw [speakerBelief_o1a3_eq_pure, PMF.pure_apply]
  split_ifs with h <;> simp

private theorem beliefReal_o2a3 (s : WorldState) :
    beliefReal .o2a3 s = if s = .s2 then 1 else 0 := by
  unfold beliefReal
  rw [speakerBelief_o2a3_eq_pure, PMF.pure_apply]
  split_ifs with h <;> simp

private theorem beliefReal_o3a3 (s : WorldState) :
    beliefReal .o3a3 s = if s = .s3 then 1 else 0 := by
  unfold beliefReal
  rw [speakerBelief_o3a3_eq_pure, PMF.pure_apply]
  split_ifs with h <;> simp

private theorem obsKernel_a3_s0_apply_diag : obsKernel .a3 .s0 .o0a3 = 1 := by
  rw [obsKernel_a3_s0_eq_pure, PMF.pure_apply, if_pos rfl]

private theorem obsKernel_a3_s1_apply_diag : obsKernel .a3 .s1 .o1a3 = 1 := by
  rw [obsKernel_a3_s1_eq_pure, PMF.pure_apply, if_pos rfl]

private theorem obsKernel_a3_s2_apply_diag : obsKernel .a3 .s2 .o2a3 = 1 := by
  rw [obsKernel_a3_s2_eq_pure, PMF.pure_apply, if_pos rfl]

private theorem obsKernel_a3_s3_apply_diag : obsKernel .a3 .s3 .o3a3 = 1 := by
  rw [obsKernel_a3_s3_eq_pure, PMF.pure_apply, if_pos rfl]

private theorem obsKernel_a3_s0_apply_off {b : Obs} (h : b ≠ .o0a3) :
    obsKernel .a3 .s0 b = 0 := by
  rw [PMF.apply_eq_zero_iff]
  rw [obsKernel_a3_s0_eq_pure, PMF.support_pure]
  simp [h]

private theorem obsKernel_a3_s1_apply_off {b : Obs} (h : b ≠ .o1a3) :
    obsKernel .a3 .s1 b = 0 := by
  rw [PMF.apply_eq_zero_iff]
  rw [obsKernel_a3_s1_eq_pure, PMF.support_pure]
  simp [h]

private theorem obsKernel_a3_s2_apply_off {b : Obs} (h : b ≠ .o2a3) :
    obsKernel .a3 .s2 b = 0 := by
  rw [PMF.apply_eq_zero_iff]
  rw [obsKernel_a3_s2_eq_pure, PMF.support_pure]
  simp [h]

private theorem obsKernel_a3_s3_apply_off {b : Obs} (h : b ≠ .o3a3) :
    obsKernel .a3 .s3 b = 0 := by
  rw [PMF.apply_eq_zero_iff]
  rw [obsKernel_a3_s3_eq_pure, PMF.support_pure]
  simp [h]

/-- `marginalSpeaker` at `.a3 .s0` collapses to `S1g` at the diagonal obs. -/
private theorem marginalSpeaker_a3_s0_apply
    {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool)
    (hCov : ∀ obs ∈ (obsKernel .a3 .s0).support, ∃ u : U, qualityOk meaning obs u)
    (u : U) :
    marginalSpeaker meaning 1 .a3 .s0 hCov u =
      S1g meaning 1 .o0a3
        (RSA.softmaxBelief_tsum_ne_zero_of_witness
          (hCov .o0a3 (by rw [obsKernel_a3_s0_eq_pure]; simp)).choose_spec) u := by
  unfold marginalSpeaker
  rw [PMF.bindOnSupport_apply, tsum_eq_single Obs.o0a3]
  · have h_ne : obsKernel .a3 .s0 Obs.o0a3 ≠ 0 := by
      rw [obsKernel_a3_s0_apply_diag]; norm_num
    rw [dif_neg h_ne, obsKernel_a3_s0_apply_diag, one_mul]
  · intro b hb
    exact mul_eq_zero.mpr (Or.inl (obsKernel_a3_s0_apply_off hb))

private theorem marginalSpeaker_a3_s1_apply
    {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool)
    (hCov : ∀ obs ∈ (obsKernel .a3 .s1).support, ∃ u : U, qualityOk meaning obs u)
    (u : U) :
    marginalSpeaker meaning 1 .a3 .s1 hCov u =
      S1g meaning 1 .o1a3
        (RSA.softmaxBelief_tsum_ne_zero_of_witness
          (hCov .o1a3 (by rw [obsKernel_a3_s1_eq_pure]; simp)).choose_spec) u := by
  unfold marginalSpeaker
  rw [PMF.bindOnSupport_apply, tsum_eq_single Obs.o1a3]
  · have h_ne : obsKernel .a3 .s1 Obs.o1a3 ≠ 0 := by
      rw [obsKernel_a3_s1_apply_diag]; norm_num
    rw [dif_neg h_ne, obsKernel_a3_s1_apply_diag, one_mul]
  · intro b hb
    exact mul_eq_zero.mpr (Or.inl (obsKernel_a3_s1_apply_off hb))

/-- `marginalSpeaker` at `.a3 .s2` collapses to `S1g` at the diagonal obs. -/
private theorem marginalSpeaker_a3_s2_apply
    {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool)
    (hCov : ∀ obs ∈ (obsKernel .a3 .s2).support, ∃ u : U, qualityOk meaning obs u)
    (u : U) :
    marginalSpeaker meaning 1 .a3 .s2 hCov u =
      S1g meaning 1 .o2a3
        (RSA.softmaxBelief_tsum_ne_zero_of_witness
          (hCov .o2a3 (by rw [obsKernel_a3_s2_eq_pure]; simp)).choose_spec) u := by
  unfold marginalSpeaker
  rw [PMF.bindOnSupport_apply, tsum_eq_single Obs.o2a3]
  · have h_ne : obsKernel .a3 .s2 Obs.o2a3 ≠ 0 := by
      rw [obsKernel_a3_s2_apply_diag]; norm_num
    rw [dif_neg h_ne, obsKernel_a3_s2_apply_diag, one_mul]
  · intro b hb
    exact mul_eq_zero.mpr (Or.inl (obsKernel_a3_s2_apply_off hb))

private theorem marginalSpeaker_a3_s3_apply
    {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool)
    (hCov : ∀ obs ∈ (obsKernel .a3 .s3).support, ∃ u : U, qualityOk meaning obs u)
    (u : U) :
    marginalSpeaker meaning 1 .a3 .s3 hCov u =
      S1g meaning 1 .o3a3
        (RSA.softmaxBelief_tsum_ne_zero_of_witness
          (hCov .o3a3 (by rw [obsKernel_a3_s3_eq_pure]; simp)).choose_spec) u := by
  unfold marginalSpeaker
  rw [PMF.bindOnSupport_apply, tsum_eq_single Obs.o3a3]
  · have h_ne : obsKernel .a3 .s3 Obs.o3a3 ≠ 0 := by
      rw [obsKernel_a3_s3_apply_diag]; norm_num
    rw [dif_neg h_ne, obsKernel_a3_s3_apply_diag, one_mul]
  · intro b hb
    exact mul_eq_zero.mpr (Or.inl (obsKernel_a3_s3_apply_off hb))

/-! ## §10.2. `s1Score` evaluation via softmax-collapse

At `.a3`, the speaker's belief is concentrated (`pure`) so the softmax
collapses to the literal lex value. These helpers express `s1Score` for
`liftMeaning`-lifted utterances at the diagonal observations. -/

/-- `s1Score` is non-zero iff the quality predicate holds. -/
private theorem s1Score_ne_zero_iff_qualityOk
    {U : Type*} [Fintype U]
    {meaning : U → WorldState → Bool} {α : ℝ} {obs : Obs} {u : U} :
    s1Score meaning α obs u ≠ 0 ↔ qualityOk meaning obs u = true := by
  unfold s1Score RSA.softmaxBelief
  constructor
  · intro h
    by_contra hQ
    rw [Bool.not_eq_true] at hQ
    rw [if_neg (by simp [hQ])] at h
    exact h rfl
  · intro h
    rw [if_pos h]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

/-- For `liftMeaning`-lifted models, `s1Score` at `.o0a3` collapses to
`ENNReal.ofReal (lexReal (liftMeaning m) u .s0)` when qOk-passing,
`0` otherwise. -/
private theorem s1Score_liftMeaning_o0a3_apply
    {U : Type*} [Fintype U] [DecidableEq U]
    (m : U → WorldState → Bool) (u : WithSilence U)
    (h_pos : qualityOk (liftMeaning m) .o0a3 u = true →
              0 < lexReal (liftMeaning m) u .s0) :
    s1Score (liftMeaning m) 1 .o0a3 u =
      if qualityOk (liftMeaning m) .o0a3 u
      then ENNReal.ofReal (lexReal (liftMeaning m) u .s0) else 0 := by
  show RSA.softmaxBelief (lexReal (liftMeaning m)) (beliefReal .o0a3) 1
        (fun u' => qualityOk (liftMeaning m) .o0a3 u') u = _
  rw [show beliefReal .o0a3 = (fun s => if s = .s0 then 1 else 0) from
        funext beliefReal_o0a3]
  exact RSA.softmaxBelief_concentrated_apply _ _ _ _ h_pos

private theorem s1Score_liftMeaning_o1a3_apply
    {U : Type*} [Fintype U] [DecidableEq U]
    (m : U → WorldState → Bool) (u : WithSilence U)
    (h_pos : qualityOk (liftMeaning m) .o1a3 u = true →
              0 < lexReal (liftMeaning m) u .s1) :
    s1Score (liftMeaning m) 1 .o1a3 u =
      if qualityOk (liftMeaning m) .o1a3 u
      then ENNReal.ofReal (lexReal (liftMeaning m) u .s1) else 0 := by
  show RSA.softmaxBelief (lexReal (liftMeaning m)) (beliefReal .o1a3) 1
        (fun u' => qualityOk (liftMeaning m) .o1a3 u') u = _
  rw [show beliefReal .o1a3 = (fun s => if s = .s1 then 1 else 0) from
        funext beliefReal_o1a3]
  exact RSA.softmaxBelief_concentrated_apply _ _ _ _ h_pos

/-- For `liftMeaning`-lifted models, `s1Score` at `.o2a3` collapses to
`ENNReal.ofReal (lexReal (liftMeaning m) u .s2)` when qOk-passing,
`0` otherwise. -/
private theorem s1Score_liftMeaning_o2a3_apply
    {U : Type*} [Fintype U] [DecidableEq U]
    (m : U → WorldState → Bool) (u : WithSilence U)
    (h_pos : qualityOk (liftMeaning m) .o2a3 u = true →
              0 < lexReal (liftMeaning m) u .s2) :
    s1Score (liftMeaning m) 1 .o2a3 u =
      if qualityOk (liftMeaning m) .o2a3 u
      then ENNReal.ofReal (lexReal (liftMeaning m) u .s2) else 0 := by
  show RSA.softmaxBelief (lexReal (liftMeaning m)) (beliefReal .o2a3) 1
        (fun u' => qualityOk (liftMeaning m) .o2a3 u') u = _
  rw [show beliefReal .o2a3 = (fun s => if s = .s2 then 1 else 0) from
        funext beliefReal_o2a3]
  exact RSA.softmaxBelief_concentrated_apply _ _ _ _ h_pos

private theorem s1Score_liftMeaning_o3a3_apply
    {U : Type*} [Fintype U] [DecidableEq U]
    (m : U → WorldState → Bool) (u : WithSilence U)
    (h_pos : qualityOk (liftMeaning m) .o3a3 u = true →
              0 < lexReal (liftMeaning m) u .s3) :
    s1Score (liftMeaning m) 1 .o3a3 u =
      if qualityOk (liftMeaning m) .o3a3 u
      then ENNReal.ofReal (lexReal (liftMeaning m) u .s3) else 0 := by
  show RSA.softmaxBelief (lexReal (liftMeaning m)) (beliefReal .o3a3) 1
        (fun u' => qualityOk (liftMeaning m) .o3a3 u') u = _
  rw [show beliefReal .o3a3 = (fun s => if s = .s3 then 1 else 0) from
        funext beliefReal_o3a3]
  exact RSA.softmaxBelief_concentrated_apply _ _ _ _ h_pos

/-! ## §10.3. Lex evaluations for the silence-extended quantifier model

The four utterances of `WithSilence QUtt` have these extension cards:
- `some QUtt.none_`: extension = `{.s0}`, card = 1, lex .s0 = 1.
- `some QUtt.some_`: extension = `{.s1, .s2, .s3}`, card = 3, lex = 1/3.
- `some QUtt.all`: extension = `{.s3}`, card = 1, lex .s3 = 1.
- `none` (silence): extension = `{.s0, .s1, .s2, .s3}`, card = 4, lex = 1/4. -/

private theorem extensionOf_qLifted_some_some_card :
    (RSA.extensionOf (liftMeaning qMeaning) (some QUtt.some_)).card = 3 := by decide

private theorem extensionOf_qLifted_all_card :
    (RSA.extensionOf (liftMeaning qMeaning) (some QUtt.all)).card = 1 := by decide

private theorem extensionOf_qLifted_silent_card :
    (RSA.extensionOf (liftMeaning qMeaning) (none : WithSilence QUtt)).card = 4 := by decide

private theorem lexReal_qLifted_some_some (s : WorldState)
    (h : qMeaning .some_ s = true) :
    lexReal (liftMeaning qMeaning) (some QUtt.some_) s = 1/3 := by
  unfold lexReal
  rw [if_pos (by simp; exact h), extensionOf_qLifted_some_some_card]
  norm_num

private theorem lexReal_qLifted_all_s3 :
    lexReal (liftMeaning qMeaning) (some QUtt.all) .s3 = 1 := by
  unfold lexReal
  rw [if_pos (by decide), extensionOf_qLifted_all_card]
  norm_num

private theorem lexReal_qLifted_silent (s : WorldState) :
    lexReal (liftMeaning qMeaning) none s = 1/4 := by
  unfold lexReal
  rw [if_pos (RSA.liftMeaning_none qMeaning s), extensionOf_qLifted_silent_card]
  norm_num

/-! Lex evaluations for the silence-extended LB numeral model.
- `some NumUtt.one`: extension = `{.s1, .s2, .s3}`, card = 3, lex (s ≥ 1) = 1/3.
- `some NumUtt.two`: extension = `{.s2, .s3}`, card = 2, lex (s ≥ 2) = 1/2.
- `some NumUtt.three`: extension = `{.s3}`, card = 1, lex .s3 = 1.
- `none` (silence): extension = `{.s0, .s1, .s2, .s3}`, card = 4, lex = 1/4. -/

private theorem extensionOf_lbLifted_one_card :
    (RSA.extensionOf (liftMeaning lbMeaning) (some NumUtt.one)).card = 3 := by decide

private theorem extensionOf_lbLifted_two_card :
    (RSA.extensionOf (liftMeaning lbMeaning) (some NumUtt.two)).card = 2 := by decide

private theorem extensionOf_lbLifted_three_card :
    (RSA.extensionOf (liftMeaning lbMeaning) (some NumUtt.three)).card = 1 := by decide

private theorem extensionOf_lbLifted_silent_card :
    (RSA.extensionOf (liftMeaning lbMeaning) (none : WithSilence NumUtt)).card = 4 := by decide

private theorem lexReal_lbLifted_one (s : WorldState)
    (h : lbMeaning .one s = true) :
    lexReal (liftMeaning lbMeaning) (some NumUtt.one) s = 1/3 := by
  unfold lexReal
  rw [if_pos (by simp; exact h), extensionOf_lbLifted_one_card]
  norm_num

private theorem lexReal_lbLifted_two (s : WorldState)
    (h : lbMeaning .two s = true) :
    lexReal (liftMeaning lbMeaning) (some NumUtt.two) s = 1/2 := by
  unfold lexReal
  rw [if_pos (by simp; exact h), extensionOf_lbLifted_two_card]
  norm_num

private theorem lexReal_lbLifted_three_s3 :
    lexReal (liftMeaning lbMeaning) (some NumUtt.three) .s3 = 1 := by
  unfold lexReal
  rw [if_pos (by decide), extensionOf_lbLifted_three_card]
  norm_num

private theorem lexReal_lbLifted_silent (s : WorldState) :
    lexReal (liftMeaning lbMeaning) none s = 1/4 := by
  rw [show (none : WithSilence NumUtt) = (none : Option NumUtt) from rfl]
  unfold lexReal
  rw [if_pos (RSA.liftMeaning_none lbMeaning s), extensionOf_lbLifted_silent_card]
  norm_num

/-! ## §10.4. Per-(obs, utterance) `s1Score` evaluations at `.a3` obs

Each `s1Score (liftMeaning m) 1 obs u` evaluates to either
`ENNReal.ofReal v` (where `v` is the literal lex value at the obs's belief
support) or `0` (when `qualityOk` fails). These helpers are the building
blocks for the sum-of-scores helpers in §10.5.

Naming: `s1Score_{model}Lifted_{obs}_{utt}` where `model ∈ {q, lb}`,
`obs ∈ {o0a3, o1a3, o2a3, o3a3}`, `utt` is the utterance name. -/

-- QUtt evaluations at `.o2a3` (belief pure on `.s2`)
private theorem s1Score_qLifted_o2a3_silent :
    s1Score (liftMeaning qMeaning) 1 .o2a3 (none : WithSilence QUtt) =
      ENNReal.ofReal (1/4 : ℝ) := by
  rw [s1Score_liftMeaning_o2a3_apply _ _ (fun _ => by
        rw [lexReal_qLifted_silent]; norm_num),
      if_pos (by simp [qualityOk]), lexReal_qLifted_silent]

private theorem s1Score_qLifted_o2a3_none :
    s1Score (liftMeaning qMeaning) 1 .o2a3 (some QUtt.none_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_o2a3_some :
    s1Score (liftMeaning qMeaning) 1 .o2a3 (some QUtt.some_) =
      ENNReal.ofReal (1/3 : ℝ) := by
  rw [s1Score_liftMeaning_o2a3_apply _ _ (fun _ => by
        rw [lexReal_qLifted_some_some _ (by decide)]; norm_num),
      if_pos (by decide), lexReal_qLifted_some_some _ (by decide)]

private theorem s1Score_qLifted_o2a3_all :
    s1Score (liftMeaning qMeaning) 1 .o2a3 (some QUtt.all) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

-- QUtt evaluations at `.o3a3` (belief pure on `.s3`)
private theorem s1Score_qLifted_o3a3_silent :
    s1Score (liftMeaning qMeaning) 1 .o3a3 (none : WithSilence QUtt) =
      ENNReal.ofReal (1/4 : ℝ) := by
  rw [s1Score_liftMeaning_o3a3_apply _ _ (fun _ => by
        rw [lexReal_qLifted_silent]; norm_num),
      if_pos (by simp [qualityOk]), lexReal_qLifted_silent]

private theorem s1Score_qLifted_o3a3_none :
    s1Score (liftMeaning qMeaning) 1 .o3a3 (some QUtt.none_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_o3a3_some :
    s1Score (liftMeaning qMeaning) 1 .o3a3 (some QUtt.some_) =
      ENNReal.ofReal (1/3 : ℝ) := by
  rw [s1Score_liftMeaning_o3a3_apply _ _ (fun _ => by
        rw [lexReal_qLifted_some_some _ (by decide)]; norm_num),
      if_pos (by decide), lexReal_qLifted_some_some _ (by decide)]

private theorem s1Score_qLifted_o3a3_all :
    s1Score (liftMeaning qMeaning) 1 .o3a3 (some QUtt.all) =
      ENNReal.ofReal (1 : ℝ) := by
  rw [s1Score_liftMeaning_o3a3_apply _ _ (fun _ => by
        rw [lexReal_qLifted_all_s3]; norm_num),
      if_pos (by decide), lexReal_qLifted_all_s3]

-- NumUtt evaluations at `.o0a3` (belief pure on `.s0`)
-- All numerals fail qOk because they are false at `.s0`.
private theorem s1Score_lbLifted_o0a3_silent :
    s1Score (liftMeaning lbMeaning) 1 .o0a3 (none : WithSilence NumUtt) =
      ENNReal.ofReal (1/4 : ℝ) := by
  rw [s1Score_liftMeaning_o0a3_apply _ _ (fun _ => by
        rw [lexReal_lbLifted_silent]; norm_num),
      if_pos (by simp [qualityOk]), lexReal_lbLifted_silent]

private theorem s1Score_lbLifted_o0a3_one :
    s1Score (liftMeaning lbMeaning) 1 .o0a3 (some NumUtt.one) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_o0a3_two :
    s1Score (liftMeaning lbMeaning) 1 .o0a3 (some NumUtt.two) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_o0a3_three :
    s1Score (liftMeaning lbMeaning) 1 .o0a3 (some NumUtt.three) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

-- NumUtt evaluations at `.o1a3` (belief pure on `.s1`)
private theorem s1Score_lbLifted_o1a3_silent :
    s1Score (liftMeaning lbMeaning) 1 .o1a3 (none : WithSilence NumUtt) =
      ENNReal.ofReal (1/4 : ℝ) := by
  rw [s1Score_liftMeaning_o1a3_apply _ _ (fun _ => by
        rw [lexReal_lbLifted_silent]; norm_num),
      if_pos (by simp [qualityOk]), lexReal_lbLifted_silent]

private theorem s1Score_lbLifted_o1a3_one :
    s1Score (liftMeaning lbMeaning) 1 .o1a3 (some NumUtt.one) =
      ENNReal.ofReal (1/3 : ℝ) := by
  rw [s1Score_liftMeaning_o1a3_apply _ _ (fun _ => by
        rw [lexReal_lbLifted_one _ (by decide)]; norm_num),
      if_pos (by decide), lexReal_lbLifted_one _ (by decide)]

private theorem s1Score_lbLifted_o1a3_two :
    s1Score (liftMeaning lbMeaning) 1 .o1a3 (some NumUtt.two) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_o1a3_three :
    s1Score (liftMeaning lbMeaning) 1 .o1a3 (some NumUtt.three) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

-- NumUtt evaluations at `.o2a3` (belief pure on `.s2`)
private theorem s1Score_lbLifted_o2a3_silent :
    s1Score (liftMeaning lbMeaning) 1 .o2a3 (none : WithSilence NumUtt) =
      ENNReal.ofReal (1/4 : ℝ) := by
  rw [s1Score_liftMeaning_o2a3_apply _ _ (fun _ => by
        rw [lexReal_lbLifted_silent]; norm_num),
      if_pos (by simp [qualityOk]), lexReal_lbLifted_silent]

private theorem s1Score_lbLifted_o2a3_one :
    s1Score (liftMeaning lbMeaning) 1 .o2a3 (some NumUtt.one) =
      ENNReal.ofReal (1/3 : ℝ) := by
  rw [s1Score_liftMeaning_o2a3_apply _ _ (fun _ => by
        rw [lexReal_lbLifted_one _ (by decide)]; norm_num),
      if_pos (by decide), lexReal_lbLifted_one _ (by decide)]

private theorem s1Score_lbLifted_o2a3_two :
    s1Score (liftMeaning lbMeaning) 1 .o2a3 (some NumUtt.two) =
      ENNReal.ofReal (1/2 : ℝ) := by
  rw [s1Score_liftMeaning_o2a3_apply _ _ (fun _ => by
        rw [lexReal_lbLifted_two _ (by decide)]; norm_num),
      if_pos (by decide), lexReal_lbLifted_two _ (by decide)]

private theorem s1Score_lbLifted_o2a3_three :
    s1Score (liftMeaning lbMeaning) 1 .o2a3 (some NumUtt.three) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

-- NumUtt evaluations at `.o3a3` (belief pure on `.s3`)
private theorem s1Score_lbLifted_o3a3_silent :
    s1Score (liftMeaning lbMeaning) 1 .o3a3 (none : WithSilence NumUtt) =
      ENNReal.ofReal (1/4 : ℝ) := by
  rw [s1Score_liftMeaning_o3a3_apply _ _ (fun _ => by
        rw [lexReal_lbLifted_silent]; norm_num),
      if_pos (by simp [qualityOk]), lexReal_lbLifted_silent]

private theorem s1Score_lbLifted_o3a3_one :
    s1Score (liftMeaning lbMeaning) 1 .o3a3 (some NumUtt.one) =
      ENNReal.ofReal (1/3 : ℝ) := by
  rw [s1Score_liftMeaning_o3a3_apply _ _ (fun _ => by
        rw [lexReal_lbLifted_one _ (by decide)]; norm_num),
      if_pos (by decide), lexReal_lbLifted_one _ (by decide)]

private theorem s1Score_lbLifted_o3a3_two :
    s1Score (liftMeaning lbMeaning) 1 .o3a3 (some NumUtt.two) =
      ENNReal.ofReal (1/2 : ℝ) := by
  rw [s1Score_liftMeaning_o3a3_apply _ _ (fun _ => by
        rw [lexReal_lbLifted_two _ (by decide)]; norm_num),
      if_pos (by decide), lexReal_lbLifted_two _ (by decide)]

private theorem s1Score_lbLifted_o3a3_three :
    s1Score (liftMeaning lbMeaning) 1 .o3a3 (some NumUtt.three) =
      ENNReal.ofReal (1 : ℝ) := by
  rw [s1Score_liftMeaning_o3a3_apply _ _ (fun _ => by
        rw [lexReal_lbLifted_three_s3]; norm_num),
      if_pos (by decide), lexReal_lbLifted_three_s3]

/-! ## §10.5. Sum-of-scores at each `.a3` obs

These collapse `∑ u, s1Score ... obs u` to a closed-form `ENNReal.ofReal v`,
where `v` is the sum of per-utterance lex values (with qOk-failing utterances
contributing 0). They feed `PMF.normalize_lt_of_apply_eq_of_sum_lt` directly. -/

private theorem sum_s1Score_qLifted_o2a3 :
    (∑ u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .o2a3 u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  show s1Score (liftMeaning qMeaning) 1 .o2a3 none +
        (s1Score (liftMeaning qMeaning) 1 .o2a3 (some QUtt.none_) +
          (s1Score (liftMeaning qMeaning) 1 .o2a3 (some QUtt.some_) +
            (s1Score (liftMeaning qMeaning) 1 .o2a3 (some QUtt.all) + 0))) = _
  rw [s1Score_qLifted_o2a3_silent, s1Score_qLifted_o2a3_none,
      s1Score_qLifted_o2a3_some, s1Score_qLifted_o2a3_all]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_qLifted_o3a3 :
    (∑ u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .o3a3 u) =
      ENNReal.ofReal (19/12 : ℝ) := by
  show s1Score (liftMeaning qMeaning) 1 .o3a3 none +
        (s1Score (liftMeaning qMeaning) 1 .o3a3 (some QUtt.none_) +
          (s1Score (liftMeaning qMeaning) 1 .o3a3 (some QUtt.some_) +
            (s1Score (liftMeaning qMeaning) 1 .o3a3 (some QUtt.all) + 0))) = _
  rw [s1Score_qLifted_o3a3_silent, s1Score_qLifted_o3a3_none,
      s1Score_qLifted_o3a3_some, s1Score_qLifted_o3a3_all]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_lbLifted_o0a3 :
    (∑ u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .o0a3 u) =
      ENNReal.ofReal (1/4 : ℝ) := by
  show s1Score (liftMeaning lbMeaning) 1 .o0a3 none +
        (s1Score (liftMeaning lbMeaning) 1 .o0a3 (some NumUtt.one) +
          (s1Score (liftMeaning lbMeaning) 1 .o0a3 (some NumUtt.two) +
            (s1Score (liftMeaning lbMeaning) 1 .o0a3 (some NumUtt.three) + 0))) = _
  rw [s1Score_lbLifted_o0a3_silent, s1Score_lbLifted_o0a3_one,
      s1Score_lbLifted_o0a3_two, s1Score_lbLifted_o0a3_three]
  simp only [add_zero, zero_add]

private theorem sum_s1Score_lbLifted_o1a3 :
    (∑ u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .o1a3 u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  show s1Score (liftMeaning lbMeaning) 1 .o1a3 none +
        (s1Score (liftMeaning lbMeaning) 1 .o1a3 (some NumUtt.one) +
          (s1Score (liftMeaning lbMeaning) 1 .o1a3 (some NumUtt.two) +
            (s1Score (liftMeaning lbMeaning) 1 .o1a3 (some NumUtt.three) + 0))) = _
  rw [s1Score_lbLifted_o1a3_silent, s1Score_lbLifted_o1a3_one,
      s1Score_lbLifted_o1a3_two, s1Score_lbLifted_o1a3_three]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_lbLifted_o2a3 :
    (∑ u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .o2a3 u) =
      ENNReal.ofReal (13/12 : ℝ) := by
  show s1Score (liftMeaning lbMeaning) 1 .o2a3 none +
        (s1Score (liftMeaning lbMeaning) 1 .o2a3 (some NumUtt.one) +
          (s1Score (liftMeaning lbMeaning) 1 .o2a3 (some NumUtt.two) +
            (s1Score (liftMeaning lbMeaning) 1 .o2a3 (some NumUtt.three) + 0))) = _
  rw [s1Score_lbLifted_o2a3_silent, s1Score_lbLifted_o2a3_one,
      s1Score_lbLifted_o2a3_two, s1Score_lbLifted_o2a3_three]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_lbLifted_o3a3 :
    (∑ u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .o3a3 u) =
      ENNReal.ofReal (25/12 : ℝ) := by
  show s1Score (liftMeaning lbMeaning) 1 .o3a3 none +
        (s1Score (liftMeaning lbMeaning) 1 .o3a3 (some NumUtt.one) +
          (s1Score (liftMeaning lbMeaning) 1 .o3a3 (some NumUtt.two) +
            (s1Score (liftMeaning lbMeaning) 1 .o3a3 (some NumUtt.three) + 0))) = _
  rw [s1Score_lbLifted_o3a3_silent, s1Score_lbLifted_o3a3_one,
      s1Score_lbLifted_o3a3_two, s1Score_lbLifted_o3a3_three]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

/-! ## §10.6. `.a1` substrate — non-concentrated obs kernel

At minimal access `.a1`, the obs kernel reaches `{.o0a1, .o1a1}`. For
extreme worlds (s0, s3) it concentrates on one obs; for middle worlds
(s1, s2) it splits. The concentrated cases reuse the `_eq_pure` /
`marginalSpeaker_a*_apply` pattern from §10.1; the split cases need a
two-obs `bindOnSupport` expansion. -/

private theorem obsKernel_a1_s0_eq_pure : obsKernel .a1 .s0 = PMF.pure .o0a1 := by
  apply PMF.normalize_eq_pure_of_singleton_support
  intro y hy
  cases y <;>
    first
      | exact absurd rfl hy
      | (unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat; simp)

private theorem obsKernel_a1_s3_eq_pure : obsKernel .a1 .s3 = PMF.pure .o1a1 := by
  apply PMF.normalize_eq_pure_of_singleton_support
  intro y hy
  cases y <;>
    first
      | exact absurd rfl hy
      | (unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat; simp)

/-- For middle worlds at `.a1`, `obsKernelRaw` is non-zero on both `.o0a1`
and `.o1a1`. The Vandermonde-like row sum: `(3 - K) + K = 3`. -/
private theorem obsKernelRaw_a1_tsum (w : WorldState) :
    (∑' obs : Obs, obsKernelRaw .a1 w obs) = (3 : ℝ≥0∞) := by
  rw [tsum_fintype]
  cases w <;>
    (show obsKernelRaw .a1 _ .o0a1 + (obsKernelRaw .a1 _ .o1a1 +
            (obsKernelRaw .a1 _ .o0a2 + (obsKernelRaw .a1 _ .o1a2 +
              (obsKernelRaw .a1 _ .o2a2 + (obsKernelRaw .a1 _ .o0a3 +
                (obsKernelRaw .a1 _ .o1a3 + (obsKernelRaw .a1 _ .o2a3 +
                  (obsKernelRaw .a1 _ .o3a3 + 0)))))))) = _
     unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat
     simp only [show ¬ Access.a2 = Access.a1 from by decide,
                show ¬ Access.a3 = Access.a1 from by decide,
                if_false, if_true]
     norm_num)

/-- `obsKernel .a1 .s1` is `2/3` on `.o0a1` and `1/3` on `.o1a1`. -/
private theorem obsKernel_a1_s1_o0a1 :
    obsKernel .a1 .s1 .o0a1 = ENNReal.ofReal (2/3 : ℝ) := by
  rw [obsKernel, PMF.normalize_apply, obsKernelRaw_a1_tsum]
  show ((2 : ℕ) : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ = _
  rw [show ((2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 from by simp,
      show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
      ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
  rfl

private theorem obsKernel_a1_s1_o1a1 :
    obsKernel .a1 .s1 .o1a1 = ENNReal.ofReal (1/3 : ℝ) := by
  rw [obsKernel, PMF.normalize_apply, obsKernelRaw_a1_tsum]
  show ((1 : ℕ) : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ = _
  rw [show ((1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 1 from by simp,
      show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
      ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
  rfl

private theorem obsKernel_a1_s2_o0a1 :
    obsKernel .a1 .s2 .o0a1 = ENNReal.ofReal (1/3 : ℝ) := by
  rw [obsKernel, PMF.normalize_apply, obsKernelRaw_a1_tsum]
  show ((1 : ℕ) : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ = _
  rw [show ((1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 1 from by simp,
      show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
      ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
  rfl

private theorem obsKernel_a1_s2_o1a1 :
    obsKernel .a1 .s2 .o1a1 = ENNReal.ofReal (2/3 : ℝ) := by
  rw [obsKernel, PMF.normalize_apply, obsKernelRaw_a1_tsum]
  show ((2 : ℕ) : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ = _
  rw [show ((2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 from by simp,
      show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
      ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
  rfl

/-! ### Off-obs zero values for `.a1` extreme worlds.

At `.s0` only `.o0a1` is reachable; at `.s3` only `.o1a1` is reachable.
Mirrors `obsKernel_a3_*_apply_off`. -/

private theorem obsKernel_a1_s0_apply_off {b : Obs} (h : b ≠ .o0a1) :
    obsKernel .a1 .s0 b = 0 := by
  rw [PMF.apply_eq_zero_iff]
  rw [obsKernel_a1_s0_eq_pure, PMF.support_pure]
  simp [h]

private theorem obsKernel_a1_s3_apply_off {b : Obs} (h : b ≠ .o1a1) :
    obsKernel .a1 .s3 b = 0 := by
  rw [PMF.apply_eq_zero_iff]
  rw [obsKernel_a1_s3_eq_pure, PMF.support_pure]
  simp [h]

/-- `obsKernel .a1 .s0 .o0a1 = 1` (extreme-world diagonal). -/
private theorem obsKernel_a1_s0_apply_diag : obsKernel .a1 .s0 .o0a1 = 1 := by
  rw [obsKernel_a1_s0_eq_pure, PMF.pure_apply, if_pos rfl]

/-- `obsKernel .a1 .s3 .o1a1 = 1` (extreme-world diagonal). -/
private theorem obsKernel_a1_s3_apply_diag : obsKernel .a1 .s3 .o1a1 = 1 := by
  rw [obsKernel_a1_s3_eq_pure, PMF.pure_apply, if_pos rfl]

/-! ### Off-obs zero values for `.a1` middle worlds.

For `.s1` and `.s2`, `obsKernelRaw .a1 _ b = 0` for any `b` whose access ≠ a1. -/

private theorem obsKernelRaw_a1_off_a1 {w : WorldState} {b : Obs} (h : b.access ≠ .a1) :
    obsKernelRaw .a1 w b = 0 := by
  unfold obsKernelRaw
  rw [if_neg h]

private theorem obsKernel_a1_s1_apply_off {b : Obs}
    (h0 : b ≠ .o0a1) (h1 : b ≠ .o1a1) : obsKernel .a1 .s1 b = 0 := by
  apply obsKernel_apply_zero_of_raw_zero
  cases b
  · exact absurd rfl h0
  · exact absurd rfl h1
  all_goals (refine obsKernelRaw_a1_off_a1 ?_; decide)

private theorem obsKernel_a1_s2_apply_off {b : Obs}
    (h0 : b ≠ .o0a1) (h1 : b ≠ .o1a1) : obsKernel .a1 .s2 b = 0 := by
  apply obsKernel_apply_zero_of_raw_zero
  cases b
  · exact absurd rfl h0
  · exact absurd rfl h1
  all_goals (refine obsKernelRaw_a1_off_a1 ?_; decide)

/-! ### `marginalSpeaker` collapse for `.a1` extreme worlds.

At `.s0` collapses to `S1g` at `.o0a1`; at `.s3` collapses to `S1g` at `.o1a1`. -/

private theorem marginalSpeaker_a1_s0_apply
    {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool)
    (hCov : ∀ obs ∈ (obsKernel .a1 .s0).support, ∃ u : U, qualityOk meaning obs u)
    (u : U) :
    marginalSpeaker meaning 1 .a1 .s0 hCov u =
      S1g meaning 1 .o0a1
        (RSA.softmaxBelief_tsum_ne_zero_of_witness
          (hCov .o0a1 (by rw [obsKernel_a1_s0_eq_pure]; simp)).choose_spec) u := by
  unfold marginalSpeaker
  rw [PMF.bindOnSupport_apply, tsum_eq_single Obs.o0a1]
  · have h_ne : obsKernel .a1 .s0 Obs.o0a1 ≠ 0 := by
      rw [obsKernel_a1_s0_apply_diag]; norm_num
    rw [dif_neg h_ne, obsKernel_a1_s0_apply_diag, one_mul]
  · intro b hb
    exact mul_eq_zero.mpr (Or.inl (obsKernel_a1_s0_apply_off hb))

private theorem marginalSpeaker_a1_s3_apply
    {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool)
    (hCov : ∀ obs ∈ (obsKernel .a1 .s3).support, ∃ u : U, qualityOk meaning obs u)
    (u : U) :
    marginalSpeaker meaning 1 .a1 .s3 hCov u =
      S1g meaning 1 .o1a1
        (RSA.softmaxBelief_tsum_ne_zero_of_witness
          (hCov .o1a1 (by rw [obsKernel_a1_s3_eq_pure]; simp)).choose_spec) u := by
  unfold marginalSpeaker
  rw [PMF.bindOnSupport_apply, tsum_eq_single Obs.o1a1]
  · have h_ne : obsKernel .a1 .s3 Obs.o1a1 ≠ 0 := by
      rw [obsKernel_a1_s3_apply_diag]; norm_num
    rw [dif_neg h_ne, obsKernel_a1_s3_apply_diag, one_mul]
  · intro b hb
    exact mul_eq_zero.mpr (Or.inl (obsKernel_a1_s3_apply_off hb))

/-! ### `speakerBelief` at `.o0a1` and `.o1a1` (non-concentrated).

Belief at `.o0a1` is supported on `{.s0, .s1, .s2}` with weights 1/2, 1/3, 1/6.
Belief at `.o1a1` is supported on `{.s1, .s2, .s3}` with weights 1/6, 1/3, 1/2.
The marginal in both cases is 1/2 (from worldPrior 1/4 × hypergeometric Σ = 2). -/

/-- For obs `.o0a1`: marginal across the 4 worlds is 1/2 = (1/4)·1 + (1/4)·(2/3) + (1/4)·(1/3) + 0. -/
private theorem marginal_obsKernel_o0a1 :
    PMF.marginal (obsKernel .a1) worldPrior .o0a1 = ENNReal.ofReal (1/2 : ℝ) := by
  unfold PMF.marginal
  rw [tsum_fintype]
  show worldPrior .s0 * obsKernel .a1 .s0 .o0a1 +
        (worldPrior .s1 * obsKernel .a1 .s1 .o0a1 +
          (worldPrior .s2 * obsKernel .a1 .s2 .o0a1 +
            (worldPrior .s3 * obsKernel .a1 .s3 .o0a1 + 0))) = _
  rw [obsKernel_a1_s0_apply_diag, obsKernel_a1_s1_o0a1, obsKernel_a1_s2_o0a1,
      obsKernel_a1_s3_apply_off (by decide), worldPrior_apply, worldPrior_apply,
      worldPrior_apply, worldPrior_apply,
      mul_zero, add_zero, add_zero,
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/4),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/4),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/4)]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem marginal_obsKernel_o1a1 :
    PMF.marginal (obsKernel .a1) worldPrior .o1a1 = ENNReal.ofReal (1/2 : ℝ) := by
  unfold PMF.marginal
  rw [tsum_fintype]
  show worldPrior .s0 * obsKernel .a1 .s0 .o1a1 +
        (worldPrior .s1 * obsKernel .a1 .s1 .o1a1 +
          (worldPrior .s2 * obsKernel .a1 .s2 .o1a1 +
            (worldPrior .s3 * obsKernel .a1 .s3 .o1a1 + 0))) = _
  rw [obsKernel_a1_s0_apply_off (by decide), obsKernel_a1_s1_o1a1, obsKernel_a1_s2_o1a1,
      obsKernel_a1_s3_apply_diag, worldPrior_apply, worldPrior_apply,
      worldPrior_apply, worldPrior_apply,
      mul_zero, zero_add, add_zero,
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/4),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/4),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/4)]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem speakerBelief_o0a1_apply (s : WorldState) :
    speakerBelief .o0a1 s = ENNReal.ofReal (
      match s with | .s0 => 1/2 | .s1 => 1/3 | .s2 => 1/6 | .s3 => 0) := by
  unfold speakerBelief
  rw [PMF.posterior_apply]
  show worldPrior s * obsKernel .a1 s .o0a1 *
        (PMF.marginal (obsKernel .a1) worldPrior .o0a1)⁻¹ = _
  rw [worldPrior_apply, marginal_obsKernel_o0a1,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  cases s
  · rw [obsKernel_a1_s0_apply_diag,
        show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp,
        ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; norm_num
  · rw [obsKernel_a1_s1_o0a1,
        ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; norm_num
  · rw [obsKernel_a1_s2_o0a1,
        ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; norm_num
  · rw [obsKernel_a1_s3_apply_off (by decide), mul_zero, zero_mul,
        show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from by simp]

private theorem speakerBelief_o1a1_apply (s : WorldState) :
    speakerBelief .o1a1 s = ENNReal.ofReal (
      match s with | .s0 => 0 | .s1 => 1/6 | .s2 => 1/3 | .s3 => 1/2) := by
  unfold speakerBelief
  rw [PMF.posterior_apply]
  show worldPrior s * obsKernel .a1 s .o1a1 *
        (PMF.marginal (obsKernel .a1) worldPrior .o1a1)⁻¹ = _
  rw [worldPrior_apply, marginal_obsKernel_o1a1,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  cases s
  · rw [obsKernel_a1_s0_apply_off (by decide), mul_zero, zero_mul,
        show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from by simp]
  · rw [obsKernel_a1_s1_o1a1,
        ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; norm_num
  · rw [obsKernel_a1_s2_o1a1,
        ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; norm_num
  · rw [obsKernel_a1_s3_apply_diag,
        show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp,
        ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; norm_num

private theorem beliefReal_o0a1 (s : WorldState) :
    beliefReal .o0a1 s =
      match s with | .s0 => 1/2 | .s1 => 1/3 | .s2 => 1/6 | .s3 => 0 := by
  unfold beliefReal
  rw [speakerBelief_o0a1_apply]
  cases s <;> (rw [ENNReal.toReal_ofReal (by norm_num)])

private theorem beliefReal_o1a1 (s : WorldState) :
    beliefReal .o1a1 s =
      match s with | .s0 => 0 | .s1 => 1/6 | .s2 => 1/3 | .s3 => 1/2 := by
  unfold beliefReal
  rw [speakerBelief_o1a1_apply]
  cases s <;> (rw [ENNReal.toReal_ofReal (by norm_num)])

private theorem beliefReal_o0a1_sum :
    (∑ s : WorldState, beliefReal .o0a1 s) = 1 := by
  show beliefReal .o0a1 .s0 + (beliefReal .o0a1 .s1 +
        (beliefReal .o0a1 .s2 + (beliefReal .o0a1 .s3 + 0))) = _
  rw [beliefReal_o0a1, beliefReal_o0a1, beliefReal_o0a1, beliefReal_o0a1]
  norm_num

private theorem beliefReal_o1a1_sum :
    (∑ s : WorldState, beliefReal .o1a1 s) = 1 := by
  show beliefReal .o1a1 .s0 + (beliefReal .o1a1 .s1 +
        (beliefReal .o1a1 .s2 + (beliefReal .o1a1 .s3 + 0))) = _
  rw [beliefReal_o1a1, beliefReal_o1a1, beliefReal_o1a1, beliefReal_o1a1]
  norm_num

/-! ### `s1Score` at `.o0a1` (compatible worlds {s0, s1, s2}).

For both quantifier and lower-bound numeral models: silence is the only `qOk`-passing
utterance. The other utterances all fail because they are false at `.s0` (which has
positive belief mass). For silence, `softmaxBelief_uniform_on_support` gives `1/4`. -/

private theorem s1Score_qLifted_o0a1_silent :
    s1Score (liftMeaning qMeaning) 1 .o0a1 (none : WithSilence QUtt) =
      ENNReal.ofReal (1/4 : ℝ) := by
  show RSA.softmaxBelief (lexReal (liftMeaning qMeaning)) (beliefReal .o0a1) 1
        (fun u' => qualityOk (liftMeaning qMeaning) .o0a1 u') none = _
  refine RSA.softmaxBelief_uniform_on_support _ _ _ _ (1/4 : ℝ) ?_ ?_ ?_ beliefReal_o0a1_sum
  · simp [qualityOk]
  · intro s _; rw [lexReal_qLifted_silent]
  · norm_num

private theorem s1Score_qLifted_o0a1_none :
    s1Score (liftMeaning qMeaning) 1 .o0a1 (some QUtt.none_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_o0a1_some :
    s1Score (liftMeaning qMeaning) 1 .o0a1 (some QUtt.some_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_o0a1_all :
    s1Score (liftMeaning qMeaning) 1 .o0a1 (some QUtt.all) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_o0a1_silent :
    s1Score (liftMeaning lbMeaning) 1 .o0a1 (none : WithSilence NumUtt) =
      ENNReal.ofReal (1/4 : ℝ) := by
  show RSA.softmaxBelief (lexReal (liftMeaning lbMeaning)) (beliefReal .o0a1) 1
        (fun u' => qualityOk (liftMeaning lbMeaning) .o0a1 u') none = _
  refine RSA.softmaxBelief_uniform_on_support _ _ _ _ (1/4 : ℝ) ?_ ?_ ?_ beliefReal_o0a1_sum
  · simp [qualityOk]
  · intro s _; rw [lexReal_lbLifted_silent]
  · norm_num

private theorem s1Score_lbLifted_o0a1_one :
    s1Score (liftMeaning lbMeaning) 1 .o0a1 (some NumUtt.one) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_o0a1_two :
    s1Score (liftMeaning lbMeaning) 1 .o0a1 (some NumUtt.two) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_o0a1_three :
    s1Score (liftMeaning lbMeaning) 1 .o0a1 (some NumUtt.three) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

/-! ### `s1Score` at `.o1a1` (compatible worlds {s1, s2, s3}).

Belief at `.o1a1` is supported on `{.s1, .s2, .s3}` with weights 1/6, 1/3, 1/2.
- For silence: lex = 1/4 always; sum to 1; result 1/4.
- For `.some_` and `.one`: lex = 1/3 on each of {s1, s2, s3}; uniform on belief
  support; result 1/3.
- For `.none_`, `.all`, `.two`, `.three`: false at some belief-support world; qOk
  fails; result 0. -/

private theorem s1Score_qLifted_o1a1_silent :
    s1Score (liftMeaning qMeaning) 1 .o1a1 (none : WithSilence QUtt) =
      ENNReal.ofReal (1/4 : ℝ) := by
  show RSA.softmaxBelief (lexReal (liftMeaning qMeaning)) (beliefReal .o1a1) 1
        (fun u' => qualityOk (liftMeaning qMeaning) .o1a1 u') none = _
  refine RSA.softmaxBelief_uniform_on_support _ _ _ _ (1/4 : ℝ) ?_ ?_ ?_ beliefReal_o1a1_sum
  · simp [qualityOk]
  · intro s _; rw [lexReal_qLifted_silent]
  · norm_num

private theorem s1Score_qLifted_o1a1_none :
    s1Score (liftMeaning qMeaning) 1 .o1a1 (some QUtt.none_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_o1a1_some :
    s1Score (liftMeaning qMeaning) 1 .o1a1 (some QUtt.some_) =
      ENNReal.ofReal (1/3 : ℝ) := by
  show RSA.softmaxBelief (lexReal (liftMeaning qMeaning)) (beliefReal .o1a1) 1
        (fun u' => qualityOk (liftMeaning qMeaning) .o1a1 u') (some QUtt.some_) = _
  refine RSA.softmaxBelief_uniform_on_support _ _ _ _ (1/3 : ℝ) ?_ ?_ ?_ beliefReal_o1a1_sum
  · decide
  · intro s hs
    -- belief at s ≠ 0 means s ∈ {s1, s2, s3}. lexReal qMeaning .some_ s = 1/3.
    cases s
    · exact absurd (by rw [beliefReal_o1a1] : beliefReal .o1a1 .s0 = 0) hs
    · exact lexReal_qLifted_some_some _ (by decide)
    · exact lexReal_qLifted_some_some _ (by decide)
    · exact lexReal_qLifted_some_some _ (by decide)
  · norm_num

private theorem s1Score_qLifted_o1a1_all :
    s1Score (liftMeaning qMeaning) 1 .o1a1 (some QUtt.all) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_o1a1_silent :
    s1Score (liftMeaning lbMeaning) 1 .o1a1 (none : WithSilence NumUtt) =
      ENNReal.ofReal (1/4 : ℝ) := by
  show RSA.softmaxBelief (lexReal (liftMeaning lbMeaning)) (beliefReal .o1a1) 1
        (fun u' => qualityOk (liftMeaning lbMeaning) .o1a1 u') none = _
  refine RSA.softmaxBelief_uniform_on_support _ _ _ _ (1/4 : ℝ) ?_ ?_ ?_ beliefReal_o1a1_sum
  · simp [qualityOk]
  · intro s _; rw [lexReal_lbLifted_silent]
  · norm_num

private theorem s1Score_lbLifted_o1a1_one :
    s1Score (liftMeaning lbMeaning) 1 .o1a1 (some NumUtt.one) =
      ENNReal.ofReal (1/3 : ℝ) := by
  show RSA.softmaxBelief (lexReal (liftMeaning lbMeaning)) (beliefReal .o1a1) 1
        (fun u' => qualityOk (liftMeaning lbMeaning) .o1a1 u') (some NumUtt.one) = _
  refine RSA.softmaxBelief_uniform_on_support _ _ _ _ (1/3 : ℝ) ?_ ?_ ?_ beliefReal_o1a1_sum
  · decide
  · intro s hs
    cases s
    · exact absurd (by rw [beliefReal_o1a1] : beliefReal .o1a1 .s0 = 0) hs
    · exact lexReal_lbLifted_one _ (by decide)
    · exact lexReal_lbLifted_one _ (by decide)
    · exact lexReal_lbLifted_one _ (by decide)
  · norm_num

private theorem s1Score_lbLifted_o1a1_two :
    s1Score (liftMeaning lbMeaning) 1 .o1a1 (some NumUtt.two) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_o1a1_three :
    s1Score (liftMeaning lbMeaning) 1 .o1a1 (some NumUtt.three) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

/-! ### Sum of `s1Score` at `.o0a1` and `.o1a1`. -/

private theorem sum_s1Score_qLifted_o0a1 :
    (∑ u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .o0a1 u) =
      ENNReal.ofReal (1/4 : ℝ) := by
  show s1Score (liftMeaning qMeaning) 1 .o0a1 none +
        (s1Score (liftMeaning qMeaning) 1 .o0a1 (some QUtt.none_) +
          (s1Score (liftMeaning qMeaning) 1 .o0a1 (some QUtt.some_) +
            (s1Score (liftMeaning qMeaning) 1 .o0a1 (some QUtt.all) + 0))) = _
  rw [s1Score_qLifted_o0a1_silent, s1Score_qLifted_o0a1_none,
      s1Score_qLifted_o0a1_some, s1Score_qLifted_o0a1_all]
  simp

private theorem sum_s1Score_qLifted_o1a1 :
    (∑ u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .o1a1 u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  show s1Score (liftMeaning qMeaning) 1 .o1a1 none +
        (s1Score (liftMeaning qMeaning) 1 .o1a1 (some QUtt.none_) +
          (s1Score (liftMeaning qMeaning) 1 .o1a1 (some QUtt.some_) +
            (s1Score (liftMeaning qMeaning) 1 .o1a1 (some QUtt.all) + 0))) = _
  rw [s1Score_qLifted_o1a1_silent, s1Score_qLifted_o1a1_none,
      s1Score_qLifted_o1a1_some, s1Score_qLifted_o1a1_all]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_lbLifted_o0a1 :
    (∑ u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .o0a1 u) =
      ENNReal.ofReal (1/4 : ℝ) := by
  show s1Score (liftMeaning lbMeaning) 1 .o0a1 none +
        (s1Score (liftMeaning lbMeaning) 1 .o0a1 (some NumUtt.one) +
          (s1Score (liftMeaning lbMeaning) 1 .o0a1 (some NumUtt.two) +
            (s1Score (liftMeaning lbMeaning) 1 .o0a1 (some NumUtt.three) + 0))) = _
  rw [s1Score_lbLifted_o0a1_silent, s1Score_lbLifted_o0a1_one,
      s1Score_lbLifted_o0a1_two, s1Score_lbLifted_o0a1_three]
  simp

private theorem sum_s1Score_lbLifted_o1a1 :
    (∑ u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .o1a1 u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  show s1Score (liftMeaning lbMeaning) 1 .o1a1 none +
        (s1Score (liftMeaning lbMeaning) 1 .o1a1 (some NumUtt.one) +
          (s1Score (liftMeaning lbMeaning) 1 .o1a1 (some NumUtt.two) +
            (s1Score (liftMeaning lbMeaning) 1 .o1a1 (some NumUtt.three) + 0))) = _
  rw [s1Score_lbLifted_o1a1_silent, s1Score_lbLifted_o1a1_one,
      s1Score_lbLifted_o1a1_two, s1Score_lbLifted_o1a1_three]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

/-! ### `marginalSpeaker` at `.a1` middle worlds (`.s1`, `.s2`).

The kernel splits across `.o0a1` and `.o1a1`; `bindOnSupport` unfolds as
`obsKernel(.o0a1) * S1g(.o0a1)(u) + obsKernel(.o1a1) * S1g(.o1a1)(u)`. -/

private theorem obsKernel_a1_s1_o0a1_mem :
    Obs.o0a1 ∈ (obsKernel .a1 .s1).support := by
  rw [mem_support_obsKernel_iff]
  unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat
  simp

private theorem obsKernel_a1_s1_o1a1_mem :
    Obs.o1a1 ∈ (obsKernel .a1 .s1).support := by
  rw [mem_support_obsKernel_iff]
  unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat
  simp

private theorem obsKernel_a1_s2_o0a1_mem :
    Obs.o0a1 ∈ (obsKernel .a1 .s2).support := by
  rw [mem_support_obsKernel_iff]
  unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat
  simp

private theorem obsKernel_a1_s2_o1a1_mem :
    Obs.o1a1 ∈ (obsKernel .a1 .s2).support := by
  rw [mem_support_obsKernel_iff]
  unfold obsKernelRaw Obs.access Obs.count Obs.sampleSize WorldState.toNat
  simp

/-- The unfolded form of `marginalSpeaker .a1 .s1` as a 2-obs sum, via
`PMF.bindOnSupport_apply_two_support`. -/
private theorem marginalSpeaker_a1_s1_apply
    {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool)
    (hCov : ∀ obs ∈ (obsKernel .a1 .s1).support, ∃ u : U, qualityOk meaning obs u)
    (u : U) :
    marginalSpeaker meaning 1 .a1 .s1 hCov u =
      obsKernel .a1 .s1 .o0a1 *
        S1g meaning 1 .o0a1
          (RSA.softmaxBelief_tsum_ne_zero_of_witness
            (hCov .o0a1 obsKernel_a1_s1_o0a1_mem).choose_spec) u +
      obsKernel .a1 .s1 .o1a1 *
        S1g meaning 1 .o1a1
          (RSA.softmaxBelief_tsum_ne_zero_of_witness
            (hCov .o1a1 obsKernel_a1_s1_o1a1_mem).choose_spec) u := by
  unfold marginalSpeaker
  exact PMF.bindOnSupport_apply_two_support _ _ _ .o0a1 .o1a1 (by decide)
    (fun b hb1 hb2 => obsKernel_a1_s1_apply_off hb1 hb2)
    (by rw [obsKernel_a1_s1_o0a1]; exact ENNReal.ofReal_ne_zero_iff.mpr (by norm_num))
    (by rw [obsKernel_a1_s1_o1a1]; exact ENNReal.ofReal_ne_zero_iff.mpr (by norm_num))

/-- The unfolded form of `marginalSpeaker .a1 .s2`. Mirror of `_a1_s1_apply`. -/
private theorem marginalSpeaker_a1_s2_apply
    {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool)
    (hCov : ∀ obs ∈ (obsKernel .a1 .s2).support, ∃ u : U, qualityOk meaning obs u)
    (u : U) :
    marginalSpeaker meaning 1 .a1 .s2 hCov u =
      obsKernel .a1 .s2 .o0a1 *
        S1g meaning 1 .o0a1
          (RSA.softmaxBelief_tsum_ne_zero_of_witness
            (hCov .o0a1 obsKernel_a1_s2_o0a1_mem).choose_spec) u +
      obsKernel .a1 .s2 .o1a1 *
        S1g meaning 1 .o1a1
          (RSA.softmaxBelief_tsum_ne_zero_of_witness
            (hCov .o1a1 obsKernel_a1_s2_o1a1_mem).choose_spec) u := by
  unfold marginalSpeaker
  exact PMF.bindOnSupport_apply_two_support _ _ _ .o0a1 .o1a1 (by decide)
    (fun b hb1 hb2 => obsKernel_a1_s2_apply_off hb1 hb2)
    (by rw [obsKernel_a1_s2_o0a1]; exact ENNReal.ofReal_ne_zero_iff.mpr (by norm_num))
    (by rw [obsKernel_a1_s2_o1a1]; exact ENNReal.ofReal_ne_zero_iff.mpr (by norm_num))

/-! ## §11. Findings (silence-extended)

The 11 paper findings restated as theorems on `L1`-apply inequalities, all
formulated against the silence-extended utterance space `WithSilence U` so
that `cover_silent` discharges the `PMF.normalize` precondition without any
`(access, word) ∉ {sensible}` carve-out.

The `.a3` cases (full-access, deterministic obs kernel) reduce to a single
`S1g` evaluation via `marginalSpeaker_a3_sX_apply`; `.a1` / `.a2` cases
require expanding the `bindOnSupport` sum over multiple reachable obs.

The marginal-non-zero hypotheses (`hMarg`) are taken as parameters; they are
finite-arithmetic facts that follow from the same calculations the proof
performs but are out-of-band on the `L1` definition. -/

namespace Findings

/-! ### Silence-extended findings

All 11 paper findings restated using `WithSilence` + `liftMeaning` +
`cover_silent`. The cover hypothesis is automatically satisfiable, so
the `(access, word) ∉ {sensible}` defects (`.o0a*` for any numeral,
or `.o0a1` / `.o0a2` for any quantifier) no longer block formalization.

**Structural discharge** (post-0.230.610 template):
1. `unfold L1 worldPrior` — expose primitives
2. `rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]` (or `_le_` for
   negative findings) — cancel L1 marginal AND uniform world prior in one move
3. For `.a3` (deterministic kernel): `rw [marginalSpeaker_a3_sX_apply]` collapses
   `marginalSpeaker` to a single `S1g` evaluation, then
   `PMF.normalize_lt_of_apply_eq_of_sum_lt` reduces to a sum-of-scores comparison.
4. For `.a1` / `.a2` (non-concentrated kernel + non-concentrated belief):
   marginalSpeaker is a `bindOnSupport` sum over 2-3 obs; each S1g uses
   `softmaxBelief_uniform_on_support` (since `liftMeaning`-lex is uniform
   on the belief support whenever qOk passes). -/

/-- Finding 1 with silence-extended utterance space: at full access, `some`
favors `s2 > s3`. The "scalar implicature" is preserved because at
infeasible obs (where silence dominates) the listener already conditioned
on hearing `.some_`, not silence. -/
theorem some_full_implicature_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning qMeaning) 1 .a3 w
                          (cover_silent qMeaning .a3 w))
              worldPrior (some QUtt.some_) ≠ 0) :
    (L1 (liftMeaning qMeaning) 1 .a3 (cover_silent qMeaning .a3)
        (some QUtt.some_) hMarg) .s2 >
    (L1 (liftMeaning qMeaning) 1 .a3 (cover_silent qMeaning .a3)
        (some QUtt.some_) hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  rw [marginalSpeaker_a3_s2_apply, marginalSpeaker_a3_s3_apply]
  show (PMF.normalize (s1Score (liftMeaning qMeaning) 1 .o3a3) _ _) (some QUtt.some_) <
        (PMF.normalize (s1Score (liftMeaning qMeaning) 1 .o2a3) _ _) (some QUtt.some_)
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt
    (a := some QUtt.some_)
  · rw [s1Score_qLifted_o2a3_some, s1Score_qLifted_o3a3_some]
  · rw [s1Score_qLifted_o2a3_some]; exact (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num))
  · rw [s1Score_qLifted_o2a3_some]; exact ENNReal.ofReal_ne_top
  · rw [tsum_fintype, tsum_fintype, sum_s1Score_qLifted_o2a3, sum_s1Score_qLifted_o3a3]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- Finding 4 with silence-extended utterance space: at full access, `two`
favors `s2 > s3` (upper-bounded reading). At `.o2a3` and `.o3a3`, `.two`
gets the same lex value (1/2), but the partition function is smaller at
`.o2a3` (where `.three` fails qOk) than at `.o3a3` (where `.three` is
consistent), making `.two` more probable at `.s2`. -/
theorem two_full_upper_bounded_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a3 w
                          (cover_silent lbMeaning .a3 w))
              worldPrior (some NumUtt.two) ≠ 0) :
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.two) hMarg) .s2 >
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.two) hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  rw [marginalSpeaker_a3_s2_apply, marginalSpeaker_a3_s3_apply]
  show (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .o3a3) _ _) (some NumUtt.two) <
        (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .o2a3) _ _) (some NumUtt.two)
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt
    (a := some NumUtt.two)
  · rw [s1Score_lbLifted_o2a3_two, s1Score_lbLifted_o3a3_two]
  · rw [s1Score_lbLifted_o2a3_two]; exact (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num))
  · rw [s1Score_lbLifted_o2a3_two]; exact ENNReal.ofReal_ne_top
  · rw [tsum_fintype, tsum_fintype, sum_s1Score_lbLifted_o2a3, sum_s1Score_lbLifted_o3a3]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- Finding 6 with silence-extended utterance space: at full access, `one`
favors `s1 > s2`. At `.o1a3` and `.o2a3`, `.one` gets the same lex value
(1/3), but the partition function is smaller at `.o1a3` (where `.two` and
`.three` fail qOk) than at `.o2a3` (where `.two` is consistent). -/
theorem one_full_1v2_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a3 w
                          (cover_silent lbMeaning .a3 w))
              worldPrior (some NumUtt.one) ≠ 0) :
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.one) hMarg) .s1 >
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.one) hMarg) .s2 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  rw [marginalSpeaker_a3_s1_apply, marginalSpeaker_a3_s2_apply]
  show (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .o2a3) _ _) (some NumUtt.one) <
        (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .o1a3) _ _) (some NumUtt.one)
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt
    (a := some NumUtt.one)
  · rw [s1Score_lbLifted_o1a3_one, s1Score_lbLifted_o2a3_one]
  · rw [s1Score_lbLifted_o1a3_one]; exact (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num))
  · rw [s1Score_lbLifted_o1a3_one]; exact ENNReal.ofReal_ne_top
  · rw [tsum_fintype, tsum_fintype, sum_s1Score_lbLifted_o1a3, sum_s1Score_lbLifted_o2a3]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- Finding 7 with silence-extended utterance space: at full access, `one`
favors `s1 > s3`. The partition function gap between `.o1a3` and `.o3a3`
is the largest of the three pairings (7/12 vs 25/12). -/
theorem one_full_1v3_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a3 w
                          (cover_silent lbMeaning .a3 w))
              worldPrior (some NumUtt.one) ≠ 0) :
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.one) hMarg) .s1 >
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.one) hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  rw [marginalSpeaker_a3_s1_apply, marginalSpeaker_a3_s3_apply]
  show (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .o3a3) _ _) (some NumUtt.one) <
        (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .o1a3) _ _) (some NumUtt.one)
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt
    (a := some NumUtt.one)
  · rw [s1Score_lbLifted_o1a3_one, s1Score_lbLifted_o3a3_one]
  · rw [s1Score_lbLifted_o1a3_one]; exact (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num))
  · rw [s1Score_lbLifted_o1a3_one]; exact ENNReal.ofReal_ne_top
  · rw [tsum_fintype, tsum_fintype, sum_s1Score_lbLifted_o1a3, sum_s1Score_lbLifted_o3a3]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-! ### `.a1` minimal-access findings (paper findings 2, 8, 9)

Three "implicature canceled" findings at `.a1` (minimal access). Each shows
that `marginalSpeaker .a1 .s_smaller u ≤ marginalSpeaker .a1 .s_larger u`
(no implicature: smaller-state posterior ≤ larger-state posterior).

Proof strategy:
1. `unfold L1 worldPrior; rw [not_lt, posterior_le_iff_kernel_le_of_uniform]` —
   reduce to `marginalSpeaker (smaller) ≤ marginalSpeaker (larger)`.
2. `rw [marginalSpeaker_a1_sX_apply]` — unfold to 2-obs `bindOnSupport` sum.
3. Compute the two `S1g` values: `S1g(.o0a1)(u) = 0` (no quality-OK utterance);
   `S1g(.o1a1)(u) = ENNReal.ofReal (4/7)` (uniform-on-support).
4. Reduce to comparing `obsKernel(.s_smaller)(.o1a1) * (4/7) ≤
   obsKernel(.s_larger)(.o1a1) * (4/7)` — true via `obsKernel_a1_*` evaluations. -/

/-- `S1g(liftMeaning lbMeaning, .o0a1)` of `(some .one)` is `0` because the
sum-of-scores at `.o0a1` is concentrated entirely on silence. -/
private theorem S1g_lbLifted_o0a1_one_eq_zero
    (h0 : ∑' u, s1Score (liftMeaning lbMeaning) 1 .o0a1 u ≠ 0) :
    S1g (liftMeaning lbMeaning) 1 .o0a1 h0 (some NumUtt.one) = 0 := by
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_o0a1_one, zero_mul]

/-- `S1g(liftMeaning qMeaning, .o0a1)` of `(some .some_)` is `0` for the same
reason. -/
private theorem S1g_qLifted_o0a1_some_eq_zero
    (h0 : ∑' u, s1Score (liftMeaning qMeaning) 1 .o0a1 u ≠ 0) :
    S1g (liftMeaning qMeaning) 1 .o0a1 h0 (some QUtt.some_) = 0 := by
  rw [S1g, PMF.normalize_apply, s1Score_qLifted_o0a1_some, zero_mul]

/-- `S1g(liftMeaning lbMeaning, .o1a1)` of `(some .one)` is `4/7 = (1/3) / (7/12)`:
the score is `1/3` (uniform on belief support) and the partition is `7/12` (silence
contributes `1/4`, `.one` contributes `1/3`, others fail qOk). -/
private theorem S1g_lbLifted_o1a1_one_eq
    (h0 : ∑' u, s1Score (liftMeaning lbMeaning) 1 .o1a1 u ≠ 0) :
    S1g (liftMeaning lbMeaning) 1 .o1a1 h0 (some NumUtt.one) =
      ENNReal.ofReal (4/7 : ℝ) := by
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_o1a1_one]
  rw [show (∑' u, s1Score (liftMeaning lbMeaning) 1 .o1a1 u) = ENNReal.ofReal (7/12 : ℝ)
        from by rw [tsum_fintype]; exact sum_s1Score_lbLifted_o1a1]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 7/12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
  congr 1; norm_num

/-- `S1g(liftMeaning qMeaning, .o1a1)` of `(some .some_)` is `4/7` (same shape). -/
private theorem S1g_qLifted_o1a1_some_eq
    (h0 : ∑' u, s1Score (liftMeaning qMeaning) 1 .o1a1 u ≠ 0) :
    S1g (liftMeaning qMeaning) 1 .o1a1 h0 (some QUtt.some_) =
      ENNReal.ofReal (4/7 : ℝ) := by
  rw [S1g, PMF.normalize_apply, s1Score_qLifted_o1a1_some]
  rw [show (∑' u, s1Score (liftMeaning qMeaning) 1 .o1a1 u) = ENNReal.ofReal (7/12 : ℝ)
        from by rw [tsum_fintype]; exact sum_s1Score_qLifted_o1a1]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 7/12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
  congr 1; norm_num

/-- Finding 2 (silence-extended): at minimal access, the scalar implicature
is canceled — state 2 does NOT have higher posterior than state 3 under `.some_`. -/
theorem some_minimal_canceled_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning qMeaning) 1 .a1 w
                          (cover_silent qMeaning .a1 w))
              worldPrior (some QUtt.some_) ≠ 0) :
    ¬ (L1 (liftMeaning qMeaning) 1 .a1 (cover_silent qMeaning .a1)
        (some QUtt.some_) hMarg) .s2 >
      (L1 (liftMeaning qMeaning) 1 .a1 (cover_silent qMeaning .a1)
        (some QUtt.some_) hMarg) .s3 := by
  rw [gt_iff_lt, not_lt]
  unfold L1 worldPrior
  rw [PMF.posterior_le_iff_kernel_le_of_uniform]
  rw [marginalSpeaker_a1_s2_apply, marginalSpeaker_a1_s3_apply]
  -- LHS: obsKernel(.s2)(.o0a1) * S1g(.o0a1)(some_) + obsKernel(.s2)(.o1a1) * S1g(.o1a1)(some_)
  -- RHS: S1g(.o1a1)(some_) (since marginalSpeaker_a1_s3 collapses to single S1g)
  rw [S1g_qLifted_o0a1_some_eq_zero, S1g_qLifted_o1a1_some_eq,
      mul_zero, zero_add, obsKernel_a1_s2_o1a1]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2/3)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Finding 8 (silence-extended): at minimal access, "one" does NOT have higher
posterior at state 1 than state 2 (no upper-bound implicature). -/
theorem one_minimal_1v2_canceled_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a1 w
                          (cover_silent lbMeaning .a1 w))
              worldPrior (some NumUtt.one) ≠ 0) :
    ¬ (L1 (liftMeaning lbMeaning) 1 .a1 (cover_silent lbMeaning .a1)
        (some NumUtt.one) hMarg) .s1 >
      (L1 (liftMeaning lbMeaning) 1 .a1 (cover_silent lbMeaning .a1)
        (some NumUtt.one) hMarg) .s2 := by
  rw [gt_iff_lt, not_lt]
  unfold L1 worldPrior
  rw [PMF.posterior_le_iff_kernel_le_of_uniform]
  rw [marginalSpeaker_a1_s1_apply, marginalSpeaker_a1_s2_apply]
  rw [S1g_lbLifted_o0a1_one_eq_zero,
      S1g_lbLifted_o1a1_one_eq,
      mul_zero, zero_add, mul_zero, zero_add,
      obsKernel_a1_s1_o1a1, obsKernel_a1_s2_o1a1]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2/3)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Finding 9 (silence-extended): at minimal access, "one" does NOT have higher
posterior at state 1 than state 3 (no upper-bound implicature). -/
theorem one_minimal_1v3_canceled_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a1 w
                          (cover_silent lbMeaning .a1 w))
              worldPrior (some NumUtt.one) ≠ 0) :
    ¬ (L1 (liftMeaning lbMeaning) 1 .a1 (cover_silent lbMeaning .a1)
        (some NumUtt.one) hMarg) .s1 >
      (L1 (liftMeaning lbMeaning) 1 .a1 (cover_silent lbMeaning .a1)
        (some NumUtt.one) hMarg) .s3 := by
  rw [gt_iff_lt, not_lt]
  unfold L1 worldPrior
  rw [PMF.posterior_le_iff_kernel_le_of_uniform]
  rw [marginalSpeaker_a1_s1_apply, marginalSpeaker_a1_s3_apply]
  rw [S1g_lbLifted_o0a1_one_eq_zero, S1g_lbLifted_o1a1_one_eq,
      mul_zero, zero_add, obsKernel_a1_s1_o1a1]
  -- Goal: ENNReal.ofReal (1/3) * ENNReal.ofReal (4/7) ≤ ENNReal.ofReal (4/7)
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-! ### Pending: paper findings 3, 5, 10, 11

The remaining 4 findings live at `.a2` (partial access), where the obs kernel
reaches three obs (`.o0a2`, `.o1a2`, `.o2a2`) and the belief at each obs is
non-concentrated. Each requires:

1. Per-(`.a2`, `.w`, `.obs`) `obsKernel`-value lemmas (Vandermonde with denom = 3).
2. Per-`.obs` `s1Score`-value lemmas using `softmaxBelief_uniform_on_support`.
3. `marginalSpeaker_a2_apply` expansion as `bindOnSupport` 3-obs sum.

Numerical predictions (all with α = 1, `liftMeaning`-extended utterance
space, sub-PMF arithmetic — see CHANGELOG 0.230.610):

- `marginalSpeaker .a2 .s_i .one` = 0, 8/21, 132/273, 4/13.
- `marginalSpeaker .a2 .s_i .two` = 0, 0, 2/13, 6/13.
- `marginalSpeaker .a2 .s_i .some_` = 0, 8/21, 4/7, 4/7.

Headline: Finding 10 (`one_partial_1v3_sil`) is `8/21 > 4/13` (i.e.,
104/273 > 84/273). The non-monotone `marginalSpeaker .a2 .s_i .one`
profile (s1 > s3 but s2 > s1) is GS2013's distinctive prediction. -/

end Findings

end Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013.PMF
