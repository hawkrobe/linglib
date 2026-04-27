import Linglib.Theories.Pragmatics.RSA.Operators
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

Definitions + cover infrastructure + grounding theorem to legacy `gsCfg`
(left as `sorry` pending PMF-shaped `rsa_predict`). The 11 finding proofs
are stated in §10 with `sorry` placeholders. Manual discharge of
`(L1 …) _ > (L1 …) _` over a softmax-of-expected-log score is not
realistic by hand — the PMF-shaped tactic is its own workstream
(see Task #36).

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

/-- The Goodman-family speaker score, instantiating `RSA.softmaxBelief`. -/
noncomputable abbrev s1Score {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool) (α : ℝ) (obs : Obs) (u : U) : ℝ≥0∞ :=
  RSA.softmaxBelief (lexReal meaning) (beliefReal obs) α (qualityOk meaning obs ·) u

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

/-! ## §10. Findings — explicit `sorry`s pending PMF-shaped `rsa_predict`

The 11 findings of `GoodmanStuhlmuller2013.lean`'s `findings` list translate
to inequalities (or negated inequalities) on `L1` apply values. Each is a
finite computation in `ℝ≥0∞` arithmetic that requires the PMF-shaped
`rsa_predict` tactic (Task #36). Each is stated below with its full L1
content and `sorry` per CLAUDE.md "Prefer `sorry` over weakening theorem
statements".

The 4 quantifier findings can be stated cleanly via `qCover`. The 7
lower-bound numeral findings carry the cover hypothesis as a parameter:
no `lbCover` exists at any access (see `lb_defect_at_o0a3` for the
honest no-witness theorem at `.a3`; the same `s0` defect blocks `.a1`
and `.a2`). Instantiating these will require either an alternative L1
that excludes `.s0` from the world prior or extending the model with
upper-bound semantics.

The marginal-non-zero hypotheses (`hMarg`) are also taken as parameters;
they are finite-arithmetic facts the PMF-shaped tactic will discharge
alongside the inequalities. -/

namespace Findings

/-! ### Quantifier findings (qMeaning)

Only `some_full_implicature` (full access `.a3`) instantiates cleanly via
`qCover_a3`. The minimal/partial findings carry the cover hypothesis as a
parameter — see `qMeaning_no_witness_at_o0a1` for the defect that blocks
`.a1` and `.a2`.

**Structural discharge** for positive findings (post-0.230.391 template):
1. `unfold L1 worldPrior` — expose primitives
2. `rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]` — cancel L1 marginal AND uniform world prior in one move
3. Per-world leaf: `marginalSpeaker .a3 w₁ ... u < marginalSpeaker .a3 w₂ ... u`

The leaf is a `bindOnSupport` comparison where BOTH the obs kernel AND the
inner speaker function depend on the world being compared. No further generic
`_lt_iff` lemma helps — this is the per-model numeric core. Bundled here as
a sorry'd helper per finding. -/

/-- Per-world leaf for `some_full_implicature`. The marginal speaker assigns
more `.some_` mass at `.s2` (where "some" is most informative) than at `.s3`
(where "all" would be more informative). -/
theorem marginalSpeaker_qSome_s2_gt_s3
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a3 w).support, ∃ u : QUtt, qualityOk qMeaning obs u) :
    marginalSpeaker qMeaning 1 .a3 .s3 (hCov .s3) .some_ <
    marginalSpeaker qMeaning 1 .a3 .s2 (hCov .s2) .some_ := by
  sorry  -- per-model numeric leaf: bindOnSupport over obsKernel + softmaxBelief comparison

/-- Finding 1: at full access, `some` favors `s2 > s3` (scalar implicature). -/
theorem some_full_implicature
    (hMarg : PMF.marginal (fun w => marginalSpeaker qMeaning 1 .a3 w (qCover_a3 w))
                worldPrior .some_ ≠ 0) :
    (L1 qMeaning 1 .a3 qCover_a3 .some_ hMarg) .s2 >
      (L1 qMeaning 1 .a3 qCover_a3 .some_ hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact marginalSpeaker_qSome_s2_gt_s3 qCover_a3

/-! ### Negative-finding template

Negative findings have the shape `¬ L1 a₁ > L1 a₂`. Via `not_lt + gt_iff_lt`,
this reduces to `L1 a₂ ≤ L1 a₁`. The `posterior_le_iff_kernel_le_of_uniform`
companion lemma cancels the marginal AND uniform prior in one step, leaving
a per-world `marginalSpeaker` ≤ leaf. -/

/-- Per-world ≤ leaf: at minimal access `.a1`, `some` does not strictly prefer
`s2` over `s3` — the marginal speaker assigns no more `.some_` mass at `.s2`
than at `.s3`. -/
theorem marginalSpeaker_qSome_a1_s2_le_s3
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a1 w).support, ∃ u : QUtt, qualityOk qMeaning obs u) :
    marginalSpeaker qMeaning 1 .a1 .s2 (hCov .s2) .some_ ≤
    marginalSpeaker qMeaning 1 .a1 .s3 (hCov .s3) .some_ := by
  sorry  -- per-model numeric leaf

/-- Finding 2: at minimal access, `some` does *not* favor `s2 > s3` (canceled). -/
theorem some_minimal_canceled
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a1 w).support, ∃ u : QUtt, qualityOk qMeaning obs u)
    (hMarg : PMF.marginal (fun w => marginalSpeaker qMeaning 1 .a1 w (hCov w))
                worldPrior .some_ ≠ 0) :
    ¬ (L1 qMeaning 1 .a1 hCov .some_ hMarg) .s2 >
        (L1 qMeaning 1 .a1 hCov .some_ hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, not_lt, PMF.posterior_le_iff_kernel_le_of_uniform]
  exact marginalSpeaker_qSome_a1_s2_le_s3 hCov

/-- Per-world ≤ leaf for `some_partial_canceled`. -/
theorem marginalSpeaker_qSome_a2_s2_le_s3
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a2 w).support, ∃ u : QUtt, qualityOk qMeaning obs u) :
    marginalSpeaker qMeaning 1 .a2 .s2 (hCov .s2) .some_ ≤
    marginalSpeaker qMeaning 1 .a2 .s3 (hCov .s3) .some_ := by
  sorry  -- per-model numeric leaf

/-- Finding 3: at partial access, `some` does *not* favor `s2 > s3` (canceled). -/
theorem some_partial_canceled
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a2 w).support, ∃ u : QUtt, qualityOk qMeaning obs u)
    (hMarg : PMF.marginal (fun w => marginalSpeaker qMeaning 1 .a2 w (hCov w))
                worldPrior .some_ ≠ 0) :
    ¬ (L1 qMeaning 1 .a2 hCov .some_ hMarg) .s2 >
        (L1 qMeaning 1 .a2 hCov .some_ hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, not_lt, PMF.posterior_le_iff_kernel_le_of_uniform]
  exact marginalSpeaker_qSome_a2_s2_le_s3 hCov

/-! ### Lower-bound numeral findings (lbMeaning, cover hypothesis as input) -/

/-- Per-world leaf: `two` is more compatible with `s2` than with `s3` under `.a3`. -/
theorem marginalSpeaker_lbTwo_s2_gt_s3
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a3 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u) :
    marginalSpeaker lbMeaning 1 .a3 .s3 (hCov .s3) .two <
    marginalSpeaker lbMeaning 1 .a3 .s2 (hCov .s2) .two := by
  sorry  -- per-model numeric leaf

/-- Finding 4: at full access, `two` favors `s2 > s3` (upper-bounded reading). -/
theorem two_full_upper_bounded
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a3 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u)
    (hMarg : PMF.marginal (fun w => marginalSpeaker lbMeaning 1 .a3 w (hCov w))
                worldPrior .two ≠ 0) :
    (L1 lbMeaning 1 .a3 hCov .two hMarg) .s2 >
      (L1 lbMeaning 1 .a3 hCov .two hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact marginalSpeaker_lbTwo_s2_gt_s3 hCov

/-- Per-world ≤ leaf for `two_partial_weakened`. -/
theorem marginalSpeaker_lbTwo_a2_s2_le_s3
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a2 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u) :
    marginalSpeaker lbMeaning 1 .a2 .s2 (hCov .s2) .two ≤
    marginalSpeaker lbMeaning 1 .a2 .s3 (hCov .s3) .two := by
  sorry  -- per-model numeric leaf

/-- Finding 5: at partial access, `two` does *not* favor `s2 > s3` (weakened). -/
theorem two_partial_weakened
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a2 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u)
    (hMarg : PMF.marginal (fun w => marginalSpeaker lbMeaning 1 .a2 w (hCov w))
                worldPrior .two ≠ 0) :
    ¬ (L1 lbMeaning 1 .a2 hCov .two hMarg) .s2 >
        (L1 lbMeaning 1 .a2 hCov .two hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, not_lt, PMF.posterior_le_iff_kernel_le_of_uniform]
  exact marginalSpeaker_lbTwo_a2_s2_le_s3 hCov

/-- Per-world leaf: `one` is more compatible with `s1` than with `s2` under `.a3`. -/
theorem marginalSpeaker_lbOne_s1_gt_s2
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a3 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u) :
    marginalSpeaker lbMeaning 1 .a3 .s2 (hCov .s2) .one <
    marginalSpeaker lbMeaning 1 .a3 .s1 (hCov .s1) .one := by
  sorry  -- per-model numeric leaf

/-- Finding 6: at full access, `one` favors `s1 > s2`. -/
theorem one_full_1v2
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a3 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u)
    (hMarg : PMF.marginal (fun w => marginalSpeaker lbMeaning 1 .a3 w (hCov w))
                worldPrior .one ≠ 0) :
    (L1 lbMeaning 1 .a3 hCov .one hMarg) .s1 >
      (L1 lbMeaning 1 .a3 hCov .one hMarg) .s2 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact marginalSpeaker_lbOne_s1_gt_s2 hCov

/-- Per-world leaf: `one` is more compatible with `s1` than with `s3` under `.a3`. -/
theorem marginalSpeaker_lbOne_s1_gt_s3
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a3 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u) :
    marginalSpeaker lbMeaning 1 .a3 .s3 (hCov .s3) .one <
    marginalSpeaker lbMeaning 1 .a3 .s1 (hCov .s1) .one := by
  sorry  -- per-model numeric leaf

/-- Finding 7: at full access, `one` favors `s1 > s3`. -/
theorem one_full_1v3
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a3 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u)
    (hMarg : PMF.marginal (fun w => marginalSpeaker lbMeaning 1 .a3 w (hCov w))
                worldPrior .one ≠ 0) :
    (L1 lbMeaning 1 .a3 hCov .one hMarg) .s1 >
      (L1 lbMeaning 1 .a3 hCov .one hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact marginalSpeaker_lbOne_s1_gt_s3 hCov

/-- Per-world ≤ leaf for `one_minimal_1v2_canceled`. -/
theorem marginalSpeaker_lbOne_a1_s1_le_s2
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a1 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u) :
    marginalSpeaker lbMeaning 1 .a1 .s1 (hCov .s1) .one ≤
    marginalSpeaker lbMeaning 1 .a1 .s2 (hCov .s2) .one := by
  sorry  -- per-model numeric leaf

/-- Finding 8: at minimal access, `one` does *not* favor `s1 > s2` (canceled). -/
theorem one_minimal_1v2_canceled
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a1 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u)
    (hMarg : PMF.marginal (fun w => marginalSpeaker lbMeaning 1 .a1 w (hCov w))
                worldPrior .one ≠ 0) :
    ¬ (L1 lbMeaning 1 .a1 hCov .one hMarg) .s1 >
        (L1 lbMeaning 1 .a1 hCov .one hMarg) .s2 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, not_lt, PMF.posterior_le_iff_kernel_le_of_uniform]
  exact marginalSpeaker_lbOne_a1_s1_le_s2 hCov

/-- Per-world ≤ leaf for `one_minimal_1v3_canceled`. -/
theorem marginalSpeaker_lbOne_a1_s1_le_s3
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a1 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u) :
    marginalSpeaker lbMeaning 1 .a1 .s1 (hCov .s1) .one ≤
    marginalSpeaker lbMeaning 1 .a1 .s3 (hCov .s3) .one := by
  sorry  -- per-model numeric leaf

/-- Finding 9: at minimal access, `one` does *not* favor `s1 > s3` (canceled). -/
theorem one_minimal_1v3_canceled
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a1 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u)
    (hMarg : PMF.marginal (fun w => marginalSpeaker lbMeaning 1 .a1 w (hCov w))
                worldPrior .one ≠ 0) :
    ¬ (L1 lbMeaning 1 .a1 hCov .one hMarg) .s1 >
        (L1 lbMeaning 1 .a1 hCov .one hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, not_lt, PMF.posterior_le_iff_kernel_le_of_uniform]
  exact marginalSpeaker_lbOne_a1_s1_le_s3 hCov

/-- Per-world leaf: at partial access `.a2`, `one` is more compatible with `s1` than `s3`. -/
theorem marginalSpeaker_lbOne_a2_s1_gt_s3
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a2 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u) :
    marginalSpeaker lbMeaning 1 .a2 .s3 (hCov .s3) .one <
    marginalSpeaker lbMeaning 1 .a2 .s1 (hCov .s1) .one := by
  sorry  -- per-model numeric leaf

/-- Finding 10: at partial access, `one` favors `s1 > s3` (partial implicature). -/
theorem one_partial_1v3
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a2 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u)
    (hMarg : PMF.marginal (fun w => marginalSpeaker lbMeaning 1 .a2 w (hCov w))
                worldPrior .one ≠ 0) :
    (L1 lbMeaning 1 .a2 hCov .one hMarg) .s1 >
      (L1 lbMeaning 1 .a2 hCov .one hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact marginalSpeaker_lbOne_a2_s1_gt_s3 hCov

/-- Per-world ≤ leaf for `one_partial_1v2_canceled`. -/
theorem marginalSpeaker_lbOne_a2_s1_le_s2
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a2 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u) :
    marginalSpeaker lbMeaning 1 .a2 .s1 (hCov .s1) .one ≤
    marginalSpeaker lbMeaning 1 .a2 .s2 (hCov .s2) .one := by
  sorry  -- per-model numeric leaf

/-- Finding 11: at partial access, `one` does *not* favor `s1 > s2` (still canceled). -/
theorem one_partial_1v2_canceled
    (hCov : ∀ w, ∀ obs ∈ (obsKernel .a2 w).support, ∃ u : NumUtt, qualityOk lbMeaning obs u)
    (hMarg : PMF.marginal (fun w => marginalSpeaker lbMeaning 1 .a2 w (hCov w))
                worldPrior .one ≠ 0) :
    ¬ (L1 lbMeaning 1 .a2 hCov .one hMarg) .s1 >
        (L1 lbMeaning 1 .a2 hCov .one hMarg) .s2 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, not_lt, PMF.posterior_le_iff_kernel_le_of_uniform]
  exact marginalSpeaker_lbOne_a2_s1_le_s2 hCov

end Findings

end Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013.PMF
