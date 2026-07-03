import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Linglib.Processing.Expectation.LanguageModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

/-!
# Memory Processes (Noisy-Channel Substrate, Memory-Side)
[futrell-gibson-levy-2020]

A `MemoryProcess` is the memory-side noisy-channel substrate of
[futrell-gibson-levy-2020]'s lossy-context surprisal: a processor that
compresses its observed history into a (possibly noisy) memory state, then
predicts the next symbol from that memory state alone. This is the
context-noise specialization of the broader noisy-channel comprehension
posture (cf. Gibson-Bergen-Piantadosi 2013 for input-string noise; Levy
2011 for noise on both the input and the memory of context).

Following the paper's claims (§3.1, Claims 1–4):

1. **Incrementality of memory** (Claim 1) — the encoder
   `encode : List Voc → PMF Mem` maps each observed history to a distribution
   over memory states. (FGL state Claim 1 in terms of a recursive step
   `m : R × W → R`; the bundled iterated form here discharges incrementality
   silently and is a known schema simplification.)
2. **Linguistic knowledge** (Claim 2) — the predictor
   `predict : Mem → PMF (Option Voc)` maps each memory state to a next-symbol
   distribution (with `none` = end-of-string).
3. **Inaccessibility of context** (Claim 3) — the predictor sees *only* the
   memory state, never the underlying history. This is what makes the model
   *lossy*.
4. **Linking hypothesis** (Claim 4) — processing difficulty for the next
   symbol is `expectedSurprisal` (Eq. 3 of the paper), the expectation of
   `-log P(w | m)` over `m ~ encode(c)`.

This file provides the abstract type and the master cost function.
Specialisations (lossless = classical surprisal, n-gram, erasure noise)
live in sibling files. Whether activation-based retrieval (see
`Studies/BakayEtAl2026.lean`) also derives as an instantiation is open.

The encoder and predictor are mathlib `PMF` kernels (countable support,
`ℝ≥0∞`-valued), so neither `Voc` nor `Mem` need to be `Fintype`. Expected
sums are taken as `tsum` (`∑'`) which collapses to `Finset.sum` whenever a
`Fintype` instance is in scope.

## Main definitions

- `MemoryProcess Voc Mem` — pair of `(encode, predict)` kernels
- `MemoryProcess.perStateSurprisal` — `-log P(w | m)`, the inner factor of
  Eq. 2/Eq. 3
- `MemoryProcess.expectedSurprisal` — Eq. 3: `E_{m ~ encode(c)}[-log P(w | m)]`
- `MemoryProcess.marginalProb` — forward-marginal `P(w | c) = Σ_m P(m|c)·P(w|m)`
  under the joint kernel `(encode, predict)` (the paper's noisy-channel
  inversion in §3.3 / Eqs. 4–9 goes the *other* direction, summing over
  contexts; the forward marginal here is implicit in the setup but not
  separately numbered)
- `MemoryProcess.IsDirac` — encoder is a point mass at `f c` (lossless)

## Main theorem

- `expectedSurprisal_of_dirac` — when the encoder is a Dirac at `f c`, expected
  surprisal collapses to per-state surprisal at `f c`. This is the structural
  identity that turns the lossless case into classical surprisal in
  `LossyContext.lean`.
-/

set_option autoImplicit false

namespace Processing.NoisyChannel

open Real
open scoped ENNReal
open Processing.LanguageModel (LangModel)

/-- A processing architecture with a memory bottleneck.

`encode` lossily compresses the observed history into a distribution over
memory states; `predict` gives the next-symbol distribution from a memory
state alone. The memory state mediates *all* information flow from the
past to the prediction (the inaccessibility-of-context claim of
[futrell-gibson-levy-2020] §3.1, Claim 3). -/
structure MemoryProcess (Voc Mem : Type*) where
  /-- Lossy encoder: history → distribution over memory states. -/
  encode : List Voc → PMF Mem
  /-- Predictor: memory state → next-symbol distribution. -/
  predict : Mem → PMF (Option Voc)

namespace MemoryProcess

variable {Voc Mem : Type*}

/-- Per-state surprisal: `D_lc(w | m) = -log P(w | m)`.

This is the inner factor that appears inside the paper's Eq. 2 (linking
hypothesis as proportionality) and Eq. 3 (expected-surprisal expectation).
[futrell-gibson-levy-2020] does not give it a standalone equation
number, but factoring it out is convenient for the Dirac-collapse proof
below. -/
noncomputable def perStateSurprisal (mp : MemoryProcess Voc Mem)
    (m : Mem) (w : Voc) : ℝ :=
  -Real.log (mp.predict m (some w)).toReal

/-- Expected surprisal under the lossy memory process:
`D_lc(w | c) = E_{m ~ encode(c)}[-log P(w | m)]`.
([futrell-gibson-levy-2020] Eq. 3.)

This is the master cost function from which classical surprisal and
n-gram surprisal derive as instantiations of `(encode, predict)`. -/
noncomputable def expectedSurprisal (mp : MemoryProcess Voc Mem)
    (c : List Voc) (w : Voc) : ℝ :=
  ∑' m : Mem, (mp.encode c m).toReal * mp.perStateSurprisal m w

/-- Forward-marginal next-symbol probability under the memory process:
`P(w | c) = Σ_m P(m | c) · P(w | m)`.

Computed as `(encode c).bind predict` evaluated at `some w` — the
mathlib `PMF` monad bind is exactly the marginal of the joint kernel.

This forward marginal is implicit in [futrell-gibson-levy-2020]'s
setup but not separately numbered. The paper's noisy-channel inversion
in §3.3 (Eqs. 4–9) goes the *other* direction: marginalizing over
contexts `c` to compute `p(w | r)` from a fixed memory state `r`. The
forward kernel below — marginalizing over memory states `m` given a
context `c` — is the dual operation.

Note: `-log marginalProb` (the surprisal of the *marginal*) is not in
general equal to `expectedSurprisal` (the *expected* surprisal). The two
agree iff the encoder is a Dirac (no information loss); otherwise Jensen
gives `expectedSurprisal ≥ -log marginalProb`. -/
noncomputable def marginalProb (mp : MemoryProcess Voc Mem)
    (c : List Voc) (w : Voc) : ℝ≥0∞ :=
  ((mp.encode c).bind mp.predict) (some w)

/-- The memory process is *Dirac at* `f` if the encoder concentrates
all mass on `f c` for every history `c`. This is the lossless
("perfect memory") regime: the memory state is a deterministic
function of the history.

([futrell-gibson-levy-2020] §3.5.1: classical surprisal arises
exactly in this case.) -/
def IsDirac (mp : MemoryProcess Voc Mem)
    (f : List Voc → Mem) : Prop :=
  ∀ c, mp.encode c = PMF.pure (f c)

/-- **Dirac collapse.** When the encoder is a Dirac at `f c`, expected
surprisal reduces to per-state surprisal evaluated at `f c`. The
expectation has no spread to average over.

This is the structural identity that lets us recover classical
surprisal as the special case of `expectedSurprisal` with lossless
memory (see `LossyContext.lean`'s
`expectedSurprisal_eq_surprisal_of_lossless`). -/
theorem expectedSurprisal_of_dirac
    {mp : MemoryProcess Voc Mem} {f : List Voc → Mem}
    (h : mp.IsDirac f) (c : List Voc) (w : Voc) :
    mp.expectedSurprisal c w = mp.perStateSurprisal (f c) w := by
  unfold expectedSurprisal
  rw [h c]
  classical
  rw [tsum_eq_single (f c)]
  · simp only [PMF.pure_apply_self, ENNReal.toReal_one, one_mul]
  · intro m hm
    rw [PMF.pure_apply_of_ne _ _ hm]
    simp only [ENNReal.toReal_zero, zero_mul]

/-- **Constant-encoder limit (regression to prior).** When the encoder
ignores its input and concentrates on a single memory state `m₀`, expected
surprisal collapses to per-state surprisal at `m₀`. The predictor's
distribution at `m₀` is then the comprehender's *prior* (no context-derived
information) — so per-state surprisal here is the unigram log-prob.

This is the opposite extreme of `expectedSurprisal_eq_surprisal_of_lossless`:
where lossless memory recovers classical surprisal, *fully lossy* memory
(all context information discarded) recovers the unigram prior. Together
they bracket the lossy-context regime — [futrell-gibson-levy-2020]
§3.4.2 ("when all information about a true context is lost, the difficulty
of comprehending a word is given exactly by its log prior unigram
probability"). -/
theorem expectedSurprisal_of_constantEncoder
    {mp : MemoryProcess Voc Mem} {m₀ : Mem}
    (h : ∀ c, mp.encode c = PMF.pure m₀) (c : List Voc) (w : Voc) :
    mp.expectedSurprisal c w = mp.perStateSurprisal m₀ w :=
  expectedSurprisal_of_dirac (f := fun _ => m₀) h c w

/-- **Jensen bound: expected surprisal lower-bounds marginal surprisal.**
The expected surprisal under the lossy memory process is always at least
the surprisal of the *forward marginal* `(encode c).bind predict`.

Equivalently: the per-state-then-expectation order yields a higher
processing cost than the marginal-then-surprisal order. The two agree iff
the encoder is a Dirac (no information loss); in general Jensen's
inequality applied to the concave function `log` gives the strict direction.

This is the substantive content of "lossy memory makes things harder":
[futrell-gibson-levy-2020] Suppl. Mat. A's *memory distortion bound*
rests on this Jensen gap.

**Hypotheses.** `[Fintype Mem]` reduces tsum to Finset.sum so that
mathlib's `ConcaveOn.le_map_sum` applies directly. `h_pos` requires the
per-state predicted probability of `w` to be strictly positive at *every*
memory state — needed because mathlib's `Real.log 0 = 0` convention
breaks the bound at zero entries: a memory state with positive `encode`
mass but zero `predict` mass for `w` contributes `0` to expected
surprisal under the convention but a positive contribution to the
marginal, so `−log marginalProb` could exceed `expectedSurprisal`. -/
theorem neg_log_marginalProb_le_expectedSurprisal
    [Fintype Mem]
    (mp : MemoryProcess Voc Mem) (c : List Voc) (w : Voc)
    (h_pos : ∀ m, 0 < (mp.predict m (some w)).toReal) :
    -Real.log (mp.marginalProb c w).toReal ≤ mp.expectedSurprisal c w := by
  classical
  set μ : Mem → ℝ := fun m => (mp.encode c m).toReal with hμ_def
  set p : Mem → ℝ := fun m => (mp.predict m (some w)).toReal with hp_def
  -- Reduce expectedSurprisal to a Finset.sum (Fintype Mem).
  have h_es : mp.expectedSurprisal c w = ∑ m : Mem, μ m * (-Real.log (p m)) :=
    tsum_eq_sum (fun m hm => absurd (Finset.mem_univ m) hm)
  -- Reduce marginalProb to a Finset.sum.
  have h_mp : (mp.marginalProb c w).toReal = ∑ m : Mem, μ m * p m := by
    show ((mp.encode c).bind mp.predict (some w)).toReal = _
    rw [PMF.bind_apply,
      tsum_eq_sum (s := (Finset.univ : Finset Mem))
        (fun m hm => absurd (Finset.mem_univ m) hm),
      ENNReal.toReal_sum (fun m _ =>
        ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))]
    simp only [ENNReal.toReal_mul, hμ_def, hp_def]
  -- Weights are non-negative and sum to one.
  have hμ_nn : ∀ m ∈ (Finset.univ : Finset Mem), 0 ≤ μ m :=
    fun m _ => ENNReal.toReal_nonneg
  have hμ_sum : ∑ m : Mem, μ m = 1 := by
    have htsum : ∑' m : Mem, mp.encode c m = 1 := (mp.encode c).tsum_coe
    rw [tsum_eq_sum (s := (Finset.univ : Finset Mem))
        (fun m hm => absurd (Finset.mem_univ m) hm)] at htsum
    have : (∑ m : Mem, mp.encode c m).toReal = (1 : ℝ≥0∞).toReal := by rw [htsum]
    rwa [ENNReal.toReal_sum (fun m _ => PMF.apply_ne_top _ _),
      ENNReal.toReal_one] at this
  -- Concavity of log on (0, ∞), applied via Jensen.
  have h_mem : ∀ m ∈ (Finset.univ : Finset Mem), p m ∈ Set.Ioi (0 : ℝ) :=
    fun m _ => h_pos m
  have hlog_concave : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
    StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi
  have hJensen := hlog_concave.le_map_sum (t := (Finset.univ : Finset Mem))
    (w := μ) (p := p) hμ_nn hμ_sum h_mem
  -- hJensen : ∑ μ m • Real.log (p m) ≤ Real.log (∑ μ m • p m)
  simp only [smul_eq_mul] at hJensen
  -- Rewrite goal in Finset.sum form and conclude.
  rw [h_es, h_mp]
  -- Goal: -Real.log (∑ m, μ m * p m) ≤ ∑ m, μ m * (-Real.log (p m))
  have h_neg : ∑ m : Mem, μ m * (-Real.log (p m))
      = -∑ m : Mem, μ m * Real.log (p m) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [h_neg]
  linarith [hJensen]

end MemoryProcess

end Processing.NoisyChannel
