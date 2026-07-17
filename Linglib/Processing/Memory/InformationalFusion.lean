import Linglib.Morphology.Paradigm.Complexity
import Linglib.Processing.Memory.SurprisalTradeoff

/-!
# Informational Fusion
[rathi-hahn-futrell-2021] [rathi-hahn-futrell-2026]

Sibling of `MemorySurprisal/Basic.lean`. Defines the **informational fusion**
measure introduced in [rathi-hahn-futrell-2021] and used as the central
empirical estimator in [rathi-hahn-futrell-2026]:

    φ(w | σ, ℓ, L_{-σ}) := -log p(w | σ, ℓ, L_{-σ})

The surprisal of surface form `w` for feature set `σ` of inflection class `ℓ`,
holding out all instances of `σ` from the learner's training corpus `L`. A
form is **informationally fused** when it cannot be predicted from any subset
of its features — high φ.

## Pairwise informational fusion

[rathi-hahn-futrell-2026] eq. (12) generalizes φ to **pairs** of features:

    φ₂(w | (f₁, f₂), ℓ, L_{-(f₁,f₂)}) := -log p(w | (f₁, f₂), ℓ, L_{-(f₁,f₂)})

Same shape, with the held-out subset being a feature pair rather than a single
feature. Used in §4.4 of the paper to show that pairs of features with high
informational fusion are close in optimal-ordering rankings.

## Learner model abstraction

The substrate is **agnostic** about the learner's implementation:
[rathi-hahn-futrell-2021] use an LSTM seq2seq model with attention;
in principle any learner that produces a probability over candidate forms is
admissible. `LearnerModel n` carries the prediction function as a field; the
held-out corpus and target cell are explicit parameters. Specific learners
(LSTM, n-gram, hand-coded morphological process libraries, ...) are out of
Lean scope — they live in the paper's Python codebase.

## Three formal arguments (paper Appendix A1, A2, A3)

The paper proves three pure information-theoretic claims:

- **A1**: fusion of features with positive mutual information can **lower
  local (zero-context) surprisal** of the resulting form, because the
  fused morpheme can adapt to the joint distribution rather than encoding
  each feature independently.
- **A2**: fusion of features with **zero** mutual information **raises
  long-range surprisal** (memory burden), because the fused morpheme cannot
  be reconstructed from a small context window.
- **A3**: **category clustering** — placing morphemes for mutually exclusive
  feature values in consistent slot positions — lowers local surprisal,
  because slot-position information becomes informative about feature value.

This file states A1/A2/A3 as **abstract theorems on entropy** parameterized
over distributions on `Fin n`-typed random variables. The Rathi 2026 study
file (`Studies/RathiHahnFutrell2026.lean`) instantiates
them on the paper's toy languages L_agg, L_fus, L_clustered with concrete
finite distributions, and proves the consequences computationally (`decide`
on rationals, no `decide`).

The substrate proofs use `Core.InformationTheory.conditionalEntropy_le_entropy`
(Cover-Thomas 2.6.4) and `mutualInformation_nonneg` (Cover-Thomas 2.6.5).
-/

namespace Processing.MemorySurprisal.InformationalFusion

open Morphology

-- ============================================================================
-- §1: Empirical estimator (paper §2.1.1, eq. 4 + eq. 12)
-- ============================================================================

/-- A learner model: predicts probability of a candidate form at a cell index
    given a training corpus.

    Parameterized over `Form` (the surface-form alphabet). Most consumers
    instantiate `Form := String` (matching `ParadigmSystem n String`); the
    Rathi 2026 toy paradigms use a small `[Fintype]` form alphabet so that
    PMF-based entropy operators apply. The `LearnerModel n Form` type does
    not require `[Fintype Form]`; consumers add it where needed.

    The corpus argument is the **held-out** corpus: it is the user's
    responsibility to remove the target cell (or feature pair) before
    invoking `predict`. This keeps the substrate agnostic about how the
    holdout is computed (per-cell, per-feature-pair, etc.).

    The predicted probability is a real number in `[0, 1]` summing to 1
    over candidate forms — but no invariant is enforced at the type level.
    Pathological learners can violate it, in which case `informationalFusion`
    silently returns `0` for `predict = 0` (per mathlib's `Real.log 0 = 0`
    convention) instead of `+∞`. The PMF-returning variant
    (`LearnerModel.toPMF`, deferred to a follow-up phase that supplies the
    requisite normalization proofs) closes this hole. -/
structure LearnerModel (n : Nat) (Form : Type*) where
  predict : ParadigmSystem n Form → Fin n → Form → ℝ

/-- **Informational fusion** ([rathi-hahn-futrell-2026] eq. 4):
    `φ(w | σ, ℓ, L_{-σ}) := -log p(w | σ, ℓ, L_{-σ})`.

    The surprisal of form `w` at cell `σ` under the learner `M` trained on
    the held-out corpus `corpus` (which the consumer constructs by removing
    `σ`-cells from the full paradigm). High φ means the form cannot be
    predicted from any subset of its other features. -/
noncomputable def informationalFusion {n : Nat} {Form : Type*}
    (M : LearnerModel n Form) (corpus : ParadigmSystem n Form)
    (σ : Fin n) (w : Form) : ℝ :=
  -Real.log (M.predict corpus σ w)

/-- For any learner whose `predict` returns a value in `[0, 1]`,
    `informationalFusion` (i.e., `-log predict`) is non-negative.
    Standard fact about the surprisal of a probability — included here as
    proof-of-concept that the substrate's `LearnerModel` API supports
    structural reasoning. Consumers that supply non-`[0,1]` predict values
    can construct pathological cases (silently `= 0` instead of `+∞` when
    `predict = 0`); see the `LearnerModel` docstring caveat. -/
theorem informationalFusion_nonneg {n : Nat} {Form : Type*}
    (M : LearnerModel n Form) (corpus : ParadigmSystem n Form)
    (σ : Fin n) (w : Form)
    (h_nonneg : 0 ≤ M.predict corpus σ w)
    (h_le_one : M.predict corpus σ w ≤ 1) :
    0 ≤ informationalFusion M corpus σ w := by
  unfold informationalFusion
  rw [neg_nonneg]
  exact Real.log_nonpos h_nonneg h_le_one

/-! ### Pairwise informational fusion ([rathi-hahn-futrell-2026] eq. 12)

The pairwise generalization of `informationalFusion` differs from the
single-feature case **only in how the held-out corpus is constructed**:
both cells of the pair are removed before the learner is trained.

Per the substrate's design (the consumer constructs the held-out corpus and
passes it to `LearnerModel.predict`), pairwise fusion does not need its own
function. To compute φ₂ for a feature pair `(σ, τ)`:

```
informationalFusion M (heldOutBoth corpus σ τ) σ w
```

where `heldOutBoth : ParadigmSystem n → Fin n → Fin n → ParadigmSystem n`
is a paradigm-restriction helper provided by the consumer (typically by
masking entries of both cells). The earlier substrate version of this file
exposed `pairwiseFusion` as a separate `def`, but the body was identical
to `informationalFusion` (the `τ` parameter was unused), so it has been
removed; future readers should use the recipe above. -/

/-- Average informational fusion across all forms expressing feature set σ. -/
noncomputable def averageInformationalFusion {n : Nat} {Form : Type} [DecidableEq Form]
    (M : LearnerModel n Form) (corpus : ParadigmSystem n Form)
    (σ : Fin n) : ℝ :=
  let cellDist := corpus.cellDistribution σ
  let total : ℚ := (cellDist.map Prod.snd).foldl (· + ·) 0
  if total = 0 then 0
  else
    let weighted : List ℝ := cellDist.map λ (w, freq) =>
      (freq : ℝ) * informationalFusion M corpus σ w
    (weighted.foldl (· + ·) 0) / (total : ℝ)

-- ============================================================================
-- §1.1: empiricalLearner — simplest LearnerModel instance
-- ============================================================================

/-! ### Empirical-frequency learner

The simplest non-trivial `LearnerModel`: predict probability of form `w`
at cell `σ` by its **empirical frequency** in the corpus's cell distribution
at `σ`. Formally:

    `predict corpus σ w = freq(w in corpus.cellDistribution σ) / total(...)`

This is the "memorizer" baseline — it just reads off observed frequencies
without any generalization. [ackerman-malouf-2013]'s i-complexity
implicitly uses this learner: `H(C_i | C_j)` is the conditional entropy
under empirical distributions. The bridge between A&M's i-complexity and
Rathi's informational fusion is precisely "average of `informationalFusion
empiricalLearner ...` across cell pairs," but we leave the full bridge
theorem for future work.

The empirical learner returns 0 when the cell is empty or when `w` is not
attested at the cell — this is the "totally surprising" case
(`informationalFusion empiricalLearner ... w = -log 0 = 0` per mathlib's
`Real.log` convention; pathological behaviour, see API caveat above). -/

/-- Empirical-frequency learner: predict by relative frequency in the cell
    distribution. Computable (no `Real.log`); returns ℝ via ℚ-then-ℝ
    coercion of the empirical fraction. Returns 0 when the form is unattested
    or the cell is empty.

    This is the smallest non-trivial witness that `LearnerModel` has at
    least one inhabitant; the full validity proof (probabilities sum to 1
    and are non-negative) requires `cellDistribution_nonneg` and
    `cellDistribution_sum_pos` lemmas in `Morphology/Paradigm.lean`,
    flagged as future work in the substrate restructure. The empirical
    learner's behaviour on the toy paradigms `L_agg` and `L_fus` is
    discussed in the Rathi 2026 study file. -/
noncomputable def empiricalLearner {n : Nat} {Form : Type} [DecidableEq Form] :
    LearnerModel n Form where
  predict corpus σ w :=
    let cellDist := corpus.cellDistribution σ
    let totalQ : ℚ := (cellDist.map Prod.snd).foldl (· + ·) 0
    let formQ : ℚ := ((cellDist.find? (·.1 == w)).map Prod.snd).getD 0
    if totalQ = 0 then 0 else (formQ : ℝ) / (totalQ : ℝ)

-- ============================================================================
-- §2: Three formal arguments — abstract on entropy
-- ============================================================================

/-! ### Paper Appendix A1: fusion can lower local surprisal

The paper's claim (Appendix A1): for binary features X₁, X₂ with joint
distribution `p`, in an agglutinative mapping where Y₂ depends only on X₂,
we have `H[Y₂] = H[X₂]`. In a fusional mapping where Y₂ depends on both
X₁ and X₂, we have `H[Y₂] ≤ H[X₂]` whenever conditioning on X₁ reduces the
entropy of (the part of Y₂ derived from) X₂.

The Lean abstract statement: for any joint distribution and any function
`f : α → β` with finite support, the entropy of the marginal of `f(X)` is
bounded by the entropy of `X`. This is **Cover-Thomas Theorem 2.8.2** (data
processing inequality for functions). It already follows from
`conditionalEntropy_le_entropy` (Theorem 2.6.4) plus `H[Y | X] = 0` when Y is a
deterministic function of X.

The study file specializes this to the paper's specific 4-element joint
distribution on (X₁, X₂) with the L_agg vs L_fus mappings, computing
H[Y₂] for each via `decide` on rationals.
-/

/-! **A1 (abstract)**: conditioning reduces entropy of any random variable.
    Cover-Thomas 2.6.4. This is the substrate version of the paper's
    Appendix A1 claim that fusion of correlated features can lower
    marginal entropy of the derived variable.

    The canonical statement lives at `PMF.conditionalEntropy_le_entropy` —
    `joint.conditionalEntropy ≤ joint.snd.entropy` for any joint
    PMF on `(α × β)` with strict-positive marginals. Consumers wanting the
    (ι→ℝ) form construct PMFs via `PMF.ofRealWeightFn` then apply.

    Was previously a re-export of `Core.InformationTheory.conditionalEntropy_le_entropy`;
    Core deletion via the PMF migration removes the re-export wrapper. -/

/-! **A2 (abstract scaffold)**: fusion of independent features cannot lower
    long-range surprisal.

    The canonical statement lives at `PMF.mutualInformation_nonneg` (free from
    `ENNReal.toReal_nonneg` since `PMF.mutualInformation := (klDiv ...).toReal`).
    The Rathi 2026 study file uses `decide` on the paper's specific 8-element
    joint distribution to verify the inequality computationally. -/

/-! ### Paper Appendix A3: category clustering lowers local surprisal

The paper's claim (§3.3, Appendix A3): in a 2-feature paradigm with
mutually-exclusive feature values realized in consistent slot positions
(category clustering), the marginal entropy of the slot-position random
variable is lower than in a non-clustered paradigm. The proof is a direct
comparison of two explicit 4-element distributions.

The Lean abstract statement reduces to: `entropy s p ≤ entropy s q` when
`p` is "more concentrated" than `q` in the appropriate sense (Schur
concavity of entropy). For the paper's specific 4-state distribution this
is verifiable by `decide` and lives in the study file. -/

end Processing.MemorySurprisal.InformationalFusion
