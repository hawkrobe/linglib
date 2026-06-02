import Linglib.Processing.Lexical.Discriminative.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# DLM training: Endstate Learning vs Frequency-Informed Learning
[baayen-2019] [gahl-baayen-2024] [heitmeier-chuang-baayen-2026]

Sibling to `Defs.lean`, `Normed.lean`, `Measures.lean`. Hosts the
substrate for **what counts as a learned production map** — the
optimization characterization of EndState Learning (EL) and
Frequency-Informed Learning (FIL).

## Paper-faithful representation: `FrequencyVector` (= paper's `Q`)

`FrequencyVector m` is the type-faithful representation of paper
[gahl-baayen-2024]'s diagonal frequency matrix `Q` (appendix §A1.3):
one nonneg weight per usage event. We do *not* normalise to a
probability distribution; the paper works with raw counts. The PMF
view is a derived bridge — call `PMF.ofRealWeightFn` from
`Core.Probability.Constructions` directly when cross-tradition
theorems require it. The ERM-equivalence between raw `q` and
normalised `q.normalize` is proved in the sibling file
`RescalingInvariance.lean`.

The cognitive interpretation: `q i` is the number of times the
learner has experienced event `i`. EL corresponds to type-uniform
weights (`q ≡ 1`); FIL corresponds to token-frequency weights
(`q i = #occurrences`).

## What this file establishes

The substantive cross-framework structure. Different cognitive
theories of learning correspond to different choices of `q`; the
substrate captures the architecture in which those theories diverge:

- `weightedLoss data q G` — the per-event squared-error loss
  weighted by `q`. Paper appendix §A1.3 of [gahl-baayen-2024].
- `IsERMSolution data q G` — `G` minimises the weighted loss. The
  cognitive theory choice IS the choice of `q`; the optimization
  procedure is fixed.
- `IsELSolution data G` and `IsFILSolution data q G` — abbrevs
  capturing the type-uniform and frequency-weighted cases.
- `weightedLoss_smul_frequency` — loss is linear in `q`.
- `ermSolution_iff_rescaled` — **T-Rescaling**: the ERM solution
  is invariant under positive rescaling of `q`. Relative
  frequencies matter; absolute scale doesn't. (Paper §3.1
  appendix discussion of the equivalent FIL forms.)
- `weightedLoss_zero_event_drops` — **T-Support (weak form)**:
  events with `q i = 0` contribute nothing to the loss. Novel
  unattested events don't update the lexicon.
- `isELSolution_eq_isERM_uniform` — **T-Uniform-EL-equivalence**:
  EL is ERM under the constant-1 frequency vector. Definitional.

## What this file does NOT do

This is **not** generic regression formalization. The substrate
captures:

1. The **loss function** `weightedLoss` as the cognitive commitment
   (paper §3 of [gahl-baayen-2024]: minimising squared error
   per usage event is what the learner does).
2. The **frequency-weight parameterisation** as the cross-theory
   axis (paper §3.1 distinguishes EL from FIL only via `q`).

We do *not* formalise:

- The **closed-form** `(SᵀQS)⁻¹SᵀQC` — that's matrix algebra,
  not theory-specific. A future `Training/ClosedForm.lean` could
  derive it from the optimization characterization here as a
  theorem (= "the closed form is the unique minimum when `SᵀQS`
  is invertible") — but that's regression formalization in the
  service of showing equivalence to the optimization picture.
- The **iterative Widrow-Hoff** convergence to `IsFILSolution`
  (paper appendix §A5.1; [heitmeier-chuang-baayen-2026]
  Heitmeier 2024 argument). Defer until a 2nd consumer needs it.
- The **PMF / ERM-theoretic** reformulation. Mathematically
  equivalent in finite case, but interpretively additive — the
  paper authors avoid framing this as ERM under empirical
  distributions (see §6.4: "we would caution against reifying any
  particular variable on the basis of its predictiveness"). A
  derived PMF view is straightforward via normalization.
-/

namespace Processing.Lexical.Discriminative

noncomputable section TrainingSubstrate

variable {m n d : ℕ}  -- m = numEvents, n = formDim, d = meaningDim

-- ============================================================================
-- §1: Substrate types
-- ============================================================================

/-- A **training experience** is a finite indexed collection of
    `(meaning, form)` observation pairs. The paper's `S` matrix has
    rows `data.meanings i` and `C` matrix has rows `data.forms i`,
    indexed by event `i : Fin m`.

    The cognitive interpretation: each `i : Fin m` is a "usage event"
    — a single attestation of a (meaning, form) pair. Type-based
    learning treats each unique pair as one event; frequency-informed
    learning may have multiple events per pair (replication = weight,
    deferred). -/
structure TrainingExperience (numEvents formDim meaningDim : ℕ) where
  meanings : Fin numEvents → MeaningVec meaningDim
  forms    : Fin numEvents → FormVec formDim

/-- A **frequency vector** — paper notation `Q` (the diagonal entries
    of the weight matrix in [gahl-baayen-2024] appendix §A1.3).
    One nonneg weight per usage event.

    We use `Fin m → ℝ` (rather than `Fin m → NNReal`) for proof
    convenience; nonnegativity is documented and asserted as a
    hypothesis in theorems that need it. The cognitive theory choice
    IS the choice of `q`:

    - `q ≡ 1` (uniform): type-based learning → EL
    - `q i = #occurrences i`: frequency-informed → FIL
    - `q i = log(#occurrences i)`: log-frequency learning
    - `q i = exp(-decay · timeAgo i)`: recency-weighted

    All instantiations of `FrequencyVector` correspond to different
    cognitive commitments about which usage events count for learning. -/
abbrev FrequencyVector (numEvents : ℕ) : Type := Fin numEvents → ℝ

/-- The constant-1 frequency vector — type-uniform weighting; every
    event counts once regardless of frequency. Endstate learning
    operates with this `q`. -/
def uniformFrequency (m : ℕ) : FrequencyVector m :=
  fun _ => 1

/-- Total mass of a frequency vector — the sum of all event weights.
    Cognitive interpretation: the total accumulated experience the
    learner has been exposed to. -/
def FrequencyVector.totalMass (q : FrequencyVector m) : ℝ :=
  ∑ i, q i

/-- Normalise a frequency vector so its weights sum to 1. The result
    represents the **empirical distribution** over events. Note this
    is a `FrequencyVector` (still typed as `Fin m → ℝ`); for the
    actual `PMF` cast use `PMF.ofRealWeightFn` from
    `Core.Probability.Constructions`. -/
def FrequencyVector.normalize (q : FrequencyVector m) : FrequencyVector m :=
  fun i => q i / q.totalMass

@[simp] theorem FrequencyVector.normalize_apply
    (q : FrequencyVector m) (i : Fin m) :
    q.normalize i = q i / q.totalMass := rfl

-- ============================================================================
-- §2: The weighted loss
-- ============================================================================

/-- Squared coordinate-distance between two form vectors:
    `Σⱼ (a j - b j)²`. Direct formula, no normed-space machinery
    required. Distinct from the bare-Pi sup-norm in `Normed.lean`;
    here we want the L² (Frobenius) inner product structure on
    `Fin n → ℝ` that the paper's quadratic loss uses. -/
def squaredDist (a b : FormVec n) : ℝ :=
  ∑ j, (a j - b j) ^ 2

/-- The **frequency-weighted training loss** for a candidate
    production map `G`:

    `weightedLoss data q G = Σᵢ qᵢ · ‖G(meaningsᵢ) − formsᵢ‖²`

    where `‖·‖²` is squared coordinate-distance (= squared Frobenius
    norm on the form-vector slot).

    This is the paper's loss in its appendix §A1.3 form, before
    being recast as the matrix expression `‖√Q (SG − C)‖²_F`. The
    cognitive commitment is at the level of this loss function:
    the learner minimises the per-event squared mismatch between
    the produced and observed form vectors, weighted by frequency
    of occurrence. -/
def weightedLoss
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) : ℝ :=
  ∑ i, q i * squaredDist (G (data.meanings i)) (data.forms i)

-- ============================================================================
-- §3: Solution Props — ERM, EL, FIL
-- ============================================================================

/-- A linear map `G` is an **empirical risk minimiser** (ERM) for
    the experience `data` under frequency vector `q` if no other
    linear map achieves a smaller weighted loss.

    The cognitive theory choice IS the choice of `q`. Different
    theories of learning specify different `q`'s; the optimisation
    procedure (minimise the resulting weighted L² loss) is fixed
    across them. -/
def IsERMSolution
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) : Prop :=
  ∀ G' : MeaningVec d →ₗ[ℝ] FormVec n,
    weightedLoss data q G ≤ weightedLoss data q G'

/-- An **endstate-learning solution** for the experience: an ERM
    solution under type-uniform weights. Paper appendix §A1.1 of
    [gahl-baayen-2024]. -/
abbrev IsELSolution
    (data : TrainingExperience m n d)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) : Prop :=
  IsERMSolution data (uniformFrequency m) G

/-- A **frequency-informed learning solution** — abbreviation for
    ERM under arbitrary `q`. The cognitive interpretation that `q`
    is "token frequencies of usage events" lives in the choice of
    `q` the consumer passes; the substrate is agnostic about which
    `q` is empirically correct.

    Paper appendix §A1.3 of [gahl-baayen-2024] introduces FIL
    with `q` = corpus token frequencies; future cognitive theories
    may motivate other `q` choices. -/
abbrev IsFILSolution
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) : Prop :=
  IsERMSolution data q G

-- ============================================================================
-- §4: Structural theorems
-- ============================================================================

/-- **T-Loss-linearity**: the weighted loss is linear in the
    frequency vector. Direct algebraic fact; basis for `T-Rescaling`. -/
theorem weightedLoss_smul_frequency
    (data : TrainingExperience m n d) (q : FrequencyVector m) (c : ℝ)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    weightedLoss data (c • q) G = c * weightedLoss data q G := by
  unfold weightedLoss
  rw [Finset.mul_sum (Finset.univ : Finset (Fin m))]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (c • q) i * _ = c * (q i * _)
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- **T-Loss-add-distrib**: the weighted loss decomposes additively
    over the frequency vector. Used downstream to formalise mixture
    decompositions of cognitive theories. -/
theorem weightedLoss_add_frequency
    (data : TrainingExperience m n d) (q₁ q₂ : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    weightedLoss data (q₁ + q₂) G = weightedLoss data q₁ G + weightedLoss data q₂ G := by
  unfold weightedLoss
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (q₁ + q₂) i * _ = q₁ i * _ + q₂ i * _
  rw [Pi.add_apply, add_mul]

/-- **T-Rescaling**: ERM solutions are invariant under positive
    rescaling of the frequency vector. Relative frequencies matter;
    absolute scale doesn't.

    Cognitive content: a learner who has experienced word A 100
    times and word B 50 times has the same trained lexicon as one
    who experienced A 200 times and B 100 times. Time of accumulated
    experience (= overall scale of `q`) doesn't affect the trained
    end-state — only the relative ratios.

    Proved via `weightedLoss_smul_frequency`: scaling `q` by `c > 0`
    scales the loss by `c`; argmins are invariant under positive
    scalar multiples. -/
theorem ermSolution_iff_rescaled
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) {c : ℝ} (hc : 0 < c) :
    IsERMSolution data (c • q) G ↔ IsERMSolution data q G := by
  unfold IsERMSolution
  constructor
  · intro h G'
    have h' := h G'
    rw [weightedLoss_smul_frequency, weightedLoss_smul_frequency] at h'
    nlinarith
  · intro h G'
    have h' := h G'
    rw [weightedLoss_smul_frequency, weightedLoss_smul_frequency]
    nlinarith

/-- **T-Support (weak form)**: if `q i = 0`, event `i` contributes
    nothing to the weighted loss.

    Cognitive content: events that the learner has not experienced
    (`q i = 0`) cannot update the trained lexicon. Novel words and
    pseudowords don't retroactively modify the production map; they
    can only be processed by the existing `D.production` (which is
    polymorphic over the entire meaning space, hence applies to any
    meaning vector — but the trained map's coefficients reflect
    only the support of `q`). -/
theorem weightedLoss_zero_event_drops
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) (i₀ : Fin m) (h : q i₀ = 0) :
    weightedLoss data q G =
      weightedLoss data (Function.update q i₀ 0) G := by
  unfold weightedLoss
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = i₀
  · subst hi; rw [h, Function.update_self]
  · rw [Function.update_of_ne hi]

/-- **Definitional equivalence**: an `IsELSolution` is exactly an ERM
    solution under uniform weights. Paper-canonical: paper §3.1 of
    [gahl-baayen-2024] introduces EL as the special case of FIL
    with `Q = I`. Here `uniformFrequency = fun _ => 1` is the discrete
    analogue. -/
theorem isELSolution_eq_isERM_uniform
    (data : TrainingExperience m n d)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    IsELSolution data G ↔ IsERMSolution data (uniformFrequency m) G :=
  Iff.rfl

end TrainingSubstrate

-- ============================================================================
-- §5: Connection to LinearDiscriminativeLexicon
-- ============================================================================

/-- A `LinearDiscriminativeLexicon`'s production map is the
    **trained** production map for given training data and
    frequency weights iff the production map is an ERM solution.

    The substrate is agnostic about which `q` is empirically
    correct; this predicate just records the relationship between
    a DLM's production map and a particular cognitive theory's
    training data. -/
def LinearDiscriminativeLexicon.IsTrainedOn
    {m n d : ℕ}
    (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (data : TrainingExperience m n d) (q : FrequencyVector m) : Prop :=
  IsERMSolution data q D.production

/-- A DLM is **EL-trained** for given data iff its production map is
    the type-uniform ERM solution. -/
abbrev LinearDiscriminativeLexicon.IsELTrainedOn
    {m n d : ℕ}
    (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (data : TrainingExperience m n d) : Prop :=
  D.IsTrainedOn data (uniformFrequency m)

/-- A DLM is **FIL-trained** with a given frequency vector iff its
    production map is the corresponding ERM solution. -/
abbrev LinearDiscriminativeLexicon.IsFILTrainedOn
    {m n d : ℕ}
    (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (data : TrainingExperience m n d) (q : FrequencyVector m) : Prop :=
  D.IsTrainedOn data q

end Processing.Lexical.Discriminative
