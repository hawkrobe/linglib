import Linglib.Processing.Lexical.Discriminative.Defs
import Linglib.Processing.Lexical.Discriminative.Measures
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# DLM training: endstate vs frequency-informed learning
[baayen-2019] [gahl-baayen-2024] [heitmeier-chuang-baayen-2026]

What counts as a learned production map: the optimization characterization
of EndState Learning (EL) and Frequency-Informed Learning (FIL). The
cognitive theory choice IS the choice of frequency weights `q`; the
optimization — minimise the weighted squared loss — is fixed across
theories. `FrequencyVector` is [gahl-baayen-2024]'s diagonal `Q`
(appendix §A1.3); [heitmeier-chuang-baayen-2026] (ch. 6) introduces the
same device with max-normalised entries applied as `√P` premultiplication
of both `S` and `C` — `ermSolution_iff_rescaled` connects the two forms.

## Main declarations

* `TrainingExperience`, `FrequencyVector`, `weightedLoss`,
  `IsERMSolution` — data, weights, loss, and minimiser Prop;
  `IsELSolution` / `IsFILSolution` are the uniform and
  frequency-weighted cases.
* `ermSolution_iff_rescaled` — **T-Rescaling**: ERM solutions are
  invariant under positive rescaling of `q`; corollaries
  `isERMSolution_normalize_iff` / `isERMSolution_of_same_normalize` cast
  this as "only the empirical distribution `q.normalize` matters",
  the bridge for comparisons against probabilistic word-learning models.
* `weightedLoss_zero_event_drops` — **T-Support**: unexperienced
  events cannot update the lexicon.
* `coordResidual`, `weightedLoss_eq_sum_coordResidual` —
  **T-Separability**: the loss is a sum of per-coordinate regression
  residuals.
* `isERMSolution_iff_coordResidual` — **T-Coordinate-optimality**:
  ERM = columnwise-unbeatable regression; no sign condition on `q`.
* `IsERMSolution.coord_eq_of_decodable` — **T-Decodable-exact-fit**:
  an exactly decodable form coordinate is reproduced exactly under
  positive weights; corollaries `IsTrainedOn.semSup_eq_of_decodable`
  and `semSupWord_eq_of_decodable` transfer this to the semantic-
  support measures — the architectural core of
  [saito-tomaschek-baayen-2025]'s inflectional-status finding.
* `isERMSolution_of_interpolates` — **T-Interpolation**:
  interpolating maps are ERM, so `IsERMSolution` is nonvacuous on
  interpolable data.
* `TrainingExperience.sqrtScale`, `isELSolution_sqrtScale_iff` —
  **T-Sqrt-transport**: FIL under `q` is EL on the `√q`-premultiplied
  experience — the [gahl-baayen-2024]-appendix `√Q` construction, whose
  equivalence with frequency-replicated data is
  [heitmeier-chuang-baayen-2026]'s.
* `exists_isERMSolution` — **T-Existence**: ERM solutions exist for any
  nonnegative weights, by the Hilbert projection theorem applied
  columnwise to the prediction subspace.

## Implementation notes

This is not generic regression formalization: the loss function is the
cognitive commitment ([gahl-baayen-2024] §3) and the frequency-weight
parameterisation is the cross-theory axis. `squaredDist` is the L²
kernel the quadratic loss uses, distinct from `Normed.lean`'s sup-norm
carrier structure. The PMF view of `q.normalize` is a derived bridge
(`PMF.ofRealWeightFn` in `Core.Probability.Constructions`).

## TODO

* Closed form `G = (SᵀS)⁻¹SᵀC` under full column rank
  ([heitmeier-chuang-baayen-2026] ch. 6; [gahl-baayen-2024] appendix)
  — a future `Training/ClosedForm.lean`.
* Iterative Widrow-Hoff convergence to the FIL solution.
* Approximate-decodability gap bounds for `semSup` (quantitative form
  of the Saito contrast).
-/

namespace Processing.Lexical.Discriminative

noncomputable section TrainingSubstrate

variable {m n d : ℕ}  -- m = numEvents, n = formDim, d = meaningDim

/-! ### Substrate types -/

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
    - `q i = log(#occurrences i)`: log-frequency learning (which
      [gahl-baayen-2024]'s appendix cautions distorts learning relative
      to incremental Widrow-Hoff)
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

/-! ### The weighted loss -/

/-- Squared coordinate-distance between two form vectors:
    `Σⱼ (a j - b j)²`. Direct formula, no normed-space machinery
    required. Distinct from the bare-Pi sup-norm in `Normed.lean`;
    here we want the L² (Frobenius) inner product structure on
    `Fin n → ℝ` that the paper's quadratic loss uses. -/
def squaredDist (a b : FormVec n) : ℝ :=
  ∑ j, (a j - b j) ^ 2

theorem squaredDist_self (a : FormVec n) : squaredDist a a = 0 :=
  Finset.sum_eq_zero fun _ _ => by rw [sub_self]; ring

theorem squaredDist_nonneg (a b : FormVec n) : 0 ≤ squaredDist a b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The **frequency-weighted training loss** for a candidate
    production map `G`:

    `weightedLoss data q G = Σᵢ qᵢ · ‖G(meaningsᵢ) − formsᵢ‖²`

    where `‖·‖²` is squared coordinate-distance (= squared Frobenius
    norm on the form-vector slot).

    The papers specify the mapping procedurally — premultiply `S` and `C`
    by `√Q` and solve the normal equations ([gahl-baayen-2024] appendix;
    [heitmeier-chuang-baayen-2026]); this loss is the standard variational
    characterisation of that procedure, connected to it by
    `weightedLoss_sqrtScale`. The cognitive commitment is at the level of
    this loss function: the learner minimises the per-event squared
    mismatch between produced and observed form vectors, weighted by
    frequency of occurrence. -/
def weightedLoss
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) : ℝ :=
  ∑ i, q i * squaredDist (G (data.meanings i)) (data.forms i)

theorem weightedLoss_nonneg
    (data : TrainingExperience m n d) {q : FrequencyVector m}
    (hq : ∀ i, 0 ≤ q i) (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    0 ≤ weightedLoss data q G :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hq k) (squaredDist_nonneg _ _)

/-! ### Solution Props: ERM, EL, FIL -/

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

/-! ### Structural theorems -/

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

/-! ### Per-coordinate residual optimality

The loss separates across form coordinates: each column of `G`
regresses one cue's support on the semantic dimensions, "optimal in
the least-squares sense" ([heitmeier-chuang-baayen-2026] ch. 6). So
ERM is exactly columnwise unbeatability, and a coordinate that some
functional decodes exactly is reproduced exactly. -/

/-- Weighted squared residual of a predicted column `pred` against
    form coordinate `j₀` of the training data. -/
def coordResidual (data : TrainingExperience m n d) (q : FrequencyVector m)
    (pred : Fin m → ℝ) (j₀ : Fin n) : ℝ :=
  ∑ k, q k * (pred k - data.forms k j₀) ^ 2

theorem coordResidual_nonneg
    (data : TrainingExperience m n d) {q : FrequencyVector m}
    (hq : ∀ i, 0 ≤ q i) (pred : Fin m → ℝ) (j₀ : Fin n) :
    0 ≤ coordResidual data q pred j₀ :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hq k) (sq_nonneg _)

/-- **T-Separability**: the weighted loss is the sum over form
    coordinates of the per-coordinate residuals — each column of the
    production map is an independent regression. -/
theorem weightedLoss_eq_sum_coordResidual
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    weightedLoss data q G
      = ∑ j, coordResidual data q (fun k => G (data.meanings k) j) j := by
  unfold weightedLoss squaredDist coordResidual
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private theorem squaredDist_update (a b : FormVec n) (j₀ : Fin n) (x : ℝ) :
    squaredDist (Function.update a j₀ x) b
      = squaredDist a b - (a j₀ - b j₀) ^ 2 + (x - b j₀) ^ 2 := by
  unfold squaredDist
  rw [← Finset.add_sum_erase Finset.univ
        (fun j => (Function.update a j₀ x j - b j) ^ 2) (Finset.mem_univ j₀),
      ← Finset.add_sum_erase Finset.univ
        (fun j => (a j - b j) ^ 2) (Finset.mem_univ j₀),
      Finset.sum_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
  simp only [Function.update_self]
  ring

/-- **T-Coordinate-optimality**: `G` is an ERM solution iff at every form
    coordinate its column's residual is at most that of any linear
    functional of the meanings — ERM is columnwise-unbeatable regression.
    No sign condition on `q` in either direction. -/
theorem isERMSolution_iff_coordResidual
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    IsERMSolution data q G ↔
      ∀ (j₀ : Fin n) (w : MeaningVec d →ₗ[ℝ] ℝ),
        coordResidual data q (fun k => G (data.meanings k) j₀) j₀
          ≤ coordResidual data q (fun k => w (data.meanings k)) j₀ := by
  constructor
  · intro hG j₀ w
    -- the competitor: `G` with coordinate `j₀` replaced by `w`
    have happ : ∀ s,
        LinearMap.pi (Function.update (fun j => (LinearMap.proj j).comp G) j₀ w) s
          = Function.update (G s) j₀ (w s) := fun s => by
      funext j
      rcases eq_or_ne j j₀ with hj | hj
      · subst hj; simp only [LinearMap.pi_apply, Function.update_self]
      · simp only [LinearMap.pi_apply, Function.update_of_ne hj,
          LinearMap.comp_apply, LinearMap.proj_apply]
    have hloss : weightedLoss data q
          (LinearMap.pi (Function.update (fun j => (LinearMap.proj j).comp G) j₀ w))
        = weightedLoss data q G
          - coordResidual data q (fun k => G (data.meanings k) j₀) j₀
          + coordResidual data q (fun k => w (data.meanings k)) j₀ := by
      unfold weightedLoss coordResidual
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [happ, squaredDist_update]
      ring
    have h := hG (LinearMap.pi (Function.update (fun j => (LinearMap.proj j).comp G) j₀ w))
    rw [hloss] at h
    linarith
  · intro h G'
    rw [weightedLoss_eq_sum_coordResidual data q G,
      weightedLoss_eq_sum_coordResidual data q G']
    exact Finset.sum_le_sum fun j _ => h j ((LinearMap.proj j).comp G')

/-- **T-Decodable-exact-fit**: if some linear functional `w` of the meanings
    exactly reproduces coordinate `j₀` of the observed forms, then any ERM
    solution under positive weights also reproduces it exactly on the
    training events. Zero-residual case of `isERMSolution_iff_coordResidual`. -/
theorem IsERMSolution.coord_eq_of_decodable
    {data : TrainingExperience m n d} {q : FrequencyVector m} (hq : ∀ i, 0 < q i)
    {G : MeaningVec d →ₗ[ℝ] FormVec n} (hG : IsERMSolution data q G)
    {j₀ : Fin n} {w : MeaningVec d →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.meanings i) = data.forms i j₀) (i : Fin m) :
    G (data.meanings i) j₀ = data.forms i j₀ := by
  have hle := (isERMSolution_iff_coordResidual data q G).1 hG j₀ w
  have hB : coordResidual data q (fun k => w (data.meanings k)) j₀ = 0 :=
    Finset.sum_eq_zero fun k _ => by
      show q k * (w (data.meanings k) - data.forms k j₀) ^ 2 = 0
      rw [hw k, sub_self]; ring
  rw [hB] at hle
  have h0 : coordResidual data q (fun k => G (data.meanings k) j₀) j₀ = 0 :=
    le_antisymm hle (coordResidual_nonneg data (fun k => (hq k).le) _ _)
  have hnn : ∀ k ∈ Finset.univ,
      (0:ℝ) ≤ q k * (G (data.meanings k) j₀ - data.forms k j₀) ^ 2 :=
    fun k _ => mul_nonneg (hq k).le (sq_nonneg _)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 i (Finset.mem_univ i)
  have hsq : (G (data.meanings i) j₀ - data.forms i j₀) ^ 2 = 0 :=
    (mul_eq_zero.1 hterm).resolve_left (hq i).ne'
  exact sub_eq_zero.1 (sq_eq_zero_iff.1 hsq)

/-- **T-Interpolation**: a map that reproduces every training form exactly
    is an ERM solution under any nonnegative weights — `IsERMSolution` is
    nonvacuous whenever the data are linearly interpolable. -/
theorem isERMSolution_of_interpolates
    {data : TrainingExperience m n d} {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i)
    {G : MeaningVec d →ₗ[ℝ] FormVec n} (hG : ∀ i, G (data.meanings i) = data.forms i) :
    IsERMSolution data q G := fun G' => by
  have h0 : weightedLoss data q G = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hG k, squaredDist_self, mul_zero]
  rw [h0]
  exact weightedLoss_nonneg data hq G'

/-! ### Rescaling invariance

The "frequency-vector-as-counts" view (DLM-paper-faithful) and the
"frequency-vector-as-empirical-distribution" view (Bayesian-tradition) make
identical predictions about which production maps are ERM-optimal. For the
`PMF (Fin m)` cast of `q.normalize`, call `PMF.ofRealWeightFn` from
`Core.Probability.Constructions` directly. -/

/-- **Normalisation preserves ERM solutions.** A FrequencyVector and
    its empirical distribution agree on which production maps are ERM
    solutions. This is the formal statement that the cognitive content
    is in the *relative weights* (= the normalised distribution) and
    not in the absolute scale.

    Direct application of `ermSolution_iff_rescaled` with `c = 1/totalMass`. -/
theorem isERMSolution_normalize_iff
    (data : TrainingExperience m n d) (q : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) (h : 0 < q.totalMass) :
    IsERMSolution data q.normalize G ↔ IsERMSolution data q G := by
  have hinv : (0:ℝ) < (q.totalMass)⁻¹ := inv_pos.mpr h
  have hnorm : q.normalize = (q.totalMass)⁻¹ • q := by
    funext i
    show q i / q.totalMass = (q.totalMass)⁻¹ * q i
    rw [div_eq_inv_mul]
  rw [hnorm]
  exact ermSolution_iff_rescaled data q G hinv

/-- **Two FrequencyVectors with identical empirical distributions are
    ERM-equivalent.** The cognitive content lives at the level of the
    normalised distribution; theories that assign different absolute
    scales but the same relative frequencies make the same predictions. -/
theorem isERMSolution_of_same_normalize
    (data : TrainingExperience m n d) (q₁ q₂ : FrequencyVector m)
    (G : MeaningVec d →ₗ[ℝ] FormVec n)
    (h₁ : 0 < q₁.totalMass) (h₂ : 0 < q₂.totalMass)
    (hnorm : q₁.normalize = q₂.normalize) :
    IsERMSolution data q₁ G ↔ IsERMSolution data q₂ G := by
  rw [← isERMSolution_normalize_iff data q₁ G h₁,
      ← isERMSolution_normalize_iff data q₂ G h₂, hnorm]

/-! ### √Q transport and existence of ERM solutions

[gahl-baayen-2024]'s appendix computes EL from the normal equations of
regression and FIL by solving the EL problem on `√Q`-premultiplied `S` and
`C` matrices; [heitmeier-chuang-baayen-2026] gives the same construction, and
[heitmeier-2024] proves the equivalence with frequency-replicated training
data via the closed-form normal-equations solution, under invertibility.
Here the premultiplied experience is `TrainingExperience.sqrtScale`, the
equivalence (`isELSolution_sqrtScale_iff`) is stated invertibility-free at
the level of ERM solution sets, and ERM existence follows by orthogonal
projection onto the prediction subspace, columnwise. -/

/-- The `√q`-premultiplied training experience: event `i` scaled by
    `√(q i)` in both meaning and form — the `√Q`-premultiplication of `S`
    and `C` of [gahl-baayen-2024]'s appendix and
    [heitmeier-chuang-baayen-2026]. -/
def TrainingExperience.sqrtScale (data : TrainingExperience m n d)
    (q : FrequencyVector m) : TrainingExperience m n d where
  meanings i := Real.sqrt (q i) • data.meanings i
  forms i := Real.sqrt (q i) • data.forms i

theorem squaredDist_smul (c : ℝ) (a b : FormVec n) :
    squaredDist (c • a) (c • b) = c ^ 2 * squaredDist a b := by
  unfold squaredDist
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- **T-Sqrt-transport** (loss level): the uniform-weight loss on the
    `√q`-premultiplied experience is the `q`-weighted loss on the original. -/
theorem weightedLoss_sqrtScale (data : TrainingExperience m n d)
    {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    weightedLoss (data.sqrtScale q) (uniformFrequency m) G
      = weightedLoss data q G := by
  unfold weightedLoss
  refine Finset.sum_congr rfl fun i _ => ?_
  show 1 * squaredDist (G (Real.sqrt (q i) • data.meanings i))
        (Real.sqrt (q i) • data.forms i) = _
  rw [one_mul, map_smul, squaredDist_smul, Real.sq_sqrt (hq i)]

/-- **T-Sqrt-transport**: FIL under `q` is exactly EL on the
    `√q`-premultiplied experience — [heitmeier-2024]'s FIL-EL equivalence,
    invertibility-free. -/
theorem isELSolution_sqrtScale_iff (data : TrainingExperience m n d)
    {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    IsELSolution (data.sqrtScale q) G ↔ IsERMSolution data q G := by
  unfold IsELSolution IsERMSolution
  exact forall_congr' fun G' => by
    rw [weightedLoss_sqrtScale data hq, weightedLoss_sqrtScale data hq]

private theorem coordResidual_uniform_eq_norm_sq (data : TrainingExperience m n d)
    (pred : Fin m → ℝ) (j : Fin n) :
    coordResidual data (uniformFrequency m) pred j
      = ‖WithLp.toLp 2 (fun k => data.forms k j)
          - WithLp.toLp 2 pred‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold coordResidual
  refine Finset.sum_congr rfl fun k _ => ?_
  show 1 * (pred k - data.forms k j) ^ 2 = _
  rw [one_mul, ← WithLp.toLp_sub]
  simp only [Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  ring

private theorem exists_forall_coordResidual_le (data : TrainingExperience m n d)
    (j : Fin n) :
    ∃ w : MeaningVec d →ₗ[ℝ] ℝ, ∀ w' : MeaningVec d →ₗ[ℝ] ℝ,
      coordResidual data (uniformFrequency m) (fun k => w (data.meanings k)) j
        ≤ coordResidual data (uniformFrequency m) (fun k => w' (data.meanings k)) j := by
  classical
  -- prediction subspace: range of the evaluation map into Euclidean event space
  set Ev : (MeaningVec d →ₗ[ℝ] ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap.comp
      (LinearMap.pi fun k => LinearMap.applyₗ (data.meanings k)) with hEv
  set y : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun k => data.forms k j) with hy
  haveI : CompleteSpace ↥(LinearMap.range Ev) := FiniteDimensional.complete ℝ _
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp ((LinearMap.range Ev).starProjection_apply_mem y)
  refine ⟨w, fun w' => ?_⟩
  have hmin : ∀ v : ↥(LinearMap.range Ev),
      ‖y - (LinearMap.range Ev).starProjection y‖ ≤ ‖y - ↑v‖ := fun v => by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, by rintro r ⟨x, rfl⟩; exact norm_nonneg _⟩ v
  have hle : ‖y - Ev w‖ ≤ ‖y - Ev w'‖ := by
    rw [hw]
    exact hmin ⟨Ev w', LinearMap.mem_range_self _ _⟩
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hEvw : ∀ v : MeaningVec d →ₗ[ℝ] ℝ,
      Ev v = WithLp.toLp 2 (fun k => v (data.meanings k)) := fun _ => rfl
  rw [coordResidual_uniform_eq_norm_sq, coordResidual_uniform_eq_norm_sq]
  rw [hEvw w, hEvw w', hy] at hsq
  exact hsq

/-- **T-EL-existence**: endstate solutions exist — the normal-equations
    solvability of [gahl-baayen-2024]'s appendix, by orthogonal projection
    of each observed form column onto the prediction subspace. -/
theorem exists_isELSolution (data : TrainingExperience m n d) :
    ∃ G : MeaningVec d →ₗ[ℝ] FormVec n, IsELSolution data G := by
  choose w hw using exists_forall_coordResidual_le data
  refine ⟨LinearMap.pi w, (isERMSolution_iff_coordResidual _ _ _).mpr fun j w' => ?_⟩
  simpa only [LinearMap.pi_apply] using hw j w'

/-- **T-Existence**: ERM solutions exist for any nonnegative frequency
    vector, via `exists_isELSolution` on the `√q`-premultiplied experience. -/
theorem exists_isERMSolution (data : TrainingExperience m n d)
    {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i) :
    ∃ G, IsERMSolution data q G :=
  let ⟨G, hG⟩ := exists_isELSolution (data.sqrtScale q)
  ⟨G, (isELSolution_sqrtScale_iff data hq G).mp hG⟩

end TrainingSubstrate

/-! ### Connection to `LinearDiscriminativeLexicon` -/

section Connection

variable {m n d : ℕ}

/-- A `LinearDiscriminativeLexicon`'s production map is the
    **trained** production map for given training data and
    frequency weights iff the production map is an ERM solution.

    The substrate is agnostic about which `q` is empirically
    correct; this predicate just records the relationship between
    a DLM's production map and a particular cognitive theory's
    training data. -/
def LinearDiscriminativeLexicon.IsTrainedOn
    (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (data : TrainingExperience m n d) (q : FrequencyVector m) : Prop :=
  IsERMSolution data q D.production

/-- A DLM is **EL-trained** for given data iff its production map is
    the type-uniform ERM solution. -/
abbrev LinearDiscriminativeLexicon.IsELTrainedOn
    (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (data : TrainingExperience m n d) : Prop :=
  D.IsTrainedOn data (uniformFrequency m)

/-- A DLM is **FIL-trained** with a given frequency vector iff its
    production map is the corresponding ERM solution. -/
abbrev LinearDiscriminativeLexicon.IsFILTrainedOn
    (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (data : TrainingExperience m n d) (q : FrequencyVector m) : Prop :=
  D.IsTrainedOn data q

variable {D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d)}
  {data : TrainingExperience m n d} {q : FrequencyVector m}

/-- A trained DLM's semantic support at a linearly decodable form coordinate
    equals the observed form value on every positively-weighted training
    event; any contrast carried by that coordinate — categorical or graded —
    transfers to `semSup` exactly. -/
theorem LinearDiscriminativeLexicon.IsTrainedOn.semSup_eq_of_decodable
    (hD : D.IsTrainedOn data q) (hq : ∀ i, 0 < q i)
    {j₀ : Fin n} {w : MeaningVec d →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.meanings i) = data.forms i j₀) (i : Fin m) :
    semSup D (data.meanings i) j₀ = data.forms i j₀ :=
  IsERMSolution.coord_eq_of_decodable hq hD hw i

/-- [heitmeier-chuang-baayen-2026]'s *Semantic Support for Form* — `semSupWord`
    over a word's cue coordinates — equals the sum of the observed form values
    whenever each coordinate is linearly decodable from the meanings. -/
theorem LinearDiscriminativeLexicon.IsTrainedOn.semSupWord_eq_of_decodable
    (hD : D.IsTrainedOn data q) (hq : ∀ i, 0 < q i)
    {js : List (Fin n)}
    (hw : ∀ j ∈ js, ∃ w : MeaningVec d →ₗ[ℝ] ℝ,
      ∀ i, w (data.meanings i) = data.forms i j)
    (i : Fin m) :
    semSupWord D (data.meanings i) js = (js.map fun j => data.forms i j).sum := by
  unfold semSupWord
  congr 1
  refine List.map_congr_left fun j hj => ?_
  obtain ⟨w, hwj⟩ := hw j hj
  exact hD.semSup_eq_of_decodable hq hwj i

end Connection

end Processing.Lexical.Discriminative
