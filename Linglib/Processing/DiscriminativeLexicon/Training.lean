import Linglib.Core.Analysis.LeastSquares
import Linglib.Processing.DiscriminativeLexicon.Measures
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# DLM training: endstate and frequency-informed learning

A DLM is trained by solving `SG = C` in the least-squares sense: the mapping matrix `G` minimises
the frequency-weighted loss `∑ᵢ qᵢ ‖(SG − C)ᵢ‖²` over the semantic matrix `S` and form matrix `C`
of the training experience. The weights are the cognitive commitment, uniform for endstate
learning (EL) and token counts for frequency-informed learning (FIL,
[heitmeier-chuang-axen-baayen-2024]); the optimisation is fixed. The loss separates over form
coordinates, so each column of `G` is a vector least-squares problem for the `√Q`-scaled design
`√Q S`, where Mathlib characterises the minimisers by the adjoint (`Core.IsLeastSquares`). That
gives the normal equations `SᵀQ(SG − C) = 0` of [gahl-baayen-2024]'s appendix and their closed
form `(SᵀQS)⁻¹SᵀQC`, existence, uniqueness of the fitted values `SG` (hence of `semSup` at
experienced meanings), the solution coset, and the identification of FIL under `q` with EL on the
`√Q`-premultiplied experience ([heitmeier-2024]).

## Main declarations

* `TrainingExperience`, `FrequencyVector`, `weightedLoss`, `IsTrained`, `IsELTrained`.
* `isTrained_iff_forall_isLeastSquares`, `exists_isTrained`: training is columnwise least
  squares, and solutions exist.
* `isTrained_iff`, `isTrained_closedForm`: the normal equations `SᵀQ(SG − C) = 0` and their
  closed form.
* `IsTrained.mul_eq`, `IsTrained.vecMul_eq_of_mem_span`, `IsTrained.exists_vecMul_ne`,
  `existsUnique_isTrained_iff`: fitted values are unique exactly on the span of experience.
* `isELTrained_sqrtScale_iff`: FIL under `q` is EL on `TrainingExperience.sqrtScale`.
* `Linear.IsTrainedOn` and the `semSup` transfer theorems.

## References

* [S. Gahl and R. H. Baayen, *Time and thyme again* (2024)][gahl-baayen-2024]
* [M. Heitmeier, *Mappings in the Discriminative Lexicon Model* (2024)][heitmeier-2024]
* [M. Heitmeier, Y.-Y. Chuang, S. D. Axen and R. H. Baayen, *Frequency effects in linear
  discriminative learning* (2024)][heitmeier-chuang-axen-baayen-2024]
* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
-/

namespace DiscriminativeLexicon

noncomputable section

open Matrix NNReal

variable {m n d : ℕ}

/-! ### The training problem -/

/-- A **training experience**: the papers' semantic matrix `S` and form matrix `C`, one usage
event per row. -/
structure TrainingExperience (numEvents formDim meaningDim : ℕ) where
  /-- The semantic matrix: the experienced meanings as rows. -/
  S : Matrix (Fin numEvents) (Fin meaningDim) ℝ
  /-- The form matrix: the observed forms as rows. -/
  C : Matrix (Fin numEvents) (Fin formDim) ℝ

/-- A **frequency vector** weights each usage event, the diagonal of the papers' `Q`. Uniform
weights give EL, token counts FIL ([gahl-baayen-2024]'s appendix, which warns against
log-transforming them). -/
abbrev FrequencyVector (numEvents : ℕ) : Type := Fin numEvents → ℝ≥0

variable (data : TrainingExperience m n d) (q : FrequencyVector m) (G : Matrix (Fin d) (Fin n) ℝ)

/-- The weight matrix `Q`. -/
def FrequencyVector.Q : Matrix (Fin m) (Fin m) ℝ := diagonal fun i => (q i : ℝ)

/-- Its square root, the `√Q` of the papers' appendix. -/
def FrequencyVector.sqrtQ : Matrix (Fin m) (Fin m) ℝ := diagonal fun i => √(q i : ℝ)

@[simp] theorem FrequencyVector.Q_one : (1 : FrequencyVector m).Q = 1 := by
  simp [FrequencyVector.Q]

@[simp] theorem FrequencyVector.sqrtQ_one : (1 : FrequencyVector m).sqrtQ = 1 := by
  simp [FrequencyVector.sqrtQ]

@[simp] theorem FrequencyVector.sqrtQ_transpose : q.sqrtQᵀ = q.sqrtQ := diagonal_transpose _

theorem FrequencyVector.sqrtQ_mul_sqrtQ : q.sqrtQ * q.sqrtQ = q.Q := by
  simp [FrequencyVector.sqrtQ, FrequencyVector.Q, diagonal_mul_diagonal, Real.mul_self_sqrt]

/-- The `√Q`-premultiplied experience `(√Q S, √Q C)` of the papers' appendix. -/
def TrainingExperience.sqrtScale : TrainingExperience m n d := ⟨q.sqrtQ * data.S, q.sqrtQ * data.C⟩

@[simp] theorem TrainingExperience.sqrtScale_S (i : Fin m) :
    (data.sqrtScale q).S i = √(q i : ℝ) • data.S i := by
  funext k; simp [TrainingExperience.sqrtScale, FrequencyVector.sqrtQ, diagonal_mul]

@[simp] theorem TrainingExperience.sqrtScale_C (i : Fin m) :
    (data.sqrtScale q).C i = √(q i : ℝ) • data.C i := by
  funext j; simp [TrainingExperience.sqrtScale, FrequencyVector.sqrtQ, diagonal_mul]

/-- The **frequency-weighted training loss** `∑ᵢ qᵢ ‖(SG − C)ᵢ‖²`. -/
def weightedLoss : ℝ :=
  ∑ i, q i * ((data.S * G - data.C) i ⬝ᵥ (data.S * G - data.C) i)

theorem weightedLoss_nonneg : 0 ≤ weightedLoss data q G :=
  Finset.sum_nonneg fun i _ => mul_nonneg (q i).2 (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)

/-- Under positive weights the loss vanishes exactly on interpolating maps. -/
theorem weightedLoss_eq_zero_iff (hq : ∀ i, 0 < q i) :
    weightedLoss data q G = 0 ↔ data.S * G = data.C := by
  constructor
  · intro h0
    ext i j
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_nonneg (q k).2 (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)).1 h0 i
      (Finset.mem_univ i)
    have hrow := dotProduct_self_eq_zero.1
      ((mul_eq_zero.1 hterm).resolve_left (NNReal.coe_pos.2 (hq i)).ne')
    simpa [sub_eq_zero] using congrFun hrow j
  · intro h
    simp [weightedLoss, h, dotProduct]

/-- `G` is **trained** on `data` under `q` when it minimises the weighted loss over all mapping
matrices: `SG = C` solved by least squares. -/
def IsTrained : Prop := IsMinOn (weightedLoss data q) Set.univ G

/-- **Endstate learning**: training under uniform weights ([gahl-baayen-2024] appendix). -/
abbrev IsELTrained : Prop := IsTrained data 1 G

theorem weightedLoss_smul (c : ℝ≥0) :
    weightedLoss data (c • q) G = c * weightedLoss data q G := by
  simp [weightedLoss, Finset.mul_sum, mul_assoc]

/-- Only relative frequencies matter. -/
theorem isTrained_smul_iff {c : ℝ≥0} (hc : 0 < c) :
    IsTrained data (c • q) G ↔ IsTrained data q G := by
  simp only [IsTrained, isMinOn_univ_iff, weightedLoss_smul,
    mul_le_mul_iff_right₀ (NNReal.coe_pos.2 hc)]

/-- The uniform-weight loss on the `√Q`-premultiplied experience is the `q`-weighted loss. -/
theorem weightedLoss_sqrtScale :
    weightedLoss (data.sqrtScale q) 1 G = weightedLoss data q G := by
  unfold weightedLoss
  refine Finset.sum_congr rfl fun i _ => ?_
  have hrow : ((data.sqrtScale q).S * G - (data.sqrtScale q).C) i =
      √(q i : ℝ) • (data.S * G - data.C) i := by
    show (data.sqrtScale q).S i ᵥ* G - (data.sqrtScale q).C i =
      √(q i : ℝ) • (data.S i ᵥ* G - data.C i)
    rw [TrainingExperience.sqrtScale_S, TrainingExperience.sqrtScale_C, smul_vecMul, smul_sub]
  rw [hrow, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  simp [← mul_assoc, Real.mul_self_sqrt (q i).coe_nonneg]

/-- FIL under `q` is exactly EL on the `√Q`-premultiplied experience: [heitmeier-2024]'s FIL–EL
equivalence, invertibility-free. -/
theorem isELTrained_sqrtScale_iff : IsELTrained (data.sqrtScale q) G ↔ IsTrained data q G := by
  have h : weightedLoss (data.sqrtScale q) 1 = weightedLoss data q :=
    funext fun G => weightedLoss_sqrtScale data q G
  simp only [IsELTrained, IsTrained, h]

/-! ### Training as columnwise least squares

The loss separates over form coordinates: column `j` of `G` is a least-squares solution of the
`√Q`-scaled regression of column `j` of `C` on `S`, a vector problem in Euclidean space. -/

private theorem col_mul {l : ℕ} (A : Matrix (Fin m) (Fin l) ℝ) (B : Matrix (Fin l) (Fin n) ℝ)
    (j : Fin n) : (A * B)ᵀ j = A *ᵥ Bᵀ j := by
  funext i; simp [mul_apply, mulVec, dotProduct]

private theorem col_sub (A B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    (A - B)ᵀ j = Aᵀ j - Bᵀ j := rfl

/-- The weighted loss is the sum over form coordinates of the columns' squared residuals. -/
theorem weightedLoss_eq_sum_norm_sq :
    weightedLoss data q G = ∑ j, ‖WithLp.toLp 2 ((q.sqrtQ * data.C)ᵀ j) -
      toEuclideanLin (q.sqrtQ * data.S) (WithLp.toLp 2 (Gᵀ j))‖ ^ 2 := by
  simp only [toLpLin_toLp, toLin'_apply, ← WithLp.toLp_sub, EuclideanSpace.norm_sq_eq,
    Pi.sub_apply, Real.norm_eq_abs, sq_abs, ← col_mul, transpose_apply, Matrix.mul_assoc,
    FrequencyVector.sqrtQ, diagonal_mul]
  rw [Finset.sum_comm]
  unfold weightedLoss dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.sub_apply]
  linear_combination -(data.C i j - (data.S * G) i j) ^ 2 * Real.mul_self_sqrt (q i).coe_nonneg

/-- Minimising a separable finite sum over a product is minimising each term. -/
private theorem sum_min_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    (g : ∀ i, β i → ℝ) (x : ∀ i, β i) :
    (∀ y : ∀ i, β i, ∑ i, g i (x i) ≤ ∑ i, g i (y i)) ↔ ∀ i, ∀ b : β i, g i (x i) ≤ g i b := by
  refine ⟨fun h i b => ?_, fun h y => Finset.sum_le_sum fun i _ => h i (y i)⟩
  have hy := h (Function.update x i b)
  simp_rw [Function.apply_update (fun j => g j) x i b] at hy
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), Finset.erase_eq] at hy
  linarith

/-- Training is columnwise least squares: each column of `G` minimises the residual of the
corresponding scaled regression. -/
theorem isTrained_iff_forall_isLeastSquares :
    IsTrained data q G ↔ ∀ j, Core.IsLeastSquares (toEuclideanLin (q.sqrtQ * data.S))
      (WithLp.toLp 2 ((q.sqrtQ * data.C)ᵀ j)) (WithLp.toLp 2 (Gᵀ j)) := by
  have key := sum_min_iff (fun j v => ‖WithLp.toLp 2 ((q.sqrtQ * data.C)ᵀ j) -
    toEuclideanLin (q.sqrtQ * data.S) (WithLp.toLp 2 v)‖ ^ 2) Gᵀ
  simp only [IsTrained, Core.IsLeastSquares, isMinOn_univ_iff, weightedLoss_eq_sum_norm_sq]
  refine ⟨fun h j z => ?_,
    fun h G' => key.2 (fun j v => pow_le_pow_left₀ (norm_nonneg _) (h j _) 2) G'ᵀ⟩
  have := key.1 (fun y => h yᵀ) j z.ofLp
  simpa using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

/-- Trained mapping matrices exist. -/
theorem exists_isTrained : ∃ G, IsTrained data q G := by
  choose x hx using fun j => Core.exists_isLeastSquares (A := toEuclideanLin (q.sqrtQ * data.S))
    (b := WithLp.toLp 2 ((q.sqrtQ * data.C)ᵀ j))
  exact ⟨Matrix.of fun k j => (x j).ofLp k, (isTrained_iff_forall_isLeastSquares _ _ _).2 hx⟩

/-! ### The normal equations -/

/-- **Normal equations**: `G` is trained iff `SᵀQ(SG − C) = 0` ([gahl-baayen-2024] (A2), (A4)),
from Mathlib's adjoint characterisation of least squares, column by column. -/
theorem isTrained_iff : IsTrained data q G ↔ data.Sᵀ * q.Q * (data.S * G - data.C) = 0 := by
  have hcol : ∀ j, Core.IsLeastSquares (toEuclideanLin (q.sqrtQ * data.S))
      (WithLp.toLp 2 ((q.sqrtQ * data.C)ᵀ j)) (WithLp.toLp 2 (Gᵀ j)) ↔
      ((q.sqrtQ * data.S)ᵀ * (q.sqrtQ * data.C - q.sqrtQ * data.S * G))ᵀ j = 0 := fun j => by
    rw [Core.isLeastSquares_iff_adjoint_eq_zero, ← toEuclideanLin_conjTranspose_eq_adjoint,
      conjTranspose_eq_transpose_of_trivial]
    simp only [toLpLin_toLp, toLin'_apply, ← WithLp.toLp_sub, WithLp.toLp_eq_zero, ← col_mul,
      ← col_sub]
  have hX : (q.sqrtQ * data.S)ᵀ * (q.sqrtQ * data.C - q.sqrtQ * data.S * G) =
      -(data.Sᵀ * q.Q * (data.S * G - data.C)) := by
    rw [transpose_mul, FrequencyVector.sqrtQ_transpose, Matrix.mul_assoc q.sqrtQ,
      ← Matrix.mul_sub, Matrix.mul_assoc, ← Matrix.mul_assoc q.sqrtQ,
      FrequencyVector.sqrtQ_mul_sqrtQ, ← Matrix.mul_assoc, ← neg_sub (data.S * G) data.C,
      Matrix.mul_neg]
  rw [isTrained_iff_forall_isLeastSquares]
  simp only [hcol]
  rw [hX, ← neg_eq_zero (a := data.Sᵀ * q.Q * (data.S * G - data.C)), ← transpose_eq_zero]
  exact ⟨funext, fun h j => congrFun h j⟩

/-- **Closed form**: when `SᵀQS` is invertible, `G = (SᵀQS)⁻¹SᵀQC` is trained
([gahl-baayen-2024] (A2), (A4)). -/
theorem isTrained_closedForm (hS : IsUnit (data.Sᵀ * q.Q * data.S)) :
    IsTrained data q ((data.Sᵀ * q.Q * data.S)⁻¹ * (data.Sᵀ * q.Q * data.C)) := by
  rw [isTrained_iff, Matrix.mul_sub, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 hS), sub_self]

/-- The endstate closed form `G = (SᵀS)⁻¹SᵀC` ([gahl-baayen-2024] (A2)). -/
theorem isELTrained_closedForm (hS : IsUnit (data.Sᵀ * data.S)) :
    IsELTrained data ((data.Sᵀ * data.S)⁻¹ * (data.Sᵀ * data.C)) := by
  simpa only [FrequencyVector.Q_one, Matrix.mul_one] using
    isTrained_closedForm data 1 (by simpa using hS)

variable {data q G}

/-- The normal equations in vector form: the `q`-weighted residual rows, weighted further by any
linear functional of the meanings, sum to zero. -/
theorem IsTrained.sum_smul_sub_eq_zero (hG : IsTrained data q G) (w : MeaningVec d →ₗ[ℝ] ℝ) :
    ∑ i, (q i * w (data.S i)) • ((data.S * G) i - data.C i) = 0 := by
  rw [isTrained_iff] at hG
  funext j
  have hw : ∀ i, w (data.S i) = ∑ k, data.S i k * w (fun j => if k = j then 1 else 0) :=
    fun i => by rw [w.pi_apply_eq_sum_univ]; simp only [smul_eq_mul]
  have hk : ∀ k, ∑ i, (q i : ℝ) * (data.S i k * ((data.S * G) i j - data.C i j)) = 0 :=
    fun k => by
    have := congrFun (congrFun hG k) j
    rw [mul_apply] at this
    simp only [FrequencyVector.Q, mul_diagonal, transpose_apply, Matrix.zero_apply,
      Matrix.sub_apply] at this
    exact (Finset.sum_congr rfl fun i _ => by ring).trans this
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hw, Finset.sum_mul,
    Finset.mul_sum, Pi.zero_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  calc _ = (∑ i, (q i : ℝ) * (data.S i k * ((data.S * G) i j - data.C i j))) *
          w (fun j => if k = j then 1 else 0) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [hk k, zero_mul]

/-! ### Fitted values -/

/-- All trained matrices under positive weights produce the same predicted forms `SG` on the
training events: fitted values are unique even when `G` is not. -/
theorem IsTrained.mul_eq (hq : ∀ i, 0 < q i) {G' : Matrix (Fin d) (Fin n) ℝ}
    (hG : IsTrained data q G) (hG' : IsTrained data q G') : data.S * G = data.S * G' := by
  rw [isTrained_iff_forall_isLeastSquares] at hG hG'
  ext i j
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin m) => v.ofLp i) ((hG j).map_eq (hG' j))
  simp only [toLpLin_toLp, toLin'_apply, WithLp.ofLp_toLp, ← col_mul, transpose_apply,
    Matrix.mul_assoc, FrequencyVector.sqrtQ, diagonal_mul] at h
  exact mul_left_cancel₀ (Real.sqrt_pos.2 (NNReal.coe_pos.2 (hq i))).ne' h

/-- Trained matrices agree at every meaning in the span of the experienced ones. -/
theorem IsTrained.vecMul_eq_of_mem_span (hq : ∀ i, 0 < q i) {G' : Matrix (Fin d) (Fin n) ℝ}
    (hG : IsTrained data q G) (hG' : IsTrained data q G') {s : MeaningVec d}
    (hs : s ∈ Submodule.span ℝ (Set.range data.S)) : s ᵥ* G = s ᵥ* G' := by
  have hker : Submodule.span ℝ (Set.range data.S) ≤ LinearMap.ker (toLin' (G - G')ᵀ) :=
    Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun i => by
      simp only [SetLike.mem_coe, LinearMap.mem_ker, toLin'_apply, mulVec_transpose,
        Matrix.vecMul_sub, sub_eq_zero]
      exact congrFun (hG.mul_eq hq hG') i
  have h0 := hker hs
  rw [LinearMap.mem_ker, toLin'_apply, mulVec_transpose, Matrix.vecMul_sub, sub_eq_zero] at h0
  exact h0

/-- Adding a matrix that annihilates every training meaning preserves training. -/
theorem IsTrained.add_of_mul_eq_zero (hG : IsTrained data q G) {H : Matrix (Fin d) (Fin n) ℝ}
    (hH : data.S * H = 0) : IsTrained data q (G + H) := by
  have : weightedLoss data q (G + H) = weightedLoss data q G := by
    simp [weightedLoss, Matrix.mul_add, hH]
  simpa only [IsTrained, isMinOn_univ_iff, this] using hG

/-- Off the span of experienced meanings, training is underdetermined: any trained matrix can be
modified into another with a different prediction at an unexperienced meaning. -/
theorem IsTrained.exists_vecMul_ne [NeZero n] (hG : IsTrained data q G) {s : MeaningVec d}
    (hs : s ∉ Submodule.span ℝ (Set.range data.S)) :
    ∃ G' : Matrix (Fin d) (Fin n) ℝ, IsTrained data q G' ∧ s ᵥ* G ≠ s ᵥ* G' := by
  obtain ⟨φ, hφ, hφs⟩ : ∃ φ ∈ (Submodule.span ℝ (Set.range data.S)).dualAnnihilator, φ s ≠ 0 := by
    have h := mt (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ s).mp hs
    push Not at h
    exact h
  set H : Matrix (Fin d) (Fin n) ℝ :=
    vecMulVec (fun k => φ fun j => if k = j then 1 else 0) (Pi.single 0 1) with hH
  have hvec (v : MeaningVec d) : v ᵥ* H = φ v • Pi.single 0 1 := by
    rw [hH, vecMul_vecMulVec, φ.pi_apply_eq_sum_univ v]; rfl
  have hSH : data.S * H = 0 := funext fun i => by
    show data.S i ᵥ* H = 0
    rw [hvec, (Submodule.mem_dualAnnihilator φ).1 hφ _ (Submodule.subset_span ⟨i, rfl⟩),
      zero_smul]
  exact ⟨G + H, hG.add_of_mul_eq_zero hSH,
    fun h => hφs (by simpa [Matrix.vecMul_add, hvec] using h.symm)⟩

/-- The trained matrix is uniquely determined exactly when the experienced meanings span the
meaning space: the coordinate-free form of the papers' full-column-rank condition on the
closed-form solution ([gahl-baayen-2024] appendix; [heitmeier-2024]). -/
theorem existsUnique_isTrained_iff [NeZero n] (hq : ∀ i, 0 < q i) :
    (∃! G : Matrix (Fin d) (Fin n) ℝ, IsTrained data q G) ↔
      Submodule.span ℝ (Set.range data.S) = ⊤ := by
  constructor
  · rintro ⟨G, hG, huniq⟩
    by_contra hne
    obtain ⟨s, hs⟩ : ∃ s, s ∉ Submodule.span ℝ (Set.range data.S) := by
      by_contra hall
      push Not at hall
      exact hne (Submodule.eq_top_iff'.mpr hall)
    obtain ⟨G', hG', hne'⟩ := hG.exists_vecMul_ne hs
    exact hne' (by rw [huniq G' hG'])
  · intro htop
    obtain ⟨G, hG⟩ := exists_isTrained data q
    refine ⟨G, hG, fun G' hG' => ?_⟩
    ext k j
    have := congrFun (hG'.vecMul_eq_of_mem_span hq hG (Submodule.eq_top_iff'.mp htop
      (Pi.single k 1))) j
    simpa [Matrix.single_one_vecMul] using this

/-- If some linear functional of the meanings reproduces column `j₀` of the observed forms
exactly, so does every trained matrix under positive weights, on every training event. -/
theorem IsTrained.mul_apply_eq_of_decodable (hq : ∀ i, 0 < q i) (hG : IsTrained data q G)
    {j₀ : Fin n} {w : MeaningVec d →ₗ[ℝ] ℝ} (hw : ∀ i, w (data.S i) = data.C i j₀) (i : Fin m) :
    (data.S * G) i j₀ = data.C i j₀ := by
  set v : Fin d → ℝ := fun k => w (fun j => if k = j then 1 else 0)
  have hSv : data.S *ᵥ v = data.Cᵀ j₀ := by
    funext i'
    rw [transpose_apply, ← hw i', w.pi_apply_eq_sum_univ]
    simp [mulVec, dotProduct, v]
  have hls : Core.IsLeastSquares (toEuclideanLin (q.sqrtQ * data.S))
      (WithLp.toLp 2 ((q.sqrtQ * data.C)ᵀ j₀)) (WithLp.toLp 2 v) :=
    Core.isLeastSquares_of_map_eq (by
      rw [toLpLin_toLp, toLin'_apply, ← mulVec_mulVec, hSv, ← col_mul])
  have h := congrArg (fun u : EuclideanSpace ℝ (Fin m) => u.ofLp i)
    (((isTrained_iff_forall_isLeastSquares data q G).1 hG j₀).map_eq hls)
  simp only [toLpLin_toLp, toLin'_apply, WithLp.ofLp_toLp] at h
  rw [← mulVec_mulVec, ← mulVec_mulVec, hSv, FrequencyVector.sqrtQ, mulVec_diagonal,
    mulVec_diagonal, ← col_mul, transpose_apply, transpose_apply] at h
  exact mul_left_cancel₀ (Real.sqrt_pos.2 (NNReal.coe_pos.2 (hq i))).ne' h

/-! ### Trained lexicons -/

namespace Linear

variable (D : Linear ℝ (FormVec n) (MeaningVec d)) (data) (q)

/-- The mapping matrix of the production map, acting on row vectors: `ĉ = sG`. -/
def productionMatrix : Matrix (Fin d) (Fin n) ℝ := (LinearMap.toMatrix' D.production)ᵀ

theorem production_eq_vecMul (s : MeaningVec d) : D.production s = s ᵥ* D.productionMatrix := by
  rw [productionMatrix, vecMul_transpose, ← toLin'_apply, toLin'_toMatrix']

/-- Row `i` of the fitted forms is the production map at the `i`-th experienced meaning. -/
theorem mul_productionMatrix_apply (i : Fin m) :
    (data.S * D.productionMatrix) i = D.production (data.S i) :=
  (D.production_eq_vecMul _).symm

@[simp] theorem productionMatrix_mk (F : FormVec n →ₗ[ℝ] MeaningVec d)
    (G : Matrix (Fin d) (Fin n) ℝ) : (Linear.mk F (toLin' Gᵀ)).productionMatrix = G := by
  simp [productionMatrix]

/-- `D` is **trained on** `data` under weights `q` if its production matrix is. Only the
production side is constrained, as in the papers' production models. -/
def IsTrainedOn : Prop := IsTrained data q D.productionMatrix

/-- A DLM is **EL-trained** on `data` iff its production matrix is trained under uniform weights. -/
abbrev IsELTrainedOn : Prop := D.IsTrainedOn data 1

variable {D data q}

/-- A trained DLM's semantic support at a linearly decodable form coordinate equals the observed
form value on every training event. -/
theorem IsTrainedOn.semSup_eq_of_decodable (hD : D.IsTrainedOn data q) (hq : ∀ i, 0 < q i)
    {j₀ : Fin n} {w : MeaningVec d →ₗ[ℝ] ℝ} (hw : ∀ i, w (data.S i) = data.C i j₀) (i : Fin m) :
    semSup D (data.S i) j₀ = data.C i j₀ := by
  rw [semSup, ← mul_productionMatrix_apply]
  exact IsTrained.mul_apply_eq_of_decodable hq hD hw i

/-- Two DLMs trained on the same experience and weights have identical semantic support at every
experienced meaning: `semSup` is a property of the training experience, not of the particular
trained matrix. -/
theorem IsTrainedOn.semSup_eq {D' : Linear ℝ (FormVec n) (MeaningVec d)}
    (hD : D.IsTrainedOn data q) (hD' : D'.IsTrainedOn data q) (hq : ∀ i, 0 < q i) (i : Fin m)
    (j : Fin n) : semSup D (data.S i) j = semSup D' (data.S i) j := by
  rw [semSup, semSup, ← mul_productionMatrix_apply, ← mul_productionMatrix_apply,
    IsTrained.mul_eq hq hD hD']

/-- `semSup` is well-defined at novel meanings in the span of experienced ones. -/
theorem IsTrainedOn.semSup_eq_of_mem_span {D' : Linear ℝ (FormVec n) (MeaningVec d)}
    (hD : D.IsTrainedOn data q) (hD' : D'.IsTrainedOn data q) (hq : ∀ i, 0 < q i)
    {s : MeaningVec d} (hs : s ∈ Submodule.span ℝ (Set.range data.S)) (j : Fin n) :
    semSup D s j = semSup D' s j := by
  rw [semSup, semSup, production_eq_vecMul, production_eq_vecMul,
    IsTrained.vecMul_eq_of_mem_span hq hD hD' hs]

/-- *Semantic Support for Form* ([gahl-baayen-2024] appendix) at a form vector equals the
observed form's own support whenever each coordinate the form vector touches is linearly
decodable from the meanings. -/
theorem IsTrainedOn.semSupWord_eq_of_decodable (hD : D.IsTrainedOn data q) (hq : ∀ i, 0 < q i)
    {c : FormVec n}
    (hw : ∀ j, c j ≠ 0 → ∃ w : MeaningVec d →ₗ[ℝ] ℝ, ∀ i, w (data.S i) = data.C i j)
    (i : Fin m) : semSupWord D (data.S i) c = data.C i ⬝ᵥ c := by
  unfold semSupWord dotProduct
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : c j = 0
  · simp [hc]
  · obtain ⟨w, hwj⟩ := hw j hc
    rw [show D.production (data.S i) j = semSup D (data.S i) j from rfl,
      hD.semSup_eq_of_decodable hq hwj i]

end Linear

end

end DiscriminativeLexicon
