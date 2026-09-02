import Linglib.Core.Analysis.LeastSquares
import Linglib.Processing.DiscriminativeLexicon.Measures
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# DLM training: endstate and frequency-informed learning

The trained production map of a DLM minimises a frequency-weighted quadratic loss over the
training experience. The choice of weights is the cognitive commitment — uniform weights are
endstate learning (EL), token counts are frequency-informed learning (FIL,
[heitmeier-chuang-axen-baayen-2024]) — and the optimisation is fixed. Through the `√q`-scaled
design map the loss is a Euclidean least-squares residual, so `Core.IsLeastSquares` supplies the
theory: the normal equations `SᵀQ(SG − C) = 0` of [gahl-baayen-2024]'s appendix, existence of
solutions, uniqueness of fitted values (hence of `semSup` at experienced meanings), the
solution coset, and the identification of FIL under `q` with EL on the `√q`-premultiplied
experience ([heitmeier-2024]).

## Main declarations

* `TrainingExperience`, `FrequencyVector`, `weightedLoss`, `IsERMSolution`, `IsELSolution`.
* `isERMSolution_iff_isLeastSquares`, `exists_isERMSolution`.
* `isERMSolution_iff_inner_eq_zero`, `isERMSolution_iff_forall_coord`,
  `IsERMSolution.sum_smul_sub_eq_zero`: the normal equations, against every direction, in
  coordinates, and in vector form.
* `IsERMSolution.apply_meanings_eq`, `apply_eq_of_mem_span`, `exists_apply_ne`,
  `existsUnique_isERMSolution_iff`: fitted values are unique exactly on the span of experience.
* `isERMSolution_toLin'_transpose_iff`, `isERMSolution_closedForm`: the normal equations as
  `SᵀQ(SG − C) = 0` and their closed form `(SᵀQS)⁻¹SᵀQC`.
* `isELSolution_sqrtScale_iff`: FIL under `q` is EL on `TrainingExperience.sqrtScale`.
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

open Matrix NNReal RealInnerProductSpace

variable {m n d : ℕ}

/-! ### The training problem -/

/-- A **training experience**: a finite indexed family of (meaning, form) observation pairs, the
rows of the papers' `S` and `C` matrices. -/
structure TrainingExperience (numEvents formDim meaningDim : ℕ) where
  meanings : Fin numEvents → MeaningVec meaningDim
  forms : Fin numEvents → FormVec formDim

/-- A **frequency vector** weights each usage event — the diagonal of the papers' `Q`. Uniform
weights give EL, token counts FIL ([gahl-baayen-2024]'s appendix, which warns against
log-transforming them). -/
abbrev FrequencyVector (numEvents : ℕ) : Type := Fin numEvents → ℝ≥0

variable (data : TrainingExperience m n d) (q : FrequencyVector m)
  (G : MeaningVec d →ₗ[ℝ] FormVec n)

/-- The **frequency-weighted training loss** `∑ᵢ qᵢ ‖G sᵢ − cᵢ‖²`. -/
def weightedLoss : ℝ :=
  ∑ i, q i * ((G (data.meanings i) - data.forms i) ⬝ᵥ (G (data.meanings i) - data.forms i))

theorem weightedLoss_nonneg : 0 ≤ weightedLoss data q G :=
  Finset.sum_nonneg fun i _ => mul_nonneg (q i).2 (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)

/-- Under positive weights the loss vanishes exactly on interpolating maps. -/
theorem weightedLoss_eq_zero_iff (hq : ∀ i, 0 < q i) :
    weightedLoss data q G = 0 ↔ ∀ i, G (data.meanings i) = data.forms i := by
  constructor
  · intro h0 i
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_nonneg (q k).2 (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)).1 h0 i
      (Finset.mem_univ i)
    exact sub_eq_zero.1 <| dotProduct_self_eq_zero.1 <|
      (mul_eq_zero.1 hterm).resolve_left (NNReal.coe_pos.2 (hq i)).ne'
  · intro h
    simp [weightedLoss, h]

/-- `G` is an **empirical risk minimiser** (ERM) for `data` under `q`: no linear map achieves
a smaller weighted loss. -/
def IsERMSolution : Prop := IsMinOn (weightedLoss data q) Set.univ G

/-- An **endstate-learning** (EL) solution is an ERM solution under uniform weights
([gahl-baayen-2024] appendix). -/
abbrev IsELSolution : Prop := IsERMSolution data 1 G

/-- The weighted loss is linear in the frequency vector. -/
theorem weightedLoss_smul_frequency (c : ℝ≥0) :
    weightedLoss data (c • q) G = c * weightedLoss data q G := by
  simp [weightedLoss, Finset.mul_sum, mul_assoc]

/-- ERM solutions are invariant under positive rescaling of the frequency vector — only
relative frequencies matter. -/
theorem isERMSolution_iff_rescaled {c : ℝ≥0} (hc : 0 < c) :
    IsERMSolution data (c • q) G ↔ IsERMSolution data q G := by
  simp only [IsERMSolution, isMinOn_univ_iff, weightedLoss_smul_frequency,
    mul_le_mul_iff_right₀ (NNReal.coe_pos.2 hc)]

/-! ### Training as Euclidean least squares

The `√q`-scaled predictions of a production map are a point of Euclidean event-coordinate
space, and the weighted loss is the squared distance to the scaled observations; production
maps enter through their matrices. -/

/-- Production maps as points of Euclidean space, via their matrices. -/
def toEuclidean : (MeaningVec d →ₗ[ℝ] FormVec n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin d) :=
  LinearMap.toMatrix' ≪≫ₗ (LinearEquiv.curry ℝ ℝ (Fin n) (Fin d)).symm ≪≫ₗ
    (WithLp.linearEquiv 2 ℝ _).symm

@[simp] theorem toEuclidean_apply (p : Fin n × Fin d) :
    (toEuclidean G).ofLp p = G (Pi.single p.2 1) p.1 := rfl

/-- The `√q`-scaled **design map**: the scaled predictions `√qᵢ (G sᵢ)ⱼ` of the production map
with the given matrix. -/
def designMap : EuclideanSpace ℝ (Fin n × Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin n) :=
  ((WithLp.linearEquiv 2 ℝ _).symm.toLinearMap ∘ₗ
    LinearMap.pi fun p => (Real.sqrt (q p.1) : ℝ) •
      (LinearMap.proj p.2 ∘ₗ LinearMap.applyₗ (data.meanings p.1))) ∘ₗ
    toEuclidean.symm.toLinearMap

@[simp] theorem designMap_toEuclidean (p : Fin m × Fin n) :
    (designMap data q (toEuclidean G)).ofLp p = Real.sqrt (q p.1) * G (data.meanings p.1) p.2 := by
  simp [designMap]

/-- The `√q`-scaled observed forms. -/
def scaledTarget : EuclideanSpace ℝ (Fin m × Fin n) :=
  WithLp.toLp 2 fun p => Real.sqrt (q p.1) * data.forms p.1 p.2

/-- The weighted loss is the squared least-squares residual of the design map. -/
theorem weightedLoss_eq_norm_sq :
    weightedLoss data q G = ‖scaledTarget data q - designMap data q (toEuclidean G)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  unfold weightedLoss dotProduct
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.sub_apply, designMap_toEuclidean, scaledTarget, Real.norm_eq_abs, sq_abs,
    Pi.sub_apply]
  linear_combination
    -(G (data.meanings i) j - data.forms i j) ^ 2 * Real.mul_self_sqrt (q i).coe_nonneg

/-- ERM solutions are exactly the least-squares solutions of the design map: DLM training,
seen through `√q`-scaling, is weighted linear regression. -/
theorem isERMSolution_iff_isLeastSquares :
    IsERMSolution data q G ↔
      Core.IsLeastSquares (designMap data q) (scaledTarget data q) (toEuclidean G) := by
  simp only [IsERMSolution, Core.IsLeastSquares, isMinOn_univ_iff, weightedLoss_eq_norm_sq]
  refine ⟨fun h z => ?_, fun h G' => ?_⟩
  · have := h (toEuclidean.symm z)
    rw [LinearEquiv.apply_symm_apply] at this
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  · exact pow_le_pow_left₀ (norm_nonneg _) (h (toEuclidean G')) 2

/-- ERM solutions exist. -/
theorem exists_isERMSolution : ∃ G, IsERMSolution data q G :=
  let ⟨z, hz⟩ := Core.exists_isLeastSquares (A := designMap data q) (b := scaledTarget data q)
  ⟨toEuclidean.symm z, by rwa [isERMSolution_iff_isLeastSquares, LinearEquiv.apply_symm_apply]⟩

/-! ### The normal equations -/

variable {data q G}

private theorem inner_residual_designMap (H : MeaningVec d →ₗ[ℝ] FormVec n) :
    ⟪scaledTarget data q - designMap data q (toEuclidean G), designMap data q (toEuclidean H)⟫ =
      -∑ i, q i * ((G (data.meanings i) - data.forms i) ⬝ᵥ H (data.meanings i)) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold dotProduct
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.sub_apply, designMap_toEuclidean, scaledTarget, Pi.sub_apply, RCLike.inner_apply,
    conj_trivial]
  linear_combination (data.forms i j - G (data.meanings i) j) * H (data.meanings i) j *
    Real.mul_self_sqrt (q i).coe_nonneg

/-- **Normal equations**: `G` is an ERM solution iff its `q`-weighted residuals are orthogonal
to the predictions of every linear map — `SᵀQ(SG − C) = 0` with `Sᵀ`'s rows generalised to all
directions. -/
theorem isERMSolution_iff_inner_eq_zero :
    IsERMSolution data q G ↔ ∀ H : MeaningVec d →ₗ[ℝ] FormVec n,
      ∑ i, q i * ((G (data.meanings i) - data.forms i) ⬝ᵥ H (data.meanings i)) = 0 := by
  rw [isERMSolution_iff_isLeastSquares, Core.isLeastSquares_iff_inner_eq_zero]
  refine ⟨fun h H => ?_, fun h y => ?_⟩
  · simpa [inner_residual_designMap] using h (toEuclidean H)
  · obtain ⟨H, rfl⟩ := toEuclidean.surjective y
    rw [inner_residual_designMap, h H, neg_zero]

/-- The normal equations in coordinates, `SᵀQ(SG − C) = 0` entrywise: at every form coordinate
`j` the `q`-weighted residual column is orthogonal to every meaning coordinate `k`. -/
theorem isERMSolution_iff_forall_coord :
    IsERMSolution data q G ↔ ∀ (j : Fin n) (k : Fin d),
      ∑ i, q i * ((G (data.meanings i) j - data.forms i j) * data.meanings i k) = 0 := by
  rw [isERMSolution_iff_inner_eq_zero]
  constructor
  · intro h j k
    simpa [dotProduct_single, mul_comm, mul_left_comm] using
      h ((LinearMap.proj k).smulRight (Pi.single j 1))
  · intro h H
    have hH : ∀ i, q i * ((G (data.meanings i) - data.forms i) ⬝ᵥ H (data.meanings i)) =
        ∑ j, ∑ k, q i * ((G (data.meanings i) j - data.forms i j) * data.meanings i k) *
          H (fun j => if k = j then 1 else 0) j := fun i => by
      have hx : H (data.meanings i) =
          ∑ k, data.meanings i k • H (fun j => if k = j then 1 else 0) :=
        H.pi_apply_eq_sum_univ _
      unfold dotProduct
      rw [hx, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_apply, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by
        simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]; ring
    simp_rw [hH]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.sum_mul, h j k, zero_mul]

/-- The normal equations in vector form: the `q`-weighted residuals, weighted further by any
linear functional of the meanings, sum to zero. -/
theorem IsERMSolution.sum_smul_sub_eq_zero (hG : IsERMSolution data q G)
    (w : MeaningVec d →ₗ[ℝ] ℝ) :
    ∑ i, (q i * w (data.meanings i)) • (G (data.meanings i) - data.forms i) = 0 := by
  funext j
  have h := isERMSolution_iff_inner_eq_zero.1 hG (w.smulRight (Pi.single j 1))
  simpa [dotProduct_smul, dotProduct_single, Finset.sum_apply, mul_assoc, mul_comm,
    mul_left_comm] using h

/-! ### Fitted values -/

/-- All ERM solutions under positive weights produce the same predicted form at every
experienced meaning — fitted values are unique even when the ERM map is not. -/
theorem IsERMSolution.apply_meanings_eq (hq : ∀ i, 0 < q i)
    {G' : MeaningVec d →ₗ[ℝ] FormVec n}
    (hG : IsERMSolution data q G) (hG' : IsERMSolution data q G') (i : Fin m) :
    G (data.meanings i) = G' (data.meanings i) := by
  rw [isERMSolution_iff_isLeastSquares] at hG hG'
  funext j
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin m × Fin n) => v.ofLp (i, j)) (hG.map_eq hG')
  simp only [designMap_toEuclidean] at h
  exact mul_left_cancel₀ (Real.sqrt_pos.2 (NNReal.coe_pos.2 (hq i))).ne' h

/-- ERM solutions agree at every meaning in the span of the experienced ones. -/
theorem IsERMSolution.apply_eq_of_mem_span (hq : ∀ i, 0 < q i)
    {G' : MeaningVec d →ₗ[ℝ] FormVec n}
    (hG : IsERMSolution data q G) (hG' : IsERMSolution data q G')
    {s : MeaningVec d} (hs : s ∈ Submodule.span ℝ (Set.range data.meanings)) :
    G s = G' s := by
  have hker : Submodule.span ℝ (Set.range data.meanings) ≤ LinearMap.ker (G' - G) :=
    Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun i => by
      simp [LinearMap.mem_ker, (IsERMSolution.apply_meanings_eq hq hG hG' i).symm]
  have h0 := hker hs
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h0
  exact h0.symm

/-- Adding a map that vanishes on every training meaning preserves ERM. -/
theorem IsERMSolution.add_of_forall_eq_zero (hG : IsERMSolution data q G)
    {H : MeaningVec d →ₗ[ℝ] FormVec n} (hH : ∀ i, H (data.meanings i) = 0) :
    IsERMSolution data q (G + H) := by
  rw [isERMSolution_iff_isLeastSquares] at hG ⊢
  refine hG.iff_map_eq.mpr ?_
  rw [map_add, map_add, add_eq_left]
  exact (WithLp.ofLp_eq_zero 2).1 (funext fun p => by simp [hH])

/-- Off the span of experienced meanings, ERM solutions are underdetermined: any ERM solution
can be modified into another with a different prediction at an unexperienced meaning. -/
theorem IsERMSolution.exists_apply_ne [NeZero n] (hG : IsERMSolution data q G)
    {s : MeaningVec d} (hs : s ∉ Submodule.span ℝ (Set.range data.meanings)) :
    ∃ G' : MeaningVec d →ₗ[ℝ] FormVec n, IsERMSolution data q G' ∧ G s ≠ G' s := by
  obtain ⟨φ, hφ, hφs⟩ : ∃ φ ∈ (Submodule.span ℝ (Set.range data.meanings)).dualAnnihilator,
      φ s ≠ 0 := by
    have h := mt (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ s).mp hs
    push Not at h
    exact h
  refine ⟨G + φ.smulRight (Pi.single 0 1), hG.add_of_forall_eq_zero fun i => by
    simp [(Submodule.mem_dualAnnihilator φ).mp hφ _
      (Submodule.subset_span (Set.mem_range_self i))], fun h => ?_⟩
  have h0 := congrFun h (0 : Fin n)
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply,
    Pi.single_eq_same, smul_eq_mul, mul_one] at h0
  exact hφs (by linarith)

/-- The trained map is uniquely determined exactly when the experienced meanings span the
meaning space — the coordinate-free form of the papers' full-column-rank condition on the
closed-form solution ([gahl-baayen-2024] appendix; [heitmeier-2024]). -/
theorem existsUnique_isERMSolution_iff [NeZero n] (hq : ∀ i, 0 < q i) :
    (∃! G : MeaningVec d →ₗ[ℝ] FormVec n, IsERMSolution data q G) ↔
      Submodule.span ℝ (Set.range data.meanings) = ⊤ := by
  constructor
  · rintro ⟨G, hG, huniq⟩
    by_contra hne
    obtain ⟨s, hs⟩ : ∃ s, s ∉ Submodule.span ℝ (Set.range data.meanings) := by
      by_contra hall
      push Not at hall
      exact hne (Submodule.eq_top_iff'.mpr hall)
    obtain ⟨G', hG', hne'⟩ := hG.exists_apply_ne hs
    exact hne' (by rw [huniq G' hG'])
  · intro htop
    obtain ⟨G, hG⟩ := exists_isERMSolution data q
    exact ⟨G, hG, fun G' hG' => LinearMap.ext fun s =>
      IsERMSolution.apply_eq_of_mem_span hq hG' hG (Submodule.eq_top_iff'.mp htop s)⟩

/-- If some linear functional of the meanings reproduces coordinate `j₀` of the observed forms
exactly, so does every ERM solution under positive weights, on every training event. -/
theorem IsERMSolution.coord_eq_of_decodable (hq : ∀ i, 0 < q i) (hG : IsERMSolution data q G)
    {j₀ : Fin n} {w : MeaningVec d →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.meanings i) = data.forms i j₀) (i : Fin m) :
    G (data.meanings i) j₀ = data.forms i j₀ := by
  have h := (isERMSolution_iff_inner_eq_zero.1 hG)
    ((w - LinearMap.proj j₀ ∘ₗ G).smulRight (Pi.single j₀ 1))
  simp only [LinearMap.smulRight_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, dotProduct_smul, dotProduct_single, Pi.sub_apply, hw, smul_eq_mul,
    mul_one] at h
  have hterm : ∀ k ∈ Finset.univ, (q k : ℝ) * ((data.forms k j₀ - G (data.meanings k) j₀) *
      (G (data.meanings k) j₀ - data.forms k j₀)) ≤ 0 := fun k _ =>
    mul_nonpos_of_nonneg_of_nonpos (q k).2
      (by nlinarith [sq_nonneg (G (data.meanings k) j₀ - data.forms k j₀)])
  have hi := (Finset.sum_eq_zero_iff_of_nonpos hterm).1 h i (Finset.mem_univ i)
  rcases mul_eq_zero.1 hi with h0 | h0
  · exact absurd h0 (NNReal.coe_pos.2 (hq i)).ne'
  · rcases mul_eq_zero.1 h0 with h1 | h1
    · exact (sub_eq_zero.1 h1).symm
    · exact sub_eq_zero.1 h1

/-! ### The normal equations in matrix form

The papers state the training problem on matrices: the semantic matrix `S` and form matrix `C`
have the experienced meanings and forms as rows, the frequency vector is the diagonal of `Q`, and
a mapping matrix `G` acts on row vectors, `ĉ = sG`. The normal equations read `SᵀQ(SG − C) = 0`,
solved in closed form as `G = (SᵀQS)⁻¹SᵀQC` whenever `SᵀQS` is invertible ([gahl-baayen-2024]
(A2), (A4); [heitmeier-chuang-baayen-2026] §6.1, §6.3). -/

variable (data q)

/-- The semantic matrix `S`: the experienced meanings as rows. -/
def TrainingExperience.S : Matrix (Fin m) (Fin d) ℝ := Matrix.of fun i k => data.meanings i k

/-- The form matrix `C`: the observed forms as rows. -/
def TrainingExperience.C : Matrix (Fin m) (Fin n) ℝ := Matrix.of fun i j => data.forms i j

/-- The weight matrix `Q`: the frequency vector on the diagonal. -/
def FrequencyVector.Q : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal fun i => (q i : ℝ)

@[simp] theorem TrainingExperience.S_apply (i : Fin m) (k : Fin d) :
    data.S i k = data.meanings i k := rfl

@[simp] theorem TrainingExperience.C_apply (i : Fin m) (j : Fin n) : data.C i j = data.forms i j :=
  rfl

@[simp] theorem FrequencyVector.Q_one : (1 : FrequencyVector m).Q = 1 := by
  simp [FrequencyVector.Q]

/-- The normal equations as a matrix identity: a mapping matrix `G`, acting on row vectors, is
an ERM solution iff `SᵀQ(SG − C) = 0`. -/
theorem isERMSolution_toLin'_transpose_iff (G : Matrix (Fin d) (Fin n) ℝ) :
    IsERMSolution data q (Matrix.toLin' Gᵀ) ↔ data.Sᵀ * q.Q * (data.S * G - data.C) = 0 := by
  rw [isERMSolution_iff_forall_coord]
  have key : ∀ (j : Fin n) (k : Fin d), (data.Sᵀ * q.Q * (data.S * G - data.C)) k j =
      ∑ i, q i * ((Matrix.toLin' Gᵀ (data.meanings i) j - data.forms i j) * data.meanings i k) := by
    intro j k
    have hsum : ∀ i, Matrix.toLin' Gᵀ (data.meanings i) j = ∑ l, data.meanings i l * G l j :=
      fun i => by simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_comm]
    rw [Matrix.mul_apply]
    simp only [FrequencyVector.Q, Matrix.mul_diagonal, Matrix.transpose_apply,
      TrainingExperience.S_apply]
    simp only [Matrix.sub_apply, Matrix.mul_apply, TrainingExperience.S_apply,
      TrainingExperience.C_apply, hsum]
    exact Finset.sum_congr rfl fun i _ => by ring
  constructor
  · intro h
    ext k j
    rw [key, h, Matrix.zero_apply]
  · intro h j k
    rw [← key, h, Matrix.zero_apply]

/-- **Closed form**: when `SᵀQS` is invertible, `G = (SᵀQS)⁻¹SᵀQC` solves the normal
equations ([gahl-baayen-2024] (A2), (A4)). -/
theorem isERMSolution_closedForm (hS : IsUnit (data.Sᵀ * q.Q * data.S)) :
    IsERMSolution data q
      (Matrix.toLin' ((data.Sᵀ * q.Q * data.S)⁻¹ * (data.Sᵀ * q.Q * data.C))ᵀ) := by
  rw [isERMSolution_toLin'_transpose_iff, Matrix.mul_sub, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 hS), sub_self]

/-- The endstate closed form `G = (SᵀS)⁻¹SᵀC` ([gahl-baayen-2024] (A2)). -/
theorem isELSolution_closedForm (hS : IsUnit (data.Sᵀ * data.S)) :
    IsELSolution data (Matrix.toLin' ((data.Sᵀ * data.S)⁻¹ * (data.Sᵀ * data.C))ᵀ) := by
  have := isERMSolution_closedForm data 1 (by simpa using hS)
  simpa [IsELSolution] using this

/-! ### √Q transport

[gahl-baayen-2024]'s appendix computes FIL by solving the EL problem on `√Q`-premultiplied `S`
and `C`; [heitmeier-2024] proves the equivalence with frequency-replicated data under
invertibility. Here it holds at the level of ERM solution sets. -/

/-- The `√q`-premultiplied training experience. -/
def TrainingExperience.sqrtScale : TrainingExperience m n d where
  meanings i := Real.sqrt (q i) • data.meanings i
  forms i := Real.sqrt (q i) • data.forms i

/-- The uniform-weight loss on the `√q`-premultiplied experience is the `q`-weighted loss. -/
theorem weightedLoss_sqrtScale :
    weightedLoss (data.sqrtScale q) 1 G = weightedLoss data q G := by
  unfold weightedLoss dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [TrainingExperience.sqrtScale, map_smul, ← smul_sub, Pi.smul_apply, smul_eq_mul,
    Pi.one_apply, NNReal.coe_one, one_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    linear_combination
      ((G (data.meanings i) - data.forms i) j) ^ 2 * Real.mul_self_sqrt (q i).coe_nonneg

/-- FIL under `q` is exactly EL on the `√q`-premultiplied experience — [heitmeier-2024]'s
FIL–EL equivalence, invertibility-free. -/
theorem isELSolution_sqrtScale_iff :
    IsELSolution (data.sqrtScale q) G ↔ IsERMSolution data q G := by
  have h : weightedLoss (data.sqrtScale q) 1 = weightedLoss data q :=
    funext fun G => weightedLoss_sqrtScale data q (G := G)
  simp only [IsELSolution, IsERMSolution, h]

end

/-! ### Trained lexicons -/

namespace Linear

variable {m n d : ℕ} (D : Linear ℝ (FormVec n) (MeaningVec d))
  (data : TrainingExperience m n d) (q : FrequencyVector m)

/-- `D` is **trained on** `data` under weights `q` if its production map is an ERM solution.
Only the production side is constrained, as in the papers' production models. -/
def IsTrainedOn : Prop := IsERMSolution data q D.production

/-- A DLM is **EL-trained** on `data` iff its production map is the uniform-weight ERM solution. -/
abbrev IsELTrainedOn : Prop := D.IsTrainedOn data 1

/-- A DLM is **FIL-trained** on `data` with weights `q` iff its production map is the
corresponding ERM solution. -/
abbrev IsFILTrainedOn : Prop := D.IsTrainedOn data q

variable {D data q}

/-- A trained DLM's semantic support at a linearly decodable form coordinate equals the observed
form value on every training event. -/
theorem IsTrainedOn.semSup_eq_of_decodable (hD : D.IsTrainedOn data q) (hq : ∀ i, 0 < q i)
    {j₀ : Fin n} {w : MeaningVec d →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.meanings i) = data.forms i j₀) (i : Fin m) :
    semSup D (data.meanings i) j₀ = data.forms i j₀ :=
  IsERMSolution.coord_eq_of_decodable hq hD hw i

/-- Two DLMs trained on the same experience and weights have identical semantic support at
every experienced meaning: `semSup` is a property of the training experience, not of the
particular ERM solution. -/
theorem IsTrainedOn.semSup_eq {D' : Linear ℝ (FormVec n) (MeaningVec d)}
    (hD : D.IsTrainedOn data q) (hD' : D'.IsTrainedOn data q) (hq : ∀ i, 0 < q i) (i : Fin m)
    (j : Fin n) : semSup D (data.meanings i) j = semSup D' (data.meanings i) j :=
  congrFun (IsERMSolution.apply_meanings_eq hq hD hD' i) j

/-- `semSup` is well-defined at novel meanings in the span of experienced ones. -/
theorem IsTrainedOn.semSup_eq_of_mem_span
    {D' : Linear ℝ (FormVec n) (MeaningVec d)}
    (hD : D.IsTrainedOn data q) (hD' : D'.IsTrainedOn data q) (hq : ∀ i, 0 < q i)
    {s : MeaningVec d} (hs : s ∈ Submodule.span ℝ (Set.range data.meanings)) (j : Fin n) :
    semSup D s j = semSup D' s j :=
  congrFun (IsERMSolution.apply_eq_of_mem_span hq hD hD' hs) j

/-- *Semantic Support for Form* ([gahl-baayen-2024] appendix) at a form vector equals the
observed form's own support whenever each coordinate the form vector touches is linearly
decodable from the meanings. -/
theorem IsTrainedOn.semSupWord_eq_of_decodable (hD : D.IsTrainedOn data q) (hq : ∀ i, 0 < q i)
    {c : FormVec n}
    (hw : ∀ j, c j ≠ 0 → ∃ w : MeaningVec d →ₗ[ℝ] ℝ, ∀ i, w (data.meanings i) = data.forms i j)
    (i : Fin m) :
    semSupWord D (data.meanings i) c = data.forms i ⬝ᵥ c := by
  unfold semSupWord dotProduct
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : c j = 0
  · simp [hc]
  · obtain ⟨w, hwj⟩ := hw j hc
    rw [show D.production (data.meanings i) j = semSup D (data.meanings i) j from rfl,
      hD.semSup_eq_of_decodable hq hwj i]

end Linear

end DiscriminativeLexicon
