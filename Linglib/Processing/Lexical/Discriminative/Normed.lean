import Linglib.Processing.Lexical.Discriminative.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# DLM in normed carriers — Lipschitz continuity and approximate isomorphism
[baayen-2019] [chuang-bell-tseng-baayen-2026] [lu-chuang-baayen-2026]
[heitmeier-chuang-baayen-2026]

Sibling to `Defs.lean`. Introduces the **normed-carrier** layer of the
DLM substrate: when the form and meaning carriers are finite-dimensional
real normed vector spaces, the production and comprehension maps are
automatically continuous (mathlib's `LinearMap.toContinuousLinearMap`),
and we can talk about their operator norms, Lipschitz constants, and
approximate-inverse properties.

## Why this is the substantive substrate layer

The `Defs.lean` substrate characterises only **exact** form identity: two
meanings surface identically iff their difference lies in the production
map's kernel (`LinearDiscriminativeLexicon.production_eq_iff`).

The headline empirical claim of [chuang-bell-tseng-baayen-2026]
(predictions iii / iv) and [lu-chuang-baayen-2026] (paper §4 form-
meaning isomorphism) is **quantitative**: that the form space and
meaning space exhibit *measurable* isomorphism — cosine similarity 0.93,
Pearson correlation 0.98 between GAMM-derived gold-standard contours
and DLM-predicted contours (Lu §4.4). That quantitative content needs
**norms** to state.

This file provides the structural primitives:

- `dlm_lipschitz_production` — the production map is Lipschitz with
  constant `‖production‖` (its operator norm). One-line proof from
  `ContinuousLinearMap.le_opNorm`.
- `dlm_neighbor_centroids_imply_neighbor_contours` — quantitative form
  of the "centroid neighbours → contour neighbours" claim: if two
  meaning vectors are within ε, their forms are within `‖production‖ * ε`.
- `IsMeaningApproxIso` / `IsFormApproxIso` — definitional forms of
  approximate inverse pairs, capturing the form-meaning isomorphism
  finding as a structural property of the round-trip composition.

## Carrier requirements

Theorems are polymorphic over normed carriers `F`, `M` with
`[NormedAddCommGroup]` + `[NormedSpace ℝ ·]` instances. Lipschitz
theorems additionally require the **source** of the relevant linear map
to be `[FiniteDimensional ℝ ·]` (so mathlib's `toContinuousLinearMap`
applies). For our concrete consumer carriers:

- `Fin n → ℝ` — `Pi.normedAddCommGroup` (sup norm),
  `Module.Finite ℝ (Fin n → ℝ)` automatic.
- `EuclideanSpace ℝ (Fin n)` — L² norm, finite-dim automatic.

Choice of carrier determines which norm appears in the operator-norm
bound. Studies that need the L² (Euclidean) norm — e.g. for cosine-
similarity statements — should use `EuclideanSpace`. The bare-Pi sup
norm suffices for direction-of-effect arguments (kernel proximity →
contour proximity).
-/

namespace Processing.Lexical.Discriminative

/-! ### Lipschitz continuity of the production map -/

section Lipschitz

variable {F M : Type*}
  [NormedAddCommGroup F] [NormedAddCommGroup M]
  [NormedSpace ℝ F] [NormedSpace ℝ M]

/-- **Lipschitz continuity of production.** For any
    `LinearDiscriminativeLexicon` over real finite-dimensional normed
    carriers, the production map sends meaning differences to form
    differences bounded by `‖production‖ * ‖meaning difference‖`.

    This is the headline normed-substrate theorem. It captures
    structurally what the consumer papers report empirically: that
    "centroid neighbours yield contour neighbours" in the trained DLM.
    The empirical claim is that the operator norm of the trained
    production map is small enough to make this bound informative on
    real data; the structural capacity for the bound is established here.

    Derived from `map_sub` + `ContinuousLinearMap.le_opNorm`. -/
theorem dlm_lipschitz_production
    [FiniteDimensional ℝ M]
    (D : LinearDiscriminativeLexicon ℝ F M) (e₁ e₂ : M) :
    ‖D.production e₁ - D.production e₂‖ ≤
      ‖D.production.toContinuousLinearMap‖ * ‖e₁ - e₂‖ := by
  rw [← map_sub]
  exact D.production.toContinuousLinearMap.le_opNorm _

/-- **Lipschitz continuity of comprehension** — dual of
    `dlm_lipschitz_production` for the form → meaning direction. -/
theorem dlm_lipschitz_comprehension
    [FiniteDimensional ℝ F]
    (D : LinearDiscriminativeLexicon ℝ F M) (f₁ f₂ : F) :
    ‖D.comprehension f₁ - D.comprehension f₂‖ ≤
      ‖D.comprehension.toContinuousLinearMap‖ * ‖f₁ - f₂‖ := by
  rw [← map_sub]
  exact D.comprehension.toContinuousLinearMap.le_opNorm _

end Lipschitz

/-! ### Neighbor preservation -/

section NeighborPreservation

variable {F M : Type*}
  [NormedAddCommGroup F] [NormedAddCommGroup M]
  [NormedSpace ℝ F] [NormedSpace ℝ M]

/-- **Neighbor centroids → neighbor contours.** Quantitative form of
    the empirical observation in [chuang-bell-tseng-baayen-2026]
    Fig. 18 and [lu-chuang-baayen-2026] Fig. 9 that the DLM-
    predicted pitch contour from a tone-pattern centroid CE matches
    the GAMM-derived gold-standard contour for that pattern.

    The structural form: if two meaning vectors are within ε of each
    other, their production-images are within `‖production‖ * ε` of
    each other. The empirical content of the consumer papers is that
    this bound is *small* for real centroid pairs because the trained
    production map's operator norm is moderate.

    Specialises `dlm_lipschitz_production` to a fixed bound. -/
theorem dlm_neighbor_centroids_imply_neighbor_contours
    [FiniteDimensional ℝ M]
    (D : LinearDiscriminativeLexicon ℝ F M) {e₁ e₂ : M} {ε : ℝ}
    (h : ‖e₁ - e₂‖ ≤ ε) :
    ‖D.production e₁ - D.production e₂‖ ≤
      ‖D.production.toContinuousLinearMap‖ * ε :=
  (dlm_lipschitz_production D e₁ e₂).trans <|
    mul_le_mul_of_nonneg_left h (ContinuousLinearMap.opNorm_nonneg _)

end NeighborPreservation

/-! ### Approximate-inverse / form-meaning ε-isomorphism -/

section ApproximateInverse

variable {F M : Type*}
  [NormedAddCommGroup F] [NormedAddCommGroup M]
  [NormedSpace ℝ F] [NormedSpace ℝ M]

/-- **Meaning-side approximate isomorphism.** The DLM is an
    `ε`-approximate isomorphism on the meaning side if, for every
    meaning vector, the round-trip `comprehension ∘ production`
    returns within ε of the input.

    The empirical content of [chuang-bell-tseng-baayen-2026]
    predictions (iii) and (iv) — that the trained DLM predicts meaning
    from pitch above chance and pitch from meaning above chance — is
    the existence of a small ε for which the trained DLM satisfies
    this property. The structural definition is here; the empirical
    witness is paper-supplied. -/
def LinearDiscriminativeLexicon.IsMeaningApproxIso
    (D : LinearDiscriminativeLexicon ℝ F M) (ε : ℝ) : Prop :=
  ∀ e : M, ‖D.comprehension (D.production e) - e‖ ≤ ε

/-- **Form-side approximate isomorphism.** Dual to `IsMeaningApproxIso`:
    the round-trip `production ∘ comprehension` returns within ε of
    the input form vector. -/
def LinearDiscriminativeLexicon.IsFormApproxIso
    (D : LinearDiscriminativeLexicon ℝ F M) (ε : ℝ) : Prop :=
  ∀ f : F, ‖D.production (D.comprehension f) - f‖ ≤ ε

/-- The `ε = 0` case of `IsMeaningApproxIso` is **exact** isomorphism
    on the meaning side: comprehension is a left inverse of production. -/
theorem LinearDiscriminativeLexicon.isMeaningApproxIso_zero_iff
    (D : LinearDiscriminativeLexicon ℝ F M) :
    D.IsMeaningApproxIso 0 ↔ ∀ e : M, D.comprehension (D.production e) = e := by
  unfold LinearDiscriminativeLexicon.IsMeaningApproxIso
  refine ⟨fun h e => ?_, fun h e => ?_⟩
  · have hn : ‖D.comprehension (D.production e) - e‖ = 0 :=
      le_antisymm (h e) (norm_nonneg _)
    rwa [norm_eq_zero, sub_eq_zero] at hn
  · rw [h e, sub_self, norm_zero]

end ApproximateInverse

end Processing.Lexical.Discriminative
