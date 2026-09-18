import Linglib.Processing.DiscriminativeLexicon.Defs
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Semantic support in the discriminative lexicon

At the `Fin`-indexed carriers the production map is a mapping matrix `G` acting on row vectors,
`ĉ = sG`, and the papers' **semantic support** measures are read off the predicted form `ĉ`: the
support a form vector `c` receives from a meaning `s` is `ĉ ⬝ᵥ c`, the bilinear form of `G`. At a
word's own cue indicator this is the diagonal of [gahl-baayen-2024]'s support matrix `T = ĈCᵀ`,
their *semantic support for form*, which [heitmeier-chuang-baayen-2026] carry over to lexical
decision; at a coordinate indicator it is the predicted value `ĉⱼ`, the per-cue `SemSup` of
[saito-tomaschek-baayen-2025], whose `SemSupWord` sums it over a word's own cues.

## Main declarations

- `Linear.productionMatrix D`: the mapping matrix of the production map, with
  `D.production s = s ᵥ* D.productionMatrix` (`production_eq_vecMul`).
- `Linear.semanticSupport D`: the support bilinear form `(s, c) ↦ D.production s ⬝ᵥ c`. Its
  matrix is the production matrix (`toMatrix₂'_semanticSupport`); linearity in each argument is
  the `LinearMap` API, and `semanticSupport_single` reads off a single coordinate.

## References

* [S. Gahl and R. H. Baayen, *Time and thyme again* (2024)][gahl-baayen-2024]
* [M. Saito, F. Tomaschek and R. H. Baayen, *Interaction of frequency and inflectional status*
  (2025)][saito-tomaschek-baayen-2025]
* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
-/

namespace DiscriminativeLexicon.Linear

open Matrix

noncomputable section

variable {n d : ℕ} (D : Linear ℝ (FormVec n) (MeaningVec d))

/-! ### The production matrix -/

/-- The mapping matrix `G` of the production map, acting on row vectors: `ĉ = sG`. -/
def productionMatrix : Matrix (Fin d) (Fin n) ℝ := (LinearMap.toMatrix' D.production)ᵀ

@[simp] theorem productionMatrix_apply (i : Fin d) (j : Fin n) :
    D.productionMatrix i j = D.production (Pi.single i 1) j := by
  simp [productionMatrix]

theorem production_eq_vecMul (s : MeaningVec d) : D.production s = s ᵥ* D.productionMatrix := by
  rw [productionMatrix, vecMul_transpose, ← toLin'_apply, toLin'_toMatrix']

@[simp] theorem productionMatrix_mk (F : FormVec n →ₗ[ℝ] MeaningVec d)
    (G : Matrix (Fin d) (Fin n) ℝ) : (Linear.mk F (toLin' Gᵀ)).productionMatrix = G := by
  simp [productionMatrix]

/-! ### Semantic support -/

/-- **Semantic support**: the bilinear form of the production matrix, pairing the form predicted
from a meaning `s` with a form vector `c`, `sG ⬝ᵥ c`. At a word's own cue indicator this is
[gahl-baayen-2024]'s *semantic support for form* and [saito-tomaschek-baayen-2025]'s
`SemSupWord`; at a coordinate indicator it is the predicted value there, their per-cue `SemSup`
(`semanticSupport_single`). -/
def semanticSupport : MeaningVec d →ₗ[ℝ] FormVec n →ₗ[ℝ] ℝ :=
  Matrix.toLinearMap₂' ℝ D.productionMatrix

@[simp] theorem semanticSupport_apply (s : MeaningVec d) (c : FormVec n) :
    D.semanticSupport s c = D.production s ⬝ᵥ c := by
  rw [semanticSupport, toLinearMap₂'_apply', dotProduct_mulVec, production_eq_vecMul]

@[simp] theorem toMatrix₂'_semanticSupport :
    LinearMap.toMatrix₂' ℝ D.semanticSupport = D.productionMatrix :=
  LinearEquiv.apply_symm_apply _ _

/-- The support for a single form coordinate is the predicted value there. -/
theorem semanticSupport_single (s : MeaningVec d) (j : Fin n) :
    D.semanticSupport s (Pi.single j 1) = D.production s j := by
  simp

end

end DiscriminativeLexicon.Linear
