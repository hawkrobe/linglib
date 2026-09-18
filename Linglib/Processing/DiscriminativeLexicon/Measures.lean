import Linglib.Processing.DiscriminativeLexicon.Defs
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Semantic support in the discriminative lexicon

This file defines the semantic support measures of a linear discriminative lexicon at its
matrix carriers.

A linear discriminative lexicon predicts the form of a meaning `s` through a mapping matrix `G`
acting on row vectors, `ĉ = sG`. The *semantic support* that a form vector `c` receives from `s`
is the dot product `ĉ ⬝ᵥ c` of the predicted form with `c`. Since this is linear in `s` and in
`c`, it is the bilinear form of `G`, and we bundle it as a bilinear map. Gahl and Baayen tabulate
it over all pairs of words as the support matrix `T = ĈCᵀ` and call its diagonal, the support a
word's own cue vector receives from its meaning, *semantic support for form*; Heitmeier, Chuang
and Baayen use the same measure for lexical decision. Saito, Tomaschek and Baayen instead read
off single coordinates of `ĉ`, the support for one cue, and sum them over a word's cues.

## Main definitions

* `Linear.productionMatrix D`: the mapping matrix of the production map, so that
  `D.production s = s ᵥ* D.productionMatrix`.
* `Linear.semanticSupport D`: the bilinear map `(s, c) ↦ D.production s ⬝ᵥ c`.

## Main results

* `toMatrix₂'_semanticSupport`: the matrix of the support form is the production matrix.
* `semanticSupport_single`: the support for a single coordinate is the predicted value there.

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

/-- The mapping matrix `G` of the production map acts on row vectors, so that the predicted form
of a meaning `s` is `sG`. -/
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

/-- The **semantic support** that a form vector `c` receives from a meaning `s` is the dot
product `sG ⬝ᵥ c` of the predicted form with `c`, the bilinear form of the production matrix. At
a word's own cue indicator this is the semantic support for form of Gahl and Baayen and the
`SemSupWord` of Saito, Tomaschek and Baayen; at a single coordinate indicator it is the predicted
value there, their per-cue `SemSup` (`semanticSupport_single`). -/
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
