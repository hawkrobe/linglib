module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Basic.Real.Basic

/-!
# The discriminative lexicon

This file defines the linear discriminative lexicon, the endstate of the Discriminative Lexicon
Model of Baayen, Chuang, Shafaei-Bajestan and Blevins.

The model relates form and meaning by learned mappings between vector spaces rather than by an
inventory of stored, decomposed form–meaning entries. At the endstate of learning it is a pair
of linear maps, a comprehension map from forms to meanings and a production map from meanings
to forms; Heitmeier, Chuang and Baayen fit them by least squares, which they call linear
discriminative learning, and the two maps are the model's entire lexicon. The kernel of the
production map is where the model neutralizes meanings, since two meanings surface as the same
form exactly when their difference lies in it (`LinearMap.sub_mem_ker_iff`). The deep
replacements for the linear maps, ResLDL and DDL, are not formalised.

## Main definitions

* `Linear R F M`: a comprehension map `F →ₗ[R] M` and a production map `M →ₗ[R] F`.
* `FormVec n`, `MeaningVec d`: the real coordinate vectors `Fin n → ℝ` and `Fin d → ℝ` on which
  the studies instantiate the model.

## References

* [R. H. Baayen, Y.-Y. Chuang, E. Shafaei-Bajestan and J. P. Blevins, *The discriminative
  lexicon* (2019)][baayen-2019]
* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
* [Y.-Y. Chuang, M. J. Bell, Y.-H. Tseng and R. H. Baayen, *Word-specific tonal realizations
  in Mandarin* (2026)][chuang-bell-tseng-baayen-2026]
* [M. Heitmeier, V. Schmidt, H. P. A. Lensch and R. H. Baayen, *Is deeper always better?*
  (2025)][heitmeier-schmidt-lensch-baayen-2025]
-/

@[expose] public section

namespace DiscriminativeLexicon

variable (R F M : Type*) [Semiring R] [AddCommMonoid F] [AddCommMonoid M] [Module R F]
  [Module R M]

/-- A **linear discriminative lexicon** consists of a comprehension map and a production map
between a form space and a meaning space, the endstate of linear discriminative learning
([heitmeier-chuang-baayen-2026]). -/
structure Linear where
  /-- The comprehension map sends forms to meanings; it is the papers' matrix `F` with `Ŝ = CF`. -/
  comprehension : F →ₗ[R] M
  /-- The production map sends meanings to forms; it is the papers' matrix `G` with `Ĉ = SG`. -/
  production : M →ₗ[R] F

/-- A **form vector** has `formDim` real coordinates. -/
abbrev FormVec (formDim : ℕ) : Type := Fin formDim → ℝ

/-- A **meaning vector** has `meaningDim` real coordinates. -/
abbrev MeaningVec (meaningDim : ℕ) : Type := Fin meaningDim → ℝ

end DiscriminativeLexicon
