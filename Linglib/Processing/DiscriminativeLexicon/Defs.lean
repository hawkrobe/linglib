import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Data.Real.Basic

/-!
# Discriminative Lexicon Model — linear substrate

The **Discriminative Lexicon Model** (DLM) is a theory of lexical processing in which form and
meaning are related by learned mappings between vector spaces rather than by an inventory of
stored, decomposed form–meaning entries ([baayen-2019]). At the endstate of learning the model
is a pair of linear maps — the papers' comprehension matrix `F` (`Ŝ = CF`) and production
matrix `G` (`Ĉ = SG`) — fitted by *linear discriminative learning*, the least-squares
estimation of [heitmeier-chuang-baayen-2026]. The two maps are the model's entire "lexicon".
The kernel of the production map is the DLM's **neutralization locus**: two meanings surface as
identical forms iff their difference lies in `LinearMap.ker D.production`
(`LinearMap.sub_mem_ker_iff`).

The deep replacements for the linear maps — ResLDL ([chuang-bell-tseng-baayen-2026]) and DDL
([heitmeier-schmidt-lensch-baayen-2025]) — are not formalised.

## Main declarations

- `Linear R F M`: a pair of linear maps between form and meaning carriers.
- `FormVec`, `MeaningVec`: `Fin n → ℝ` carriers for the studies' specialisations.

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

namespace DiscriminativeLexicon

variable (R F M : Type*) [Semiring R] [AddCommMonoid F] [AddCommMonoid M] [Module R F]
  [Module R M]

/-- The endstate of a **Discriminative Lexicon Model** with linear mappings: a comprehension
map and a production map between form and meaning carriers, fitted by linear discriminative
learning ([heitmeier-chuang-baayen-2026]). -/
structure Linear where
  /-- The form → meaning map — the papers' comprehension matrix `F` (`Ŝ = CF`). -/
  comprehension : F →ₗ[R] M
  /-- The meaning → form map — the papers' production matrix `G` (`Ĉ = SG`). -/
  production : M →ₗ[R] F

/-- A `formDim`-dimensional **form vector** over ℝ. -/
abbrev FormVec (formDim : ℕ) : Type := Fin formDim → ℝ

/-- A `meaningDim`-dimensional **meaning vector** over ℝ. -/
abbrev MeaningVec (meaningDim : ℕ) : Type := Fin meaningDim → ℝ

end DiscriminativeLexicon
