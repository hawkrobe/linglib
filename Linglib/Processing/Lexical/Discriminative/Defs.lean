import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Real.Basic

/-!
# Discriminative Lexicon Model — linear substrate
[baayen-2019] [heitmeier-chuang-baayen-2026]
[chuang-bell-tseng-baayen-2026] [lu-chuang-baayen-2026]

The **Discriminative Lexicon Model** (DLM) is a theory of lexical processing in
which form ↔ meaning relations are learned mappings between vector spaces rather
than an inventory of stored, decomposed form-meaning entries ([baayen-2019]).
At the endstate of learning the model is a pair of linear maps — a comprehension
map (the papers' `F`, with `Ŝ = CF`) and a production map (`G`, with `Ĉ = SG`) —
fitted by *linear discriminative learning* (LDL), the least-squares estimation
method of [heitmeier-chuang-baayen-2026].

## Main declarations

- `LinearDiscriminativeLexicon R F M`: a pair of `LinearMap`s between form and
  meaning carriers.
- `LinearDiscriminativeLexicon.sub_mem_ker_iff`: the kernel of the production
  map is the DLM's neutralization locus.
- `FormVec`, `MeaningVec`: `Fin n → ℝ` carriers for the Studies specialisations.
- `broadcast`: the coordinate-broadcast linear map, a witness for
  non-degenerate example DLMs.
-/

namespace Processing.Lexical.Discriminative

variable (R F M : Type*)

/-! ### The Linear Discriminative Lexicon -/

section Defs

variable [Semiring R] [AddCommMonoid F] [AddCommMonoid M] [Module R F] [Module R M]

/-- The endstate of a **Discriminative Lexicon Model** with linear mappings:
    a comprehension map and a production map between form and meaning carriers,
    fitted by linear discriminative learning ([heitmeier-chuang-baayen-2026]).
    The two maps are the model's entire "lexicon" — there is no stored
    inventory. -/
structure LinearDiscriminativeLexicon where
  /-- The form → meaning map — the papers' comprehension matrix `F` (`Ŝ = CF`). -/
  comprehension : F →ₗ[R] M
  /-- The meaning → form map — the papers' production matrix `G` (`Ĉ = SG`). -/
  production : M →ₗ[R] F

end Defs

/-! ### Kernel = neutralization locus -/

section Kernel

variable {R F M} [Ring R] [AddCommGroup F] [AddCommGroup M] [Module R F] [Module R M]

/-- Two meanings surface as identical forms iff their difference lies in
    `ker production` — the DLM's **neutralization locus**. -/
theorem LinearDiscriminativeLexicon.sub_mem_ker_iff
    (D : LinearDiscriminativeLexicon R F M) {e₁ e₂ : M} :
    e₁ - e₂ ∈ LinearMap.ker D.production ↔ D.production e₁ = D.production e₂ :=
  LinearMap.sub_mem_ker_iff

end Kernel

/-! ### ℝ-typed Fin-indexed carriers -/

/-- A `formDim`-dimensional **form vector** over ℝ. -/
abbrev FormVec (formDim : ℕ) : Type := Fin formDim → ℝ

/-- A `meaningDim`-dimensional **meaning vector** over ℝ. -/
abbrev MeaningVec (meaningDim : ℕ) : Type := Fin meaningDim → ℝ

/-! ### The broadcast witness -/

/-- The "broadcast coordinate `i`" linear map `e ↦ fun _ => e i`. -/
def broadcast {n d : ℕ} (i : Fin d) : MeaningVec d →ₗ[ℝ] FormVec n :=
  LinearMap.pi fun _ => LinearMap.proj i

@[simp] theorem broadcast_apply {n d : ℕ} (i : Fin d) (e : MeaningVec d)
    (j : Fin n) : broadcast i e j = e i := rfl

end Processing.Lexical.Discriminative
