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

Housed under `Processing/Lexical/` rather than a `Theories/Lexicon/`: the DLM
rejects the lexicon-as-stored-inventory architecture, so what it contributes is a
*processing* theory — how form vectors map to meaning vectors and back. Rival
stored-lexicon accounts (frequency-channel theories, [bybee-1985]'s usage-based
network) live with the linguistic level whose generalisations they explain; see
`Studies/ChuangEtAl2026.lean` for the architectural comparison.

## Main declarations

- `LinearDiscriminativeLexicon R F M`: a pair of `LinearMap`s between form and
  meaning carriers; applies to any `[Module R F]`/`[Module R M]` pair.
- `LinearDiscriminativeLexicon.production_eq_iff`: two meanings surface as
  identical forms iff their difference lies in `LinearMap.ker production` — the
  kernel of the production map is the DLM's **neutralization locus**.
- `FormVec`, `MeaningVec`: `Fin n → ℝ` carriers for the Studies specialisations.
- `broadcast`: the coordinate-broadcast linear map, a reusable witness for
  non-degenerate example DLMs (e.g. `LuChuangBaayen2026.dlm_dialect_flexibility`).

Siblings: `Normed.lean` (operator-norm/Lipschitz layer), `Measures.lean`
(semantic-support measures), `Training.lean` (endstate vs frequency-informed
learning as weighted least squares). Consumers: `Studies/ChuangEtAl2026`,
`Studies/LuChuangBaayen2026`, `Studies/Saito2025`, `Studies/GahlBaayen2024`.
Not formalized here: [chuang-bell-tseng-baayen-2026]'s ResLDL (LDL plus a deep
network fitted to the linear map's residuals) and
[heitmeier-chuang-baayen-2026]'s DDL (deep replacement for the linear maps).
-/

namespace Processing.Lexical.Discriminative

/-! ### The Linear Discriminative Lexicon -/

/-- The endstate of a **Discriminative Lexicon Model** with linear mappings: a
    comprehension map and a production map between form and meaning carriers.
    Linearity is baked in via mathlib's `LinearMap` because the maps are fitted
    by *linear discriminative learning* (LDL names the estimation method, not
    the model; [heitmeier-chuang-baayen-2026]).

    There are exactly two fields, both linear maps — no `entries` list, no
    frequency field: this model's "lexicon" is its mappings, not a stored
    inventory. The kernel of `production` is the model's neutralization locus
    (`production_eq_iff`). -/
structure LinearDiscriminativeLexicon (R : Type*) (F M : Type*)
    [Semiring R] [AddCommMonoid F] [AddCommMonoid M]
    [Module R F] [Module R M] where
  /-- The form → meaning map — the papers' comprehension matrix `F` (`Ŝ = CF`).
      (The papers' letter `F` names this map, not the form carrier.) -/
  comprehension : F →ₗ[R] M
  /-- The meaning → form map — the papers' production matrix `G` (`Ĉ = SG`). -/
  production : M →ₗ[R] F

/-! ### Kernel = neutralization locus -/

section Kernel

variable {R : Type*} {F M : Type*}
  [Ring R] [AddCommGroup F] [AddCommGroup M] [Module R F] [Module R M]

/-- Two meanings surface as identical forms iff their difference lies in the
    kernel of the production map: `ker production` is the **neutralization
    locus** — the meaning-differences the DLM cannot realize in form. When two
    empirically distinct meanings share a surface form, that identity follows
    from their difference landing in the kernel, not from a stipulated rule;
    `Studies/LuChuangBaayen2026.lean` applies this to Taiwan Mandarin T3 tone
    sandhi. Specialises `LinearMap.sub_mem_ker_iff`. -/
theorem LinearDiscriminativeLexicon.production_eq_iff
    (D : LinearDiscriminativeLexicon R F M) {e₁ e₂ : M} :
    D.production e₁ = D.production e₂ ↔ e₁ - e₂ ∈ LinearMap.ker D.production :=
  LinearMap.sub_mem_ker_iff.symm

end Kernel

/-! ### ℝ-typed Fin-indexed carriers -/

/-- A `formDim`-dimensional **form vector** over ℝ. Both Mandarin tone studies
    use pitch contours sampled at uniform points on a normalised time axis
    (`formDim = 50` in [chuang-bell-tseng-baayen-2026], `100` in
    [lu-chuang-baayen-2026]); the duration studies use triphone cue vectors. -/
abbrev FormVec (formDim : ℕ) : Type := Fin formDim → ℝ

/-- A `meaningDim`-dimensional **meaning vector** over ℝ — e.g. the 768-dim
    CKIP GPT-2 contextualised embeddings of both Mandarin tone studies. -/
abbrev MeaningVec (meaningDim : ℕ) : Type := Fin meaningDim → ℝ

/-! ### The broadcast witness -/

/-- The "broadcast coordinate `i`" linear map: `e ↦ (fun _ => e i)`. The
    simplest non-degenerate `LinearMap` from `MeaningVec d` to `FormVec n`;
    reusable by consumers for concrete example DLMs without re-implementation. -/
def broadcast {n d : ℕ} (i : Fin d) : MeaningVec d →ₗ[ℝ] FormVec n :=
  LinearMap.pi fun _ => LinearMap.proj i

/-- Evaluation of `broadcast` at any sample index returns the input's
    coordinate-`i` value. -/
@[simp] theorem broadcast_apply {n d : ℕ} (i : Fin d) (e : MeaningVec d)
    (j : Fin n) : broadcast i e j = e i := rfl

end Processing.Lexical.Discriminative
