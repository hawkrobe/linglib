import Linglib.Processing.Lexical.Discriminative.Defs

/-!
# DLM-derived semantic-support measures
[baayen-2019] [gahl-baayen-2024] [saito-tomaschek-baayen-2025]
[heitmeier-chuang-baayen-2026]

Sibling to `Defs.lean` and `Normed.lean`. Hosts the family of *semantic
support* measures derived from a trained `LinearDiscriminativeLexicon` —
the per-coordinate, per-word, and per-region projections of
`production` that consumer studies have come to rely on.

## What is in this file

- `semSup D s j` — semantic support for coordinate `j` of the form
  vector predicted from meaning vector `s`. Direct projection of
  `D.production s` at index `j`.
- `semSupWord D s js` — sum of `semSup` over a list of form coordinates.
  The natural "how strongly does the meaning predict this word's
  combination of form units" measure (paper §3.1 of
  [saito-tomaschek-baayen-2025]; paper §3.4 of
  [gahl-baayen-2024]).
- `semSup_add` / `semSup_smul` / `semSup_zero` — `@[simp]` linearity
  lemmas in the meaning argument; derived from `LinearMap.map_add` /
  `map_smul` / `map_zero` on `D.production`.

## Carriers

Specialised to `FormVec n` / `MeaningVec d` (i.e. `Fin n → ℝ` /
`Fin d → ℝ`), the most common DLM carrier types. All current consumers
(`ChuangEtAl2026`, `LuChuangBaayen2026`, `Saito2025`, `GahlBaayen2024`)
use these. A `Measures/InnerProduct.lean` sibling can host
inner-product-typed variants if a future consumer needs cosine
similarities directly.
-/

namespace Processing.Lexical.Discriminative

noncomputable section SemSupMeasures

variable {n d : ℕ}

/-! ### Semantic support — coordinate projection of production -/

/-- **Semantic support** for coordinate `j` of the form vector predicted
    from meaning vector `s`: `semSup D s j = D.production s j`.

    The substrate's `D.production s j` already provides this directly;
    the named binding makes the cross-paper concept (paper §3.1 eq. 1
    of [saito-tomaschek-baayen-2025]; the per-triphone support
    of [gahl-baayen-2024] §3.4) grep-able. -/
def semSup (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (s : MeaningVec d) (j : Fin n) : ℝ :=
  D.production s j

/-- **Word-level semantic support** — the sum of `semSup` over a word's
    component form coordinates. In the consumer studies' triphone-
    based form representation, this is the sum over the word's
    component triphones (paper §3.4 of [gahl-baayen-2024] terms
    this `Semantic Support for Form`; paper §3.1 eq. 2 of
    [saito-tomaschek-baayen-2025] terms it `SemSupWord`). -/
def semSupWord (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (s : MeaningVec d) (js : List (Fin n)) : ℝ :=
  (js.map (semSup D s)).sum

/-! ### `semSup` is linear in the meaning vector

Since `D.production` is a `LinearMap`, `semSup D · j` is a linear
functional on the meaning space. Three structural lemmas (additivity,
scalar-multiplication, zero) follow by `map_add` / `map_smul` /
`map_zero` on the production map. `@[simp]` so consumers can rewrite
linear-combination meaning vectors directly. -/

@[simp] theorem semSup_add
    (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (s₁ s₂ : MeaningVec d) (j : Fin n) :
    semSup D (s₁ + s₂) j = semSup D s₁ j + semSup D s₂ j := by
  unfold semSup
  rw [map_add]
  rfl

@[simp] theorem semSup_smul
    (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (c : ℝ) (s : MeaningVec d) (j : Fin n) :
    semSup D (c • s) j = c * semSup D s j := by
  unfold semSup
  rw [map_smul]
  rfl

@[simp] theorem semSup_zero
    (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (j : Fin n) :
    semSup D 0 j = 0 := by
  unfold semSup
  rw [map_zero]
  rfl

/-! ### `semSupWord` zero case

`semSupWord D 0 js = 0` follows from `semSup_zero` plus `List.sum`
of the constant-zero list. The general `semSupWord_add` /
`semSupWord_smul` linearity (sum of linear functionals is linear)
is deferred until a consumer needs to rewrite linear-combination
meaning vectors at the word level — induction on `js` plus `ring`
at the cons step works once `Mathlib.Tactic.Ring` is imported, but
no current consumer requires it. -/

@[simp] theorem semSupWord_zero
    (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (js : List (Fin n)) :
    semSupWord D 0 js = 0 := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    show semSup D 0 j + semSupWord D 0 js = 0
    rw [semSup_zero, ih, zero_add]

end SemSupMeasures

end Processing.Lexical.Discriminative
