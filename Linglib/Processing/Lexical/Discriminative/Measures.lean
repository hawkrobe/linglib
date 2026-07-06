import Linglib.Processing.Lexical.Discriminative.Defs

/-!
# DLM-derived semantic-support measures
[baayen-2019] [gahl-baayen-2024] [saito-tomaschek-baayen-2025]
[heitmeier-chuang-baayen-2026]

The *semantic support* measures projected from a
`LinearDiscriminativeLexicon`'s production map, specialised to the
`FormVec`/`MeaningVec` carriers.

## Main declarations

- `semSup D s j`: semantic support for form coordinate `j` from meaning `s`.
- `semSupWord D s js`: sum of `semSup` over a word's form coordinates —
  [gahl-baayen-2024]'s *Semantic Support for Form*,
  [saito-tomaschek-baayen-2025]'s `SemSupWord`.
- `semSup_add` / `semSup_smul` / `semSup_zero`: `@[simp]` linearity lemmas
  in the meaning argument.
-/

namespace Processing.Lexical.Discriminative

noncomputable section SemSupMeasures

variable {n d : ℕ}

/-! ### Semantic support — coordinate projection of production -/

/-- **Semantic support** for form coordinate `j` from meaning vector `s`:
    the named binding for `D.production s j` ([saito-tomaschek-baayen-2025];
    [gahl-baayen-2024]'s per-triphone support). -/
def semSup (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (s : MeaningVec d) (j : Fin n) : ℝ :=
  D.production s j

/-- **Word-level semantic support** — the sum of `semSup` over a word's
    component form coordinates ([gahl-baayen-2024]'s *Semantic Support for
    Form*; [saito-tomaschek-baayen-2025]'s `SemSupWord`). -/
def semSupWord (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
    (s : MeaningVec d) (js : List (Fin n)) : ℝ :=
  (js.map (semSup D s)).sum

/-! ### `semSup` is linear in the meaning vector

Since `D.production` is a `LinearMap`, `semSup D · j` is a linear
functional on the meaning space. -/

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

The general `semSupWord_add` / `semSupWord_smul` linearity is deferred
until a consumer needs it. -/

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
