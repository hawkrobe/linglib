import Linglib.Processing.DiscriminativeLexicon.Defs
import Mathlib.Data.Matrix.Mul

/-!
# DLM-derived semantic-support measures

The *semantic support* measures read off a `Linear`'s production map at
the `FormVec`/`MeaningVec` carriers. The support a form receives from a meaning is the dot
product of the predicted form with the target form, `ĉ ⬝ᵥ c` for `ĉ = sG`: the entries of
[gahl-baayen-2024]'s support matrix `T = ĈCᵀ`, whose diagonal is their *semantic support for
form*, and at a single triphone [saito-tomaschek-baayen-2025]'s `SemSupSuffix`.

## Main declarations

- `semSup D s j`: support for form coordinate `j` from meaning `s`, the predicted value
  `D.production s j`.
- `semSupWord D s c`: support for the form vector `c` from meaning `s`, `D.production s ⬝ᵥ c`;
  `semSup` is its value at a coordinate indicator (`semSupWord_single`).
- `semSup_add`, `semSup_smul`, `semSupWord_add_left`, `semSupWord_smul_right`, …: `@[simp]`
  linearity in each argument.

## References

* [R. H. Baayen, Y.-Y. Chuang, E. Shafaei-Bajestan and J. P. Blevins, *The discriminative
  lexicon* (2019)][baayen-2019]
* [S. Gahl and R. H. Baayen, *Time and thyme again* (2024)][gahl-baayen-2024]
* [M. Saito, F. Tomaschek and R. H. Baayen, *Interaction of frequency and inflectional status*
  (2025)][saito-tomaschek-baayen-2025]
* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
-/

namespace DiscriminativeLexicon

noncomputable section

variable {n d : ℕ} (D : Linear ℝ (FormVec n) (MeaningVec d))

/-! ### Semantic support -/

/-- **Semantic support** for form coordinate `j` from meaning `s`: the predicted value
`D.production s j` ([saito-tomaschek-baayen-2025]; [gahl-baayen-2024]'s per-triphone support). -/
def semSup (s : MeaningVec d) (j : Fin n) : ℝ := D.production s j

/-- **Semantic support** for the form vector `c` from meaning `s`: the dot product of the
predicted form with `c`. At a word's own binary triphone vector this is [gahl-baayen-2024]'s
*semantic support for form*, the diagonal of `T = ĈCᵀ`. -/
def semSupWord (s : MeaningVec d) (c : FormVec n) : ℝ := D.production s ⬝ᵥ c

variable {D}

@[simp] theorem semSupWord_single (s : MeaningVec d) (j : Fin n) :
    semSupWord D s (Pi.single j 1) = semSup D s j := by
  simp [semSupWord, semSup]

/-! ### Linearity -/

@[simp] theorem semSup_add (s₁ s₂ : MeaningVec d) (j : Fin n) :
    semSup D (s₁ + s₂) j = semSup D s₁ j + semSup D s₂ j := by
  simp [semSup]

@[simp] theorem semSup_smul (a : ℝ) (s : MeaningVec d) (j : Fin n) :
    semSup D (a • s) j = a * semSup D s j := by
  simp [semSup]

@[simp] theorem semSup_zero (j : Fin n) : semSup D 0 j = 0 := by
  simp [semSup]

@[simp] theorem semSupWord_add_left (s₁ s₂ : MeaningVec d) (c : FormVec n) :
    semSupWord D (s₁ + s₂) c = semSupWord D s₁ c + semSupWord D s₂ c := by
  simp [semSupWord, add_dotProduct]

@[simp] theorem semSupWord_smul_left (a : ℝ) (s : MeaningVec d) (c : FormVec n) :
    semSupWord D (a • s) c = a * semSupWord D s c := by
  simp [semSupWord, smul_dotProduct]

@[simp] theorem semSupWord_zero_left (c : FormVec n) : semSupWord D 0 c = 0 := by
  simp [semSupWord]

@[simp] theorem semSupWord_add_right (s : MeaningVec d) (c₁ c₂ : FormVec n) :
    semSupWord D s (c₁ + c₂) = semSupWord D s c₁ + semSupWord D s c₂ := by
  simp [semSupWord, dotProduct_add]

@[simp] theorem semSupWord_smul_right (a : ℝ) (s : MeaningVec d) (c : FormVec n) :
    semSupWord D s (a • c) = a * semSupWord D s c := by
  simp [semSupWord, dotProduct_smul]

@[simp] theorem semSupWord_zero_right (s : MeaningVec d) : semSupWord D s 0 = 0 := by
  simp [semSupWord]

end

end DiscriminativeLexicon
