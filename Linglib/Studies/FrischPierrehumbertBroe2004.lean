import Mathlib.Tactic.Linarith
import Linglib.Fragments.Arabic.ModernStandard.Phonology
import Linglib.Studies.Broe1993
import Linglib.Data.Examples.FrischPierrehumbertBroe2004

/-!
# Frisch, Pierrehumbert and Broe (2004): Similarity Avoidance and the OCP

This file formalizes [frisch-pierrehumbert-broe-2004]'s gradient OCP-Place: the rarity of
homorganic consonant pairs in Arabic verbal roots is a decreasing function of the similarity of
the pair, where similarity counts the natural classes two consonants share against those they
share or do not share, restricted to the classes defined by a place feature (`similarity`, the
paper's equation (7)). The natural classes are generated from the feature matrix by
[broe-1993]'s structured specification, so a larger, more contrastive region of the inventory
generates more classes and any coronal pair is less similar than a comparable labial pair,
deriving the strength of the labial restriction against the weakness of the coronal one that the
categorical analyses of [mccarthy-1986], [mccarthy-1994] and [padgett-1995] stipulate. The
paper's worked labial examples are reproduced both from its printed class lists and from the
labial columns of its feature matrix through `Broe1993.naturalClasses`; the printed list for
/b, f/ contains the class {b, w}, which no description over the matrix generates, in place of
{f}, leaving the count and the reported value correct (`similarity_derived_b_f`). Against the
gradient, a categorical OCP-Place predicts only two rates of co-occurrence, one for violations
and one for the rest; three distinct rates defeat it (`not_categorical_of_three`), and the
paper's three worked root types, with no /d t C/ roots where 2.3 are expected, two /d s C/ roots
where 2.9 are expected, and four /d g C/ roots where 3.3 are expected, are three such rates
ordered against similarity (`rows_not_categorical`). The paper's own comparison is the fit over
the whole lexicon of [cowan-1979]: observed over expected co-occurrence falls from 1.22 for
non-homorganic adjacent pairs to near zero from similarity 0.4 upward (Table IV), and the
natural-classes model explains more of the variance than the categorical one (Table V).

## Implementation notes

* Similarity is exact over ℚ. The rows carry observed counts, expected counts in tenths, and
  rates and similarities in hundredths, the paper's printed precision.
* The two class lists are the paper's enumerations; `labialContext` records the labial columns
  of the feature matrix with nasality specified for the stops only, the paper's trivial
  underspecification.
* The examples are `Data.Examples.FrischPierrehumbertBroe2004`.

## References

* [frisch-pierrehumbert-broe-2004]
* [broe-1993]
* [mccarthy-1986]
* [mccarthy-1994]
* [padgett-1995]
* [cowan-1979]
-/

namespace FrischPierrehumbertBroe2004

open Arabic.ModernStandard Data.Examples

/-- The natural-classes similarity of two segments (equation (7)): the classes containing both
over the classes containing either. -/
def similarity {α : Type*} [DecidableEq α] (xs : List (Finset α)) (x y : α) : ℚ :=
  (xs.countP λ s => decide (x ∈ s ∧ y ∈ s) : ℚ) / xs.countP λ s => decide (x ∈ s ∨ y ∈ s)

/-! ### The labial worked examples (p. 199) -/

/-- The labial natural classes of the /f, m/ computation: the two shared, then the seven not
shared. -/
def labialClasses_fm : List (Finset Consonant) :=
  [{.b, .f, .m, .w}, {.b, .f, .m},
   {.b, .f}, {.f, .w}, {.f}, {.b, .m, .w}, {.b, .m}, {.m, .w}, {.m}]

/-- The labial natural classes of the /b, f/ computation as printed: the three shared, then the
five not shared. The entry {b, w} stands where the feature matrix generates {f}
(`derived_bf_classes`); the count, and the reported 3/8, are unaffected. -/
def labialClasses_bf : List (Finset Consonant) :=
  [{.b, .f, .m, .w}, {.b, .f, .m}, {.b, .f},
   {.f, .w}, {.b, .m, .w}, {.b, .m}, {.b, .w}, {.b}]

theorem similarity_f_m : similarity labialClasses_fm .f .m = 2/9 := by decide +kernel

theorem similarity_b_f : similarity labialClasses_bf .b .f = 3/8 := by decide +kernel

/-! ### The classes from the feature matrix (8) (p. 201) -/

/-- The labial columns of the feature matrix: the extents on {b, f, m, w} of the values it
specifies for consonantal, sonorant, continuant, nasal (on the stops only) and voice. -/
def labialContext : List (Finset Consonant) :=
  [{.b, .f, .m}, {.w},
   {.m, .w}, {.b, .f},
   {.f, .w}, {.b, .m},
   {.m}, {.b},
   {.b, .m, .w}, {.f}]

/-- The natural classes the matrix generates over the labials. -/
def derivedLabialClasses : List (Finset Consonant) :=
  Broe1993.naturalClasses {.b, .f, .m, .w} labialContext

/-- The derived classes containing /f/ or /m/ are the paper's enumeration. -/
theorem derived_fm_classes :
    (derivedLabialClasses.filter λ s => decide (Consonant.f ∈ s ∨ Consonant.m ∈ s)).toFinset =
      labialClasses_fm.toFinset := by
  decide +kernel

/-- The derived classes containing /b/ or /f/ are the paper's enumeration with {f} in place of
{b, w}. -/
theorem derived_bf_classes :
    (derivedLabialClasses.filter λ s => decide (Consonant.b ∈ s ∨ Consonant.f ∈ s)).toFinset =
      insert {.f} (labialClasses_bf.toFinset.erase {.b, .w}) := by
  decide +kernel

theorem similarity_derived_f_m : similarity derivedLabialClasses .f .m = 2/9 := by
  decide +kernel

/-- The reported value survives the list's typo. -/
theorem similarity_derived_b_f : similarity derivedLabialClasses .b .f = 3/8 := by
  decide +kernel

/-! ### Gradient against categorical -/

variable (t c₁ c₂ : ℚ)

/-- A categorical OCP-Place as a predictor of co-occurrence: one rate for pairs whose similarity
reaches the threshold, another for the rest. -/
def categoricalAtThreshold (sim : ℚ) : ℚ := if sim < t then c₁ else c₂

/-- A categorical predictor takes at most two values, so three distinct rates defeat it. -/
theorem not_categorical_of_three {s₁ s₂ s₃ o₁ o₂ o₃ : ℚ} (h₁₂ : o₁ ≠ o₂) (h₁₃ : o₁ ≠ o₃)
    (h₂₃ : o₂ ≠ o₃) :
    ¬ (categoricalAtThreshold t c₁ c₂ s₁ = o₁ ∧ categoricalAtThreshold t c₁ c₂ s₂ = o₂ ∧
      categoricalAtThreshold t c₁ c₂ s₃ = o₃) := by
  rintro ⟨h₁, h₂, h₃⟩
  simp only [categoricalAtThreshold] at h₁ h₂ h₃
  split_ifs at h₁ h₂ h₃ <;>
    first
    | exact h₁₂ (h₁.symm.trans h₂)
    | exact h₁₃ (h₁.symm.trans h₃)
    | exact h₂₃ (h₂.symm.trans h₃)

/-! ### The paper's root types -/

/-- A root type of the paper: its first two consonants, the roots observed and expected (in
tenths) in the lexicon, their ratio in hundredths, and the consonants' similarity in hundredths
(Table III). -/
structure Row where
  pair : Consonant × Consonant
  observed : ℕ
  expected : ℕ
  oe : ℕ
  similarity : ℕ
  deriving DecidableEq

private def consonants : List (String × Consonant) := [("d", .d), ("t", .t), ("s", .s), ("g", .jim)]

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let c₁ ← ex.parse? "c1" consonants
  let c₂ ← ex.parse? "c2" consonants
  let o ← ex.nat? "observed"
  let e ← ex.nat? "expectedTenths"
  let oe ← ex.nat? "oeHundredths"
  let s ← ex.nat? "similarityHundredths"
  pure ⟨(c₁, c₂), o, e, oe, s⟩

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Co-occurrence falls as similarity rises across the worked root types. -/
theorem rows_antitone :
    ∀ r ∈ rows, ∀ r' ∈ rows, r.similarity < r'.similarity → r'.oe < r.oe := by
  decide

/-- No categorical predictor fits the three worked root types. -/
theorem rows_not_categorical :
    ¬ ∀ r ∈ rows, categoricalAtThreshold t c₁ c₂ (r.similarity / 100) = r.oe / 100 := λ h =>
  not_categorical_of_three t c₁ c₂ (by norm_num) (by norm_num) (by norm_num)
    ⟨h ⟨(.d, .t), 0, 23, 0, 42⟩ (by decide), h ⟨(.d, .s), 2, 29, 69, 17⟩ (by decide),
      h ⟨(.d, .jim), 4, 33, 121, 0⟩ (by decide)⟩

end FrischPierrehumbertBroe2004
