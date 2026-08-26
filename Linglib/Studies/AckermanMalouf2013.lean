import Linglib.Morphology.Paradigm.Complexity
import Linglib.Fragments.Greek.StandardModern.Declension
import Linglib.Fragments.Burmeso.ObjectAgreement
import Linglib.Fragments.Mazatec.Verbs
import Linglib.Data.Examples.AckermanMalouf2013

/-!
# The low conditional entropy conjecture

Ackerman and Malouf separate the enumerative complexity of an inflectional system — how many
cells, realizations, and inflection classes it has — from its integrative complexity, the
average conditional entropy of one paradigm cell given another (`iComplexity`, over
`Morphology.ParadigmSystem.conditionalCellEntropy`), and conjecture that the latter stays low
however large the former grows. Their Modern Greek fragment
(`Greek.StandardModern.Declension.nominal`) carries the argument against enumerative principles:
its eight declensions exceed the five rival realizations of its most varied cell, violating
paradigm economy (`greek_not_paradigmEconomy`), while implicative structure keeps the speaker's
task small — the genitive plural has a single realization (`greek_cellEntropy_genPl`),
accusative and vocative singular predict each other and the accusative plural predicts the
nominative plural (`greek_predicts`), an accusative plural in *-i* fixes the genitive singular
(`greek_accPl_i_genSg`) although the accusative plural alone does not predict it
(`greek_not_predicts`), and three cells form a principal-part set where two do not
(`greek_principalParts`).

Synonymy avoidance — each realization of a cell identifying its class — is the zero of the
measure: a vocabularly clear system is transparent and has integrative complexity zero
(`Morphology.ParadigmSystem.isTransparent_of_isVocabularClear`, `transparent_iComplexity_zero`),
as Burmeso's two object-agreement classes are (`burmeso_iComplexity`). Chiquihuitlán Mazatec
departs from it in both dimensions the paper distinguishes: its final-vowel classes are not
vocabularly clear (`mazatec_vowels_not_clear`) and two of their cells are constant
(`mazatec_vowels_constant`), and no cell of its neutral-aspect tone patterns is diagnostic of
class membership (`mazatec_tones_no_diagnostic_cell`).

## References

* [ackerman-malouf-2013]
* [carstairs-mccarthy-2010]
* [bonami-beniamine-2016]
-/

namespace AckermanMalouf2013

open Morphology Greek.StandardModern.Declension Burmeso.ObjectAgreement Mazatec.Verbs

variable {n : ℕ} {Form : Type*} [DecidableEq Form]

/-- Integrative complexity: the average conditional entropy over ordered pairs of distinct
cells. -/
noncomputable def iComplexity (ps : ParadigmSystem n Form) : ℝ :=
  (∑ ci, ∑ cj ∈ Finset.univ.erase ci, ps.conditionalCellEntropy ci cj) / (n * (n - 1))

/-- A transparent system has integrative complexity zero. -/
theorem transparent_iComplexity_zero {ps : ParadigmSystem n Form} (h : ps.IsTransparent) :
    iComplexity ps = 0 := by
  rw [iComplexity, Finset.sum_eq_zero, zero_div]
  exact fun ci _ => Finset.sum_eq_zero fun cj hcj => h ci cj (Finset.ne_of_mem_erase hcj).symm

/-! ### Modern Greek -/

theorem greek_eComplexity : nominal.eComplexity = 8 := rfl

theorem greek_maxRealizations : nominal.maxRealizations = 5 := by decide

/-- Eight declensions exceed the five rival realizations of the genitive singular. -/
theorem greek_not_paradigmEconomy : ¬ nominal.ParadigmEconomy := by decide

/-- The genitive plural has a single realization. -/
theorem greek_cellEntropy_genPl : nominal.cellEntropy genPl = 0 :=
  nominal.cellEntropy_eq_zero_of_card_le_one (by decide)

theorem greek_predicts :
    nominal.Predicts {vocSg} accSg ∧ nominal.Predicts {accSg} vocSg ∧
      nominal.Predicts {accPl} nomPl := by
  decide

/-- The accusative plural does not predict the genitive singular: after *-a* two genitives
remain. -/
theorem greek_not_predicts : ¬ nominal.Predicts {accPl} genSg := by decide

/-- An accusative plural in *-i* fixes the genitive singular in *-us*. -/
theorem greek_accPl_i_genSg : ∀ e ∈ nominal.entries, e.1 accPl = .i → e.1 genSg = .us := by
  decide

/-- Nominative singular, genitive singular, and accusative plural are principal parts; the
last two alone are not. -/
theorem greek_principalParts :
    nominal.IsPrincipalPartSet {nomSg, genSg, accPl} ∧
      ¬ nominal.IsPrincipalPartSet {genSg, accPl} := by
  decide

theorem greek_not_clear : ¬ nominal.IsVocabularClear := by decide

/-! ### Burmeso -/

/-- Every cell identifies the class. -/
theorem burmeso_clear : objectAgreement.IsVocabularClear := by decide

theorem burmeso_iComplexity : iComplexity objectAgreement = 0 :=
  transparent_iComplexity_zero (objectAgreement.isTransparent_of_isVocabularClear burmeso_clear)

/-! ### Chiquihuitlán Mazatec -/

theorem mazatec_vowels_not_clear : ¬ finalVowels.IsVocabularClear := by decide

/-- The first and second person plural vowels are constant across classes. -/
theorem mazatec_vowels_constant :
    finalVowels.cellEntropy firstPl = 0 ∧ finalVowels.cellEntropy secondPl = 0 :=
  ⟨finalVowels.cellEntropy_eq_zero_of_card_le_one (by decide),
    finalVowels.cellEntropy_eq_zero_of_card_le_one (by decide)⟩

/-- No cell of the tone patterns is diagnostic of class membership. -/
theorem mazatec_tones_no_diagnostic_cell : ∀ c, ¬ tones.IsPrincipalPartSet {c} := by decide

end AckermanMalouf2013
