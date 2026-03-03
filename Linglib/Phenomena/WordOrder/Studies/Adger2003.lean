import Linglib.Theories.Syntax.Minimalism.Inversion
import Linglib.Phenomena.WordOrder.SubjectAuxInversion

/-!
# Minimalist Analysis of Subject-Auxiliary Inversion
@cite{adger-2003}

Connects the Minimalist T-to-C analysis of inversion
(`Theories/Syntax/Minimalism/Inversion.lean`) to the theory-neutral SAI data
(`Phenomena/WordOrder/SubjectAuxInversion.lean`).

The Minimalist analysis derives SAI from head movement:
- Matrix questions have [+Q] on C, triggering T-to-C movement → T precedes subject.
- Embedded questions satisfy [+Q] via the embedding verb → no T-to-C → subject precedes T.

Each theorem pairs a Data judgment with the corresponding Minimalist
licensing result, verifying that the theory's predictions match the
empirical pattern.
-/

namespace Phenomena.WordOrder.Studies.Adger2003

open Phenomena.WordOrder.SubjectAuxInversion

private abbrev what := Fragments.English.Pronouns.what.toWord
private abbrev can := Fragments.English.FunctionWords.can.toWord
private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev eat := Fragments.English.Predicates.Verbal.eat.toWordPl

-- ============================================================================
-- SAI Data ↔ Minimalist Licensing
-- ============================================================================

/-! ### Matrix wh-questions

The Data file marks inverted matrix wh-questions as grammatical and
non-inverted ones as ungrammatical. Minimalism licenses the former via
T-to-C movement and blocks the latter because [+Q] on C requires T in C. -/

/-- ex01 "What can John eat?" — grammatical per Data, licensed per Minimalism -/
theorem bridge_ex01 :
    ex01.acceptability == .grammatical ∧
    Minimalism.licenses [what, can, john, eat] .matrixQuestion :=
  ⟨rfl, Minimalism.licenses_matrix_t_first _ rfl⟩

/-- ex02 "*What John can eat?" — ungrammatical per Data, not licensed per Minimalism -/
theorem bridge_ex02 :
    ex02.acceptability == .ungrammatical ∧
    ¬ Minimalism.licenses [what, john, can, eat] .matrixQuestion :=
  ⟨rfl, Minimalism.not_licenses_matrix_subject_first _ rfl⟩

/-! ### Embedded questions -/

/-- ex07 "I wonder what John can eat" — grammatical per Data, licensed per Minimalism -/
theorem bridge_ex07 :
    ex07.acceptability == .grammatical ∧
    Minimalism.licenses [john, can, eat] .embeddedQuestion :=
  ⟨rfl, Minimalism.licenses_embedded_subject_first _ rfl⟩

/-- ex08 "*I wonder what can John eat" — ungrammatical per Data, not licensed per Minimalism -/
theorem bridge_ex08 :
    ex08.acceptability == .ungrammatical ∧
    ¬ Minimalism.licenses [can, john, eat] .embeddedQuestion :=
  ⟨rfl, Minimalism.not_licenses_embedded_t_first _ rfl⟩

/-! ### Summary

The Minimalist T-to-C analysis correctly captures all 4 core SAI data points:

| Datum | Sentence                   | Data       | Minimalism |
|-------|----------------------------|------------|------------|
| ex01  | What can John eat?         | ✓ gram.    | ✓ licensed |
| ex02  | *What John can eat?        | ✗ ungram.  | ✗ blocked  |
| ex07  |...what John can eat       | ✓ gram.    | ✓ licensed |
| ex08  | *...what can John eat      | ✗ ungram.  | ✗ blocked  |

Note: The Minimalist theory file uses T-position (finding `.AUX` tokens)
rather than category-neutral word order, so it covers the same empirical
ground as HPSG but through different formal machinery (derivational
movement vs. declarative feature constraint).
-/

end Phenomena.WordOrder.Studies.Adger2003
