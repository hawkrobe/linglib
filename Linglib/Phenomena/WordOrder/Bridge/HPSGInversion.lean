import Linglib.Theories.Syntax.HPSG.Inversion
import Linglib.Phenomena.WordOrder.SubjectAuxInversion

/-!
# Bridge: HPSG → Subject-Auxiliary Inversion Data

Connects the HPSG [INV ±] analysis of inversion
(`Theories/Syntax/HPSG/Inversion.lean`) to the theory-neutral SAI data
(`Phenomena/WordOrder/SubjectAuxInversion.lean`).

The HPSG analysis (Sag, Wasow & Bender 2003) uses a binary [INV] feature:
- Matrix questions require [INV +], forcing auxiliary-before-subject order.
- Embedded questions require [INV −], forcing subject-before-auxiliary order.

Each bridge theorem pairs a Data judgment with the corresponding HPSG
licensing result, verifying that the theory's predictions match the
empirical pattern.
-/

namespace Phenomena.WordOrder.Bridge.HPSGInversion

open Phenomena.WordOrder.SubjectAuxInversion

private abbrev what := Fragments.English.Pronouns.what.toWord
private abbrev can := Fragments.English.FunctionWords.can.toWord
private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev eat := Fragments.English.Predicates.Verbal.eat.toWordPl
private abbrev pizza := Fragments.English.Nouns.pizza.toWordSg

-- ============================================================================
-- Bridge Theorems: SAI Data ↔ HPSG Licensing
-- ============================================================================

/-! ### Matrix wh-questions

The Data file marks inverted matrix wh-questions as grammatical and
non-inverted ones as ungrammatical. HPSG licenses the former via [INV +]
and blocks the latter because [INV +] requires aux < subj. -/

/-- ex01 "What can John eat?" — grammatical per Data, licensed per HPSG -/
theorem bridge_ex01 :
    ex01.acceptability == .grammatical ∧
    HPSG.licenses [what, can, john, eat] .matrixQuestion :=
  ⟨rfl, HPSG.licenses_matrix_aux_first _ rfl⟩

/-- ex02 "*What John can eat?" — ungrammatical per Data, not licensed per HPSG -/
theorem bridge_ex02 :
    ex02.acceptability == .ungrammatical ∧
    ¬ HPSG.licenses [what, john, can, eat] .matrixQuestion :=
  ⟨rfl, HPSG.not_licenses_matrix_subject_first _ rfl⟩

/-! ### Matrix yes/no questions -/

/-- ex04 "Can John eat pizza?" — grammatical per Data, licensed per HPSG -/
theorem bridge_ex04 :
    ex04.acceptability == .grammatical ∧
    HPSG.licenses [can, john, eat, pizza] .matrixQuestion :=
  ⟨rfl, HPSG.licenses_matrix_aux_first _ rfl⟩

/-- ex05 "*John can eat pizza?" — ungrammatical per Data, not licensed per HPSG -/
theorem bridge_ex05 :
    ex05.acceptability == .ungrammatical ∧
    ¬ HPSG.licenses [john, can, eat, pizza] .matrixQuestion :=
  ⟨rfl, HPSG.not_licenses_matrix_subject_first _ rfl⟩

/-! ### Embedded questions -/

/-- ex07 "I wonder what John can eat" — grammatical per Data, licensed per HPSG -/
theorem bridge_ex07 :
    ex07.acceptability == .grammatical ∧
    HPSG.licenses [john, can, eat] .embeddedQuestion :=
  ⟨rfl, HPSG.licenses_embedded_subject_first _ rfl⟩

/-- ex08 "*I wonder what can John eat" — ungrammatical per Data, not licensed per HPSG -/
theorem bridge_ex08 :
    ex08.acceptability == .ungrammatical ∧
    ¬ HPSG.licenses [can, john, eat] .embeddedQuestion :=
  ⟨rfl, HPSG.not_licenses_embedded_aux_first _ rfl⟩

/-! ### Summary

The HPSG [INV ±] analysis correctly captures all 6 core SAI data points:

| Datum | Sentence                   | Data       | HPSG       |
|-------|----------------------------|------------|------------|
| ex01  | What can John eat?         | ✓ gram.    | ✓ licensed |
| ex02  | *What John can eat?        | ✗ ungram.  | ✗ blocked  |
| ex04  | Can John eat pizza?        | ✓ gram.    | ✓ licensed |
| ex05  | *John can eat pizza?       | ✗ ungram.  | ✗ blocked  |
| ex07  | ...what John can eat       | ✓ gram.    | ✓ licensed |
| ex08  | *...what can John eat      | ✗ ungram.  | ✗ blocked  |
-/

end Phenomena.WordOrder.Bridge.HPSGInversion
