import Linglib.Core.Case.Basic
import Linglib.Theories.Syntax.Case.Dependent

/-!
# Yakut (Sakha) Case System
@cite{baker-vinokurova-2010}

Sakha is the Turkic language analyzed by @cite{baker-vinokurova-2010}
as the cross-linguistic exemplar of a *two-modality* case grammar:
ACC and DAT are dependent case (Marantz; cf. `Marantz1991.lean`),
while NOM is assigned by finite T via Agree and GEN is assigned by
D via Agree.

The clausal-level derivations live in
`Phenomena/Case/Studies/BakerVinokurova2010.lean`. This fragment
records the language-level case inventory and the corresponding
`CaseSystemConfig` instance, parallel to `Fragments.Mongolian.Case`.
-/

namespace Fragments.Yakut.Case

open Syntax.Case

-- ============================================================================
-- § 1: Case System Configuration
-- ============================================================================

/-- The Sakha case system @cite{baker-vinokurova-2010}: accusative
    alignment with dependent ACC + DAT and Agree-based NOM + GEN. -/
def yakutCaseConfig : CaseSystemConfig where
  langType := .accusative
  nomMode  := .agreeT
  datMode  := .dependent
  accMode  := .dependent
  genMode  := .agreeD

theorem yakut_is_accusative : yakutCaseConfig.langType = .accusative := rfl
theorem yakut_acc_dependent : yakutCaseConfig.accMode  = .dependent  := rfl
theorem yakut_dat_dependent : yakutCaseConfig.datMode  = .dependent  := rfl
theorem yakut_nom_agree     : yakutCaseConfig.nomMode  = .agreeT     := rfl
theorem yakut_gen_agree     : yakutCaseConfig.genMode  = .agreeD     := rfl

-- ============================================================================
-- § 2: Case Inventory
-- ============================================================================

/-- Sakha morphological case inventory.

    Sakha distinguishes NOM (unmarked), ACC, DAT, ABL, INST, COM,
    and PART, plus the relational/derivational GEN that surfaces on
    DP-internal possessors. The traditional eight-case system is
    accusative-aligned with no ABS/ERG distinction. -/
def caseInventory : Finset Core.Case :=
  {.nom, .acc, .gen, .dat, .abl, .inst, .com, .part}

-- ============================================================================
-- § 3: Contrast with Mongolian
-- ============================================================================

/-- Sakha vs. Mongolian (cf. `Fragments.Mongolian.Case`): the two
    languages share `langType`, `nomMode`, `accMode`, and `genMode`
    but differ exclusively in `datMode`. Sakha has dependent DAT
    (assigned by the (4a)/(85) DAT rule); Mongolian has nonstructural
    DAT supplied by the lexicon. The cross-Turkic/Mongolic contrast
    localizes to a single config parameter. -/
theorem yakut_vs_mongolian_localized :
    yakutCaseConfig.langType = .accusative ∧
    yakutCaseConfig.nomMode  = .agreeT ∧
    yakutCaseConfig.accMode  = .dependent ∧
    yakutCaseConfig.genMode  = .agreeD := ⟨rfl, rfl, rfl, rfl⟩

end Fragments.Yakut.Case
