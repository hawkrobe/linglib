import Linglib.Theories.Pragmatics.Implicature.Core.Markedness
import Linglib.Phenomena.Gradability.Studies.Rett2015

/-!
# Bridge: NeoGricean Alternatives → M-Alternative Verification
@cite{horn-1984} @cite{rett-2015}

Verifies M-alternative generation for concrete adjective pairs.

Tests that the M-alternative framework correctly identifies:
- Which constructions have M-alternatives (equatives, degree questions)
- Which constructions lack M-alternatives (comparatives, positives)
- Which form is marked in M-alternative pairs

-/

namespace Phenomena.Gradability.Implicature_AlternativesBridge

open Implicature.Markedness


/--
M-alternatives exist in equative constructions.
-/
theorem equative_has_m_alternatives :
    (generateMAlternatives tall_with_morphology short_with_morphology .equative).isSome = true := by
  native_decide

/--
M-alternatives exist in degree question constructions.
-/
theorem question_has_m_alternatives :
    (generateMAlternatives tall_with_morphology short_with_morphology .degreeQuestion).isSome = true := by
  native_decide

/--
M-alternatives do NOT exist in comparative constructions.
-/
theorem comparative_no_m_alternatives :
    (generateMAlternatives tall_with_morphology short_with_morphology .comparative).isNone = true := by
  native_decide

/--
M-alternatives do NOT exist in positive constructions.
-/
theorem positive_no_m_alternatives :
    (generateMAlternatives tall_with_morphology short_with_morphology .positive).isNone = true := by
  native_decide

/--
"short" is the marked member in equative M-alternatives.
-/
theorem short_is_marked_in_equative :
    isMarkedInMAlternatives "short" tall_with_morphology short_with_morphology .equative = true := by
  native_decide

/--
"tall" is NOT the marked member in equative M-alternatives.
-/
theorem tall_is_not_marked_in_equative :
    isMarkedInMAlternatives "tall" tall_with_morphology short_with_morphology .equative = false := by
  native_decide


end Phenomena.Gradability.Implicature_AlternativesBridge
