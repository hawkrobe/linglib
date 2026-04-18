import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
import Linglib.Theories.Interfaces.Morphosyntax.CaseContainment
open Interfaces.Morphosyntax.CaseContainment

/-!
# Telugu Case Inventory
@cite{krishnamurti-gwynn-1985} @cite{mcfadden-2018}

Telugu (Dravidian) has **5 core cases** with agglutinative suffixes:
NOM (∅), ACC (-ni), GEN (∅), DAT (-ki), and a locative postposition
(-lō 'in'). @cite{krishnamurti-gwynn-1985} list these as the
productive case/postposition forms for modern Telugu nominals.

Like Tamil and other Dravidian languages, Telugu shows a robust
**NOM-vs-oblique split** in stem allomorphy: the nominative stem
form differs from the form used in all nonnominative contexts
(@cite{mcfadden-2018}). This split is predicted by the case containment
hierarchy (@cite{caha-2009}), where all nonnominative cases include
the ACC feature in their syntactic representation.

See `Phenomena/Allomorphy/Studies/Aitha2026.lean` for
the full analysis of Telugu stem allomorphy patterns.
-/

namespace Fragments.Telugu.Case

-- ============================================================================
-- § 1: Case Inventory
-- ============================================================================

/-- Telugu 5-case core inventory.
    ACC, GEN, DAT are inflectional suffixes within the prosodic word;
    LOC is realized by a postposition (-lō) in a separate prosodic word. -/
def caseInventory : Finset Core.Case :=
  {.nom, .acc, .gen, .dat, .loc}

-- Contiguous on Blake's hierarchy (ranks 6 down to 3).
example : Core.Case.IsValidInventory caseInventory := by decide

-- ============================================================================
-- § 2: Containment Properties
-- ============================================================================

/-- All nonnominative Telugu cases bear the ACC feature. -/
theorem acc_nonnom : Core.Case.IsNonnominative .acc := by decide
theorem gen_nonnom : Core.Case.IsNonnominative .gen := by decide
theorem dat_nonnom : Core.Case.IsNonnominative .dat := by decide
theorem loc_nonnom : Core.Case.IsNonnominative .loc := by decide
theorem nom_not_nonnom : ¬ Core.Case.IsNonnominative .nom := by decide

/-- Telugu's NOM-vs-oblique split is an ABB pattern — contiguous on the
    containment hierarchy, consistent with case-conditioned VI. -/
theorem nom_vs_oblique_contiguous :
    (AllomorphyPattern.mk 0 1 1 1).isContiguous = true := by native_decide

-- ============================================================================
-- § 3: Cross-Dravidian Connection
-- ============================================================================

/-- Telugu and Tamil share the same core case spine on Blake's hierarchy.
    Both have NOM, ACC, GEN, DAT, LOC (Tamil additionally has ABL, INST, COM). -/
theorem telugu_subset_tamil :
    caseInventory ⊆ ({.nom, .acc, .gen, .dat, .loc, .abl, .inst, .com} : Finset Core.Case) := by
  decide

end Fragments.Telugu.Case
