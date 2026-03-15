import Linglib.Core.Case
import Linglib.Theories.Morphology.CaseContainment
open Theories.Morphology.CaseContainment

/-!
# Finnish Case Inventory @cite{blake-1994}
@cite{karlsson-2017}

Finnish has **15 morphological cases**, one of the richest
case systems in Europe:

- **Grammatical** (3): nominative, genitive, partitive (+ accusative for
  pronouns/total objects, often syncretic with NOM or GEN)
- **Internal local** (3): inessive (-ssA, 'in'), elative (-stA, 'out of'),
  illative (-Vn, 'into')
- **External local** (3): adessive (-llA, 'on/at'), ablative (-ltA, 'from'),
  allative (-lle, 'to/onto')
- **Other** (5–6): essive (-nA, 'as'), translative (-ksi, 'becoming'),
  abessive (-ttA, 'without'), comitative (-ine-, 'with'),
  instructive (-n, 'by means of')

Our 19-value `Core.Case` represents 12 of the 15 Finnish cases. The three
Finnish-specific semantic cases (essive, translative, abessive) are included
directly; the internal/external local pairs (inessive/adessive → LOC,
elative/ablative → ABL, illative/allative → ALL) are collapsed into a
single rank.

Finnish lacks a dedicated **dative** case — the allative covers recipient
function (@cite{blake-1994}, Ch. 6: ALL → DAT extension). This creates a gap at
rank 4 (DAT) on Blake's hierarchy, making Finnish a known exception to
strict contiguity.

-/

namespace Fragments.Finnish.Case

-- ============================================================================
-- § 1: Case Inventory
-- ============================================================================

/-- Finnish case inventory mapped to `Core.Case`.

    All 15 Finnish cases now have Core.Case equivalents (essive, translative,
    abessive added to Core.Case; internal/external local pairs collapsed):
    - NOM →.nom, ACC →.acc (pronoun/total-object accusative)
    - GEN →.gen, PART →.part
    - INE/ADE →.loc, ELA/ABL →.abl, ILL/ALL →.all
    - ESS →.ess, TRANSL →.transl, ABESS →.abess
    - INSTR →.inst, COM →.com -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .part, .loc, .abl, .all, .ess, .transl, .abess, .inst, .com]

/-- Finnish's mapped inventory **fails** strict contiguity: GEN (rank 5)
    and LOC (rank 3) have no DAT (rank 4) between them. Finnish uses
    allative for recipient function instead of a dedicated dative.

    This illustrates Blake's hedge: the hierarchy holds "usually" but
    languages like Finnish fill the dative slot with a local case
    extension (ALL → DAT, formalized in `LocalExtension.lean`). -/
theorem inventory_fails_strict :
    Core.validInventory caseInventory = false := by native_decide

/-- The allative-for-dative substitution is exactly the extension path
    formalized in `Core.localExtension`. -/
theorem allative_extends_to_dative :
    Core.Case.dat ∈ Core.localExtension .all := by simp [Core.localExtension]

-- ============================================================================
-- § 2: Syncretism
-- ============================================================================

/-- Finnish NOM/ACC syncretism: the accusative of non-pronominal singular
    nouns is identical to the nominative.
    Uses the cross-linguistic pattern from `Core.Case.Syncretism`. -/
def finnishNomAccSync : Syncretism := nomAccSyncretism

/-- Finnish ABL/INST are not syncretic — ablative (-ltA) and instructive
    (-n) are distinct forms. Unlike many IE languages where ABL and INST
    merge, Finnish keeps them separate. -/
theorem abl_inst_distinct :
    hierarchyAdjacent .abl .inst = true := by native_decide

-- ============================================================================
-- § 3: Local Case Matrix (3 × 2)
-- ============================================================================

/-- Direction of motion/relation in the Finnish local case system.
    @cite{karlsson-2017}: the three directional dimensions —
    static location, source of motion, and goal of motion. -/
inductive Direction where
  | static   -- at/in/on (no motion)
  | source   -- from/out of/off (motion away)
  | goal     -- to/into/onto (motion toward)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Location type: whether the spatial relation is conceptualized as
    internal (containment) or external (surface/proximity).
    @cite{karlsson-2017}: Finnish systematically distinguishes
    "inside" (inessive/elative/illative) from "at/on" (adessive/ablative/allative). -/
inductive LocationType where
  | internal  -- containment: in, out of, into
  | external  -- surface/proximity: on/at, off/from, to/onto
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A cell in the Finnish local case matrix: the case name, suffix,
    directional coordinates, and mapping to `Core.Case`. -/
structure LocalCase where
  name : String
  suffix : String
  direction : Direction
  locationType : LocationType
  coreCase : Core.Case
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The 3×2 local case matrix.

    |           | Internal     | External     |
    |-----------|-------------|-------------|
    | Static    | inessive -ssA | adessive -llA |
    | Source    | elative -stA  | ablative -ltA |
    | Goal      | illative -Vn  | allative -lle |

    Core.Case collapses each row into a single value (static →.loc,
    source →.abl, goal →.all). The matrix reveals the full structure. -/
def localCaseMatrix : Direction → LocationType → LocalCase
  | .static, .internal => ⟨"inessive",  "-ssA", .static, .internal, .loc⟩
  | .static, .external => ⟨"adessive",  "-llA", .static, .external, .loc⟩
  | .source, .internal => ⟨"elative",   "-stA", .source, .internal, .abl⟩
  | .source, .external => ⟨"ablative",  "-ltA", .source, .external, .abl⟩
  | .goal,   .internal => ⟨"illative",  "-Vn",  .goal,   .internal, .all⟩
  | .goal,   .external => ⟨"allative",  "-lle", .goal,   .external, .all⟩

/-- All 6 local cases as a flat list. -/
def allLocalCases : List LocalCase :=
  [ localCaseMatrix .static .internal
  , localCaseMatrix .static .external
  , localCaseMatrix .source .internal
  , localCaseMatrix .source .external
  , localCaseMatrix .goal   .internal
  , localCaseMatrix .goal   .external ]

/-- The matrix has exactly 6 cells. -/
theorem localCases_count : allLocalCases.length = 6 := by native_decide

/-- Core.Case collapses each direction row: both internal and external
    static cases map to.loc. -/
theorem static_collapses_to_loc :
    (localCaseMatrix .static .internal).coreCase =
    (localCaseMatrix .static .external).coreCase := rfl

/-- Both source cases map to.abl. -/
theorem source_collapses_to_abl :
    (localCaseMatrix .source .internal).coreCase =
    (localCaseMatrix .source .external).coreCase := rfl

/-- Both goal cases map to.all. -/
theorem goal_collapses_to_all :
    (localCaseMatrix .goal .internal).coreCase =
    (localCaseMatrix .goal .external).coreCase := rfl

/-- All 6 local cases appear in the full Finnish inventory. -/
theorem localCases_subset_inventory :
    allLocalCases.all (fun lc => caseInventory.any (· == lc.coreCase)) = true := by native_decide

/-- Within each direction, internal and external suffixes differ. -/
theorem internal_external_distinct (d : Direction) :
    (localCaseMatrix d .internal).suffix ≠ (localCaseMatrix d .external).suffix := by
  cases d <;> decide

end Fragments.Finnish.Case
