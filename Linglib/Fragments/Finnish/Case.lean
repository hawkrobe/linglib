import Linglib.Features.Case.Basic
import Linglib.Features.Case.Grammaticalization
import Linglib.Syntax.Case.Order

/-!
# Finnish Case Inventory [blake-1994]
[karlsson-2017]

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

Our 19-value `Case` represents 12 of the 15 Finnish cases. The three
Finnish-specific semantic cases (essive, translative, abessive) are included
directly; the internal/external local pairs (inessive/adessive → LOC,
elative/ablative → ABL, illative/allative → ALL) are collapsed into a
single rank.

Finnish lacks a dedicated **dative** case — the allative covers recipient
function ([blake-1994], Ch. 6: ALL → DAT extension). This creates a gap at
rank 4 (DAT) on Blake's hierarchy, making Finnish a known exception to
strict contiguity.

-/

namespace Finnish.Case

-- ============================================================================
-- § 1: Case Inventory
-- ============================================================================

/-- Finnish case inventory mapped to `Case`.

    All 15 Finnish cases now have Case equivalents (essive, translative,
    abessive added to Case; internal/external local pairs collapsed):
    - NOM →.nom, ACC →.acc (pronoun/total-object accusative)
    - GEN →.gen, PART →.part
    - the 6 local cases as *distinct* cells: INE/ELA/ILL (interior),
      ADE/ABL/ALL (exterior) — via the shared `Region × PathDir`
      decomposition (`Syntax/Case/Order.lean`)
    - ESS →.ess, TRANSL →.transl, ABESS →.abess
    - INSTR →.inst, COM →.com -/
def caseInventory : Finset Case :=
  {.nom, .acc, .gen, .part, .ine, .ade, .ela, .abl, .ill, .all,
   .ess, .transl, .abess, .inst, .com}

/-- Finnish's inventory **fails** strict contiguity: the spatial tier
    (rank ≤ 2) and GEN/core (rank ≥ 5) have no LOC (rank 3) or DAT
    (rank 4) between them. Finnish uses allative for recipient function
    instead of a dedicated dative.

    This illustrates Blake's hedge: the hierarchy holds "usually" but
    languages like Finnish fill the dative slot with a local case
    extension (ALL → DAT, formalized in `Case.Extends`). -/
theorem inventory_fails_strict :
    ¬ Case.IsValidInventory caseInventory := by decide

/-- The allative-for-dative substitution is exactly the extension path
    in [heine-2009] Table 29.6, formalized in `Case.Extends`. -/
theorem allative_extends_to_dative :
    Case.Extends .all .dat := by decide

-- ============================================================================
-- § 2: Syncretism
-- ============================================================================

theorem abl_inst_distinct :
    Case.HierarchyAdjacent .abl .inst := by decide

-- ============================================================================
-- § 3: Local Case Matrix (3 × 2)
-- ============================================================================

/-- Direction of motion/relation in the Finnish local case system.
    [karlsson-2017]: the three directional dimensions —
    static location, source of motion, and goal of motion. -/
inductive Direction where
  | static   -- at/in/on (no motion)
  | source   -- from/out of/off (motion away)
  | goal     -- to/into/onto (motion toward)
  deriving DecidableEq, Repr, Inhabited

/-- Location type: whether the spatial relation is conceptualized as
    internal (containment) or external (surface/proximity).
    [karlsson-2017]: Finnish systematically distinguishes
    "inside" (inessive/elative/illative) from "at/on" (adessive/ablative/allative). -/
inductive LocationType where
  | internal  -- containment: in, out of, into
  | external  -- surface/proximity: on/at, off/from, to/onto
  deriving DecidableEq, Repr, Inhabited

/-- A cell in the Finnish local case matrix: the case name, suffix,
    directional coordinates, and mapping to `Case`. -/
structure LocalCase where
  name : String
  suffix : String
  direction : Direction
  locationType : LocationType
  coreCase : Case
  deriving DecidableEq, Repr, Inhabited

/-- The Finnish directional dimension as the shared `Case.PathDir`
    (static = the locative Place base). -/
def Direction.toPathDir : Direction → Case.PathDir
  | .static => .place
  | .source => .source
  | .goal => .goal

/-- The Finnish location type as the shared `Case.Region`. -/
def LocationType.toRegion : LocationType → Case.Region
  | .internal => .interior
  | .external => .exterior

/-- The 3×2 local case matrix, mapping each cell to its *distinct* `Case`
    via the shared `Region × PathDir` decomposition
    (`Syntax/Case/Order.lean`) — no longer collapsing internal/external
    (cf. the deleted `static_collapses_to_loc`).

    |           | Internal      | External      |
    |-----------|---------------|---------------|
    | Static    | inessive -ssA | adessive -llA |
    | Source    | elative -stA  | ablative -ltA |
    | Goal      | illative -Vn  | allative -lle | -/
def localCaseMatrix : Direction → LocationType → LocalCase
  | .static, .internal => ⟨"inessive",  "-ssA", .static, .internal, .ine⟩
  | .static, .external => ⟨"adessive",  "-llA", .static, .external, .ade⟩
  | .source, .internal => ⟨"elative",   "-stA", .source, .internal, .ela⟩
  | .source, .external => ⟨"ablative",  "-ltA", .source, .external, .abl⟩
  | .goal,   .internal => ⟨"illative",  "-Vn",  .goal,   .internal, .ill⟩
  | .goal,   .external => ⟨"allative",  "-lle", .goal,   .external, .all⟩

/-- All 6 local cases as a flat list. -/
def allLocalCases : List LocalCase :=
  [ localCaseMatrix .static .internal
  , localCaseMatrix .static .external
  , localCaseMatrix .source .internal
  , localCaseMatrix .source .external
  , localCaseMatrix .goal   .internal
  , localCaseMatrix .goal   .external ]

/-- Each cell's `Case` is exactly what the shared `Case.toCase`
    decomposition builds from its `Region × PathDir` coordinates — the
    matrix is the shared spatial decomposition, not a private table. -/
theorem coreCase_eq_toCase (d : Direction) (l : LocationType) :
    some (localCaseMatrix d l).coreCase =
      Case.toCase l.toRegion d.toPathDir := by
  cases d <;> cases l <;> rfl

/-- The 6 local cases are 6 *distinct* `Case` cells — the faithful
    decomposition keeps internal and external apart (the lossy collapse
    of the old `*_collapses_to_*` theorems is gone). -/
theorem localCases_distinct :
    (allLocalCases.map LocalCase.coreCase).Nodup := by decide

/-- All 6 local cases appear in the full Finnish inventory. -/
theorem localCases_subset_inventory :
    ∀ lc ∈ allLocalCases, lc.coreCase ∈ caseInventory := by decide

/-- Within each direction, internal and external suffixes differ. -/
theorem internal_external_distinct (d : Direction) :
    (localCaseMatrix d .internal).suffix ≠ (localCaseMatrix d .external).suffix := by
  cases d <;> decide

end Finnish.Case
