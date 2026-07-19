import Linglib.Syntax.DependencyGrammar.Formal.HarmonicOrder
import Linglib.Data.WALS.Features.F95A
import Linglib.Data.UD.Basic
import Linglib.Features.WordOrder
import Linglib.Morphology.Word.Basic

open Morphology (Word)

/-!
# Gibson 2025: DLM and the Head-Direction Generalization
[gibson-2025] [dryer-1992] [greenberg-1963] [dryer-haspelmath-2013]

[gibson-2025] argues that Dependency Length Minimization (DLM) explains
the head-direction generalization originally documented by [greenberg-1963]
and systematized by [dryer-1992]: languages overwhelmingly prefer
consistent (harmonic) head direction across construction types, because
disharmonic order incurs higher total dependency length on recursive structures.

This file owns Gibson's quantitative argument: the WALS-derived count tables
he uses (Tables 1–3, plus the Single-Word-Exceptions discussion at Table 4),
the per-table harmonic-dominance theorems, the head-direction-generalization
statement over those tables, and the DLM-vs-WALS consistency theorems that
package the central claim. The DLM apparatus itself lives in
`Syntax/DependencyGrammar/Formal/HarmonicOrder.lean`.

## Cross-tabulation apparatus

The `AlignmentCell` / `CrossTab` 2×2 head-direction tabulation types are
defined here as paper-anchored apparatus rather than substrate, since the
only consumers are this paper plus the Levshina-style gradient extension
(`Studies/LevshinaEtAl2023.lean`). They will be promoted to
`Features/WordOrder.lean` substrate when a second paper-independent
consumer materialises (e.g., a `FOFC.lean`, a `Hawkins1983.lean`, or a
systematic WALS Ch 95/96/97 ingestion that needs the type at substrate
level).

## Substrate-derivation evidence: WALS Ch 95

`fromWALSCh95` constructs a `CrossTab` directly from
`Data.WALS.F95A.allData` (verb-object × adposition correlation;
[dryer-haspelmath-2013] Ch 95). This is internal evidence that
Gibson's hand-coded Table 1 corresponds to the substrate-derivable
form: same correlation, same harmonic-dominance conclusion. Counts
differ in magnitude (Gibson 981 = 454+41+14+472; WALS Ch 95 raw =
984 = 456+42+14+472, the residual ~3 absorbed in Gibson's reporting
and ~158 "Other" languages excluded by Gibson). Cell *pairings* match
exactly: hihf = HI×HF = (VO, postpositions); hfhi = HF×HI = (OV,
prepositions). `Studies/DryerHaspelmath2013.lean`
has its own aggregate-count `ch95_harmonic_dominant` theorem at higher
stringency (>16×); chronological dependency rules prohibit DH2013
importing this file, so it is not currently wired through.
-/

namespace Gibson2025


open DepGrammar DependencyLength DepGrammar.HarmonicOrder

-- ============================================================================
-- §0. Cross-tabulation apparatus (paper-anchored substrate)
-- ============================================================================

/-- A single cell in a 2×2 head-direction cross-tabulation. `dir1`
    and `dir2` are the head directions of two construction types being
    correlated. The struct does not enforce that `dir1` / `dir2`
    originate from genuinely head-direction-bearing constructions;
    consumers carry that contract. -/
structure AlignmentCell where
  dir1 : HeadDirection
  dir2 : HeadDirection
  count : Nat
  deriving Repr, DecidableEq

/-- A cell is harmonic when both constructions take the same head
    direction. -/
def AlignmentCell.IsHarmonic (c : AlignmentCell) : Prop :=
  c.dir1 = c.dir2

instance : DecidablePred AlignmentCell.IsHarmonic := fun c =>
  decEq c.dir1 c.dir2

/-- A 2×2 cross-tabulation of two head-direction-bearing construction
    types (e.g., verb-object × adposition). The four cells enumerate
    the head-initial / head-final combinations. -/
structure CrossTab where
  name : String
  construction1 : String
  construction2 : String
  hihi : AlignmentCell    -- both head-initial
  hihf : AlignmentCell    -- construction 1 HI, construction 2 HF
  hfhi : AlignmentCell    -- construction 1 HF, construction 2 HI
  hfhf : AlignmentCell    -- both head-final
  deriving Repr

/-- Total count of harmonic (diagonal) cells. -/
def CrossTab.harmonicCount (t : CrossTab) : Nat :=
  t.hihi.count + t.hfhf.count

/-- Total count of disharmonic (off-diagonal) cells. -/
def CrossTab.disharmonicCount (t : CrossTab) : Nat :=
  t.hihf.count + t.hfhi.count

/-- Total number of languages in the table. -/
def CrossTab.totalCount (t : CrossTab) : Nat :=
  t.harmonicCount + t.disharmonicCount

/-- Harmonic pairings strictly outnumber disharmonic. A *raw-count*
    primitive; serious typological generalisations require sample-bias
    correction (cf. [dryer-1992]'s genus method). -/
def CrossTab.IsHarmonicDominant (t : CrossTab) : Prop :=
  t.harmonicCount > t.disharmonicCount

instance : DecidablePred CrossTab.IsHarmonicDominant := fun _ =>
  Nat.decLt _ _

-- ============================================================================
-- §1. Gibson Tables 1–3: WALS cross-tabulations
-- ============================================================================
-- Each table is a 2×2 head-direction contingency: VO/OV × HI/HF for the second
-- construction. Hand-coded from Gibson 2025's reproduction of the WALS counts.

/-- Gibson Table 1: Verb-Object order × Adposition order (981 languages). -/
def voAdposition : CrossTab :=
  { name := "VO × Adposition"
    construction1 := "Verb-Object"
    construction2 := "Adposition"
    hihi := ⟨.headInitial, .headInitial, 454⟩
    hihf := ⟨.headInitial, .headFinal, 41⟩
    hfhi := ⟨.headFinal, .headInitial, 14⟩
    hfhf := ⟨.headFinal, .headFinal, 472⟩ }

/-- Gibson Table 2: Verb-Object order × Subordinator order (456 languages). -/
def voSubordinator : CrossTab :=
  { name := "VO × Subordinator"
    construction1 := "Verb-Object"
    construction2 := "Subordinator"
    hihi := ⟨.headInitial, .headInitial, 302⟩
    hihf := ⟨.headInitial, .headFinal, 2⟩
    hfhi := ⟨.headFinal, .headInitial, 61⟩
    hfhf := ⟨.headFinal, .headFinal, 91⟩ }

/-- Gibson Table 3: Verb-Object order × Relative clause order (665 languages). -/
def voRelativeClause : CrossTab :=
  { name := "VO × Relative clause"
    construction1 := "Verb-Object"
    construction2 := "Relative clause"
    hihi := ⟨.headInitial, .headInitial, 415⟩
    hihf := ⟨.headInitial, .headFinal, 5⟩
    hfhi := ⟨.headFinal, .headInitial, 113⟩
    hfhf := ⟨.headFinal, .headFinal, 132⟩ }

/-- All three Gibson cross-tabulations. -/
def allTables : List CrossTab :=
  [voAdposition, voSubordinator, voRelativeClause]

-- ============================================================================
-- §2. Per-table harmonic dominance
-- ============================================================================

/-- Table 1: harmonic (926) > disharmonic (55). -/
theorem voAdposition_harmonic_dominant :
    voAdposition.IsHarmonicDominant := by decide

/-- Table 2: harmonic (393) > disharmonic (63). -/
theorem voSubordinator_harmonic_dominant :
    voSubordinator.IsHarmonicDominant := by decide

/-- Table 3: harmonic (547) > disharmonic (118). -/
theorem voRelativeClause_harmonic_dominant :
    voRelativeClause.IsHarmonicDominant := by decide

/-- Harmonic cells have matching directions. -/
theorem hihi_is_harmonic : voAdposition.hihi.IsHarmonic := by decide
theorem hfhf_is_harmonic : voAdposition.hfhf.IsHarmonic := by decide

/-- Disharmonic cells have mismatched directions. -/
theorem hihf_is_disharmonic : ¬ voAdposition.hihf.IsHarmonic := by decide
theorem hfhi_is_disharmonic : ¬ voAdposition.hfhi.IsHarmonic := by decide

-- ============================================================================
-- §3. The Head-Direction Generalization ([greenberg-1963] / [dryer-1992])
-- ============================================================================

/-- The head-direction generalization: across all three of Gibson's
    construction-pair tables, harmonic word-order pairings dominate. The
    underlying observation goes back to [greenberg-1963] and was
    systematized by [dryer-1992]; [gibson-2025] argues DLM explains
    it (consistent head direction keeps recursive spine dependencies local). -/
theorem head_direction_generalization :
    ∀ t ∈ allTables, t.IsHarmonicDominant := by decide

-- ============================================================================
-- §4. Single-Word Exceptions (Gibson Table 4)
-- ============================================================================

/-- Construction types where disharmonic order is common (Gibson's Table 4).

    These are cases where the dependent is typically a single word (no
    recursive subtree), so head direction doesn't affect DLM. Gibson's
    argument: DLM only cares about direction when subtrees intervene
    between head and dependent. -/
inductive SingleWordException where
  /-- adjective-noun: many VO languages have Adj-N (head-final order). -/
  | adjN
  /-- demonstrative-noun: many OV languages have Dem-N (head-initial order). -/
  | demN
  /-- intensifier-adjective: "very tall" is head-initial in many OV languages. -/
  | intensAdj
  /-- negator-verb: "not run" is head-initial in many OV languages. -/
  | negVerb
  deriving Repr, DecidableEq

/-- All single-word exceptions from Gibson Table 4. -/
def singleWordExceptions : List SingleWordException :=
  [.adjN, .demN, .intensAdj, .negVerb]

/-- These exceptions all involve dependents that are typically single words
    (leaves in the dependency tree), not recursive phrases. -/
def isSingleWordDependent : SingleWordException → Prop
  | .adjN      => True
  | .demN      => True
  | .intensAdj => True
  | .negVerb   => True

instance : DecidablePred isSingleWordDependent := fun x => by
  cases x <;> unfold isSingleWordDependent <;> infer_instance

theorem all_exceptions_single_word :
    ∀ e ∈ singleWordExceptions, isSingleWordDependent e := by decide

-- ============================================================================
-- §5. DLM-vs-WALS consistency: Gibson's central claim
-- ============================================================================

/-- WALS confirms harmonic order is more common, for a given table. -/
def walsConfirmsHarmonic (t : CrossTab) : Bool :=
  decide t.IsHarmonicDominant

/-- Combined consistency check: DLM prediction and WALS observation agree. -/
def dlmWalsConsistent (t : CrossTab) : Bool :=
  dlmPredictsHarmonicCheaper && walsConfirmsHarmonic t

/-- For all three of Gibson's construction pairs, DLM predicts harmonic is
    cheaper AND WALS confirms harmonic is more common. This is
    [gibson-2025]'s central claim: DLM explains the head-direction
    generalization. -/
theorem dlm_explains_head_direction_generalization :
    allTables.all dlmWalsConsistent = true := by decide

/-- Per-table DLM-WALS consistency theorems. -/
theorem vo_adposition_consistent :
    dlmWalsConsistent voAdposition = true := by decide

theorem vo_subordinator_consistent :
    dlmWalsConsistent voSubordinator = true := by decide

theorem vo_relative_clause_consistent :
    dlmWalsConsistent voRelativeClause = true := by decide

-- ============================================================================
-- §6. Bridge to DependencyLength.lean's HarmonicOrder examples
-- ============================================================================

/-- The harmonic tree examples are well-formed (unique heads, acyclic). -/
example : hasUniqueHeads harmonicHI = true := by native_decide
example : hasUniqueHeads harmonicHF = true := by native_decide
example : hasUniqueHeads disharmonicHF = true := by native_decide
example : hasUniqueHeads disharmonicFH = true := by native_decide

/-- All four trees are projective (no crossing arcs). The disharmonic ones
    are longer NOT because of non-projectivity, but because consistent
    direction is a separate (stronger) constraint. -/
example : isProjective harmonicHI = true := by native_decide
example : isProjective harmonicHF = true := by native_decide
example : isProjective disharmonicHF = true := by native_decide
example : isProjective disharmonicFH = true := by native_decide

/-- Bridge to Behaghel: harmonic trees satisfy Oberstes Gesetz with
    threshold 2 (no dep longer than 2). Disharmonic trees do not. -/
example : oberstesGesetz harmonicHI 2 = true := by native_decide
example : oberstesGesetz harmonicHF 2 = true := by native_decide
example : oberstesGesetz disharmonicHF 2 = false := by native_decide
example : oberstesGesetz disharmonicFH 2 = false := by native_decide

-- ============================================================================
-- §7. WALS Ch 95 → CrossTab bridge (substrate-derived counterpart)
-- ============================================================================

/-- Build a `CrossTab` for WALS Ch 95 (verb-object × adposition) by
    counting datapoints in each of the four cells of
    [dryer-haspelmath-2013]'s WALS Ch 95. The same underlying
    correlation viewed via raw WALS counts rather than Gibson's
    hand-coded snapshot. -/
def CrossTab.fromWALSCh95 : CrossTab :=
  let data := Data.WALS.F95A.allData
  let voPrep   := (data.filter (·.value == .voAndPrepositions)).length
  let voPostp  := (data.filter (·.value == .voAndPostpositions)).length
  let ovPrep   := (data.filter (·.value == .ovAndPrepositions)).length
  let ovPostp  := (data.filter (·.value == .ovAndPostpositions)).length
  { name := "WALS Ch 95: VO × Adposition"
    construction1 := "Verb-Object"
    construction2 := "Adposition"
    hihi := ⟨.headInitial, .headInitial, voPrep⟩
    hihf := ⟨.headInitial, .headFinal, voPostp⟩
    hfhi := ⟨.headFinal, .headInitial, ovPrep⟩
    hfhf := ⟨.headFinal, .headFinal, ovPostp⟩ }

set_option maxRecDepth 8192 in
/-- The substrate-derived Ch 95 CrossTab is harmonic-dominant — the
    same fact `voAdposition_harmonic_dominant` proves over Gibson's
    hand-coded counts, restated over the WALS-derived form. The
    substrate-side claim is `harmonicCount > disharmonicCount`; the
    aggregate-count form in `DryerHaspelmath2013.ch95_harmonic_dominant`
    proves the stronger 16-to-1 dominance. -/
theorem fromWALSCh95_harmonic_dominant :
    CrossTab.fromWALSCh95.IsHarmonicDominant := by decide

end Gibson2025
