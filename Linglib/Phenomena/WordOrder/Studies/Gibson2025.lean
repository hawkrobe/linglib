import Linglib.Theories.Syntax.DependencyGrammar.Formal.HarmonicOrder
import Linglib.Typology.WordOrder

/-!
# Gibson 2025: DLM and the Head-Direction Generalization
@cite{gibson-2025} @cite{dryer-1992} @cite{greenberg-1963} @cite{dryer-haspelmath-2013}

@cite{gibson-2025} argues that Dependency Length Minimization (DLM) explains
the head-direction generalization originally documented by @cite{greenberg-1963}
and systematized by @cite{dryer-1992}: languages overwhelmingly prefer
consistent (harmonic) head direction across construction types, because
disharmonic order incurs higher total dependency length on recursive structures.

This file owns Gibson's quantitative argument: the WALS-derived count tables
he uses (Tables 1–3, plus the Single-Word-Exceptions discussion at Table 4),
the per-table harmonic-dominance theorems, the head-direction-generalization
statement over those tables, and the DLM-vs-WALS consistency theorems that
package the central claim. The DLM apparatus itself lives in
`Theories/Syntax/DependencyGrammar/Formal/HarmonicOrder.lean`.

Substrate types `CrossTab` / `AlignmentCell` plus `harmonicCount` /
`disharmonicCount` / `harmonicDominant` helpers live in
`Linglib/Typology/WordOrder.lean` (substrate, theory-neutral 2×2 contingency
tables; consumers like `Phenomena/WordOrder/Gradience.lean` import them
directly).

This file was previously named `Studies/Dryer1992.lean` but the content was
already Gibson 2025 in nature (DLM + WALS counts + the central
DLM-explains-Greenberg theorem) — renamed to fix the chronology violation
(Dryer 1992 cannot cite a 2025 paper or a 2013 atlas).
-/

namespace Phenomena.WordOrder.Studies.Gibson2025

open DepGrammar DependencyLength DepGrammar.HarmonicOrder
open Typology.WordOrder

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
    voAdposition.harmonicDominant = true := by decide

/-- Table 2: harmonic (393) > disharmonic (63). -/
theorem voSubordinator_harmonic_dominant :
    voSubordinator.harmonicDominant = true := by decide

/-- Table 3: harmonic (547) > disharmonic (118). -/
theorem voRelativeClause_harmonic_dominant :
    voRelativeClause.harmonicDominant = true := by decide

/-- Harmonic cells have matching directions. -/
theorem hihi_is_harmonic : voAdposition.hihi.isHarmonic = true := by decide
theorem hfhf_is_harmonic : voAdposition.hfhf.isHarmonic = true := by decide

/-- Disharmonic cells have mismatched directions. -/
theorem hihf_is_disharmonic : voAdposition.hihf.isHarmonic = false := by decide
theorem hfhi_is_disharmonic : voAdposition.hfhi.isHarmonic = false := by decide

-- ============================================================================
-- §3. The Head-Direction Generalization (@cite{greenberg-1963} / @cite{dryer-1992})
-- ============================================================================

/-- The head-direction generalization: across all three of Gibson's
    construction-pair tables, harmonic word-order pairings dominate. The
    underlying observation goes back to @cite{greenberg-1963} and was
    systematized by @cite{dryer-1992}; @cite{gibson-2025} argues DLM explains
    it (consistent head direction keeps recursive spine dependencies local). -/
theorem head_direction_generalization :
    allTables.all CrossTab.harmonicDominant = true := by decide

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
  t.harmonicDominant

/-- Combined consistency check: DLM prediction and WALS observation agree. -/
def dlmWalsConsistent (t : CrossTab) : Bool :=
  dlmPredictsHarmonicCheaper && walsConfirmsHarmonic t

/-- For all three of Gibson's construction pairs, DLM predicts harmonic is
    cheaper AND WALS confirms harmonic is more common. This is
    @cite{gibson-2025}'s central claim: DLM explains the head-direction
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

end Phenomena.WordOrder.Studies.Gibson2025
