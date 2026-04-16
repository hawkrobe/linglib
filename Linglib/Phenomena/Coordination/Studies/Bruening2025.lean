import Linglib.Phenomena.Coordination.Studies.BrueningAlKhalaf2020

/-!
# @cite{bruening-2025} — Selectional Violations in Coordination: A Response

Bruening, Benjamin. 2025. Selectional violations in coordination:
A response to Patejuk and Przepiórkowski 2023. *Linguistic Inquiry*
56(3). 439–483.

## Three AMT Experiments

### Experiment 1a (n=65): Adverbs vs Adjectives in Prenominal Position

Tests whether non-*ly* adverbs can appear in prenominal coordination
with adjectives. The adverb condition is significantly degraded relative
to the adjective condition (t=7.28, p<.001) but more acceptable than
ungrammatical baselines, consistent with Adv↔Adj being a permitted but
marked selection violation.

### Experiment 1b (n=65, same participants): CPs in NP Positions

Tests the coordination rescue effect: CPs in DP-selecting positions
are more acceptable in coordination with DPs than alone. Coordination
condition significantly better than bare CP (t=5.575, p<.001).

### Experiment 2 (n=77): One-Replacement Test

Tests whether one-replacement accepts adverbs in coordination.
Adjective one-replacement is significantly more acceptable than adverb
one-replacement (t=6.895, p<.001).

## C-Selection Irreducibility (§4.1)

*become*/*grow*/*get*/*end up*/*turn out* have identical semantics
(change-of-state to property state) but different c-selectional profiles,
proving c-selection is not reducible to s-selection.
-/

namespace Bruening2025

open BrueningAlKhalaf2020
open Core.Tree (Cat)
open Core.Tree.Cat (NP AdvP AdjP)

-- ============================================================================
-- § 1: Experiment Data Structure
-- ============================================================================

/-- Condition-level descriptive statistics for AMT acceptability experiments.
    Z-scores stored as Int × 1000 (milli-z) for exact arithmetic. -/
structure ExpCondition where
  label : String
  meanZ : Int   -- z-score × 1000
  sdZ : Int     -- SD × 1000
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- § 2: Experiment 1a — Adverbs vs Adjectives in Prenominal Position
-- ============================================================================

/-- Experiment 1a: 65 AMT masters participants.
    Tests prenominal coordination [Adj and Adv] N.
    Data from Table 2 of @cite{bruening-2025}. -/
def exp1a_nParticipants : Nat := 65

def exp1a_control : ExpCondition :=
  { label := "Control (grammatical)", meanZ := 630, sdZ := 710 }

def exp1a_ungram : ExpCondition :=
  { label := "Ungrammatical", meanZ := -970, sdZ := 940 }

def exp1a_adj : ExpCondition :=
  { label := "Adjective coordination", meanZ := 870, sdZ := 400 }

def exp1a_adv : ExpCondition :=
  { label := "Adverb coordination", meanZ := -310, sdZ := 830 }

/-- Adjective coordination is more acceptable than adverb coordination. -/
theorem exp1a_adj_better_than_adv :
    exp1a_adj.meanZ > exp1a_adv.meanZ := by native_decide

/-- Adverb coordination is rated between grammatical and ungrammatical:
    not fully acceptable, but not as bad as outright ungrammaticality.
    This is consistent with adverb-as-adjective being a permitted but
    degraded selection violation (@cite{bruening-alkhalaf-2020} §3.2). -/
theorem exp1a_adv_intermediate :
    exp1a_adv.meanZ > exp1a_ungram.meanZ ∧
    exp1a_adv.meanZ < exp1a_control.meanZ :=
  ⟨by native_decide, by native_decide⟩

/-- Experiment 1a paired t-test (Adj vs Adv): t=7.28, df=8.35, p<.001. -/
def exp1a_tValue : Int := 7280  -- t × 1000
def exp1a_df : Int := 8350      -- df × 1000

-- ============================================================================
-- § 3: Experiment 1b — CPs in NP Positions
-- ============================================================================

/-- Experiment 1b: same 65 participants as Exp 1a.
    Tests CP in DP-selecting position: coordination vs simple.
    Data from Table 6 of @cite{bruening-2025}. -/
def exp1b_nParticipants : Nat := 65

def exp1b_control : ExpCondition :=
  { label := "Control (grammatical)", meanZ := 630, sdZ := 710 }

def exp1b_ungram : ExpCondition :=
  { label := "Ungrammatical", meanZ := -970, sdZ := 940 }

def exp1b_coord : ExpCondition :=
  { label := "DP-CP coordination", meanZ := 280, sdZ := 670 }

def exp1b_simple : ExpCondition :=
  { label := "Simple CP", meanZ := -500, sdZ := 740 }

/-- DP-CP coordination is more acceptable than bare CP: the coordination
    rescue effect. A CP that cannot appear alone in a DP-selecting
    position becomes acceptable when coordinated with a DP. -/
theorem exp1b_coord_rescues :
    exp1b_coord.meanZ > exp1b_simple.meanZ := by native_decide

/-- Bare CP is rated below grammatical control: it IS unacceptable
    without coordination rescue. -/
theorem exp1b_simple_degraded :
    exp1b_simple.meanZ < exp1b_control.meanZ := by native_decide

/-- Coordination rescue raises acceptability above the ungrammatical
    baseline. -/
theorem exp1b_coord_above_ungram :
    exp1b_coord.meanZ > exp1b_ungram.meanZ := by native_decide

/-- Experiment 1b paired t-test (Coord vs Simple): t=5.575, df=7.984, p<.001. -/
def exp1b_tValue : Int := 5575
def exp1b_df : Int := 7984

-- ============================================================================
-- § 4: Experiment 2 — One-Replacement Test
-- ============================================================================

/-- Experiment 2: 77 AMT masters participants.
    Tests one-replacement in [Adj and Adv] coordination.
    Data from Table 4 of @cite{bruening-2025}. -/
def exp2_nParticipants : Nat := 77

def exp2_filler_gram : ExpCondition :=
  { label := "Filler (grammatical)", meanZ := 750, sdZ := 670 }

def exp2_filler_ungram : ExpCondition :=
  { label := "Filler (ungrammatical)", meanZ := -780, sdZ := 870 }

def exp2_adj : ExpCondition :=
  { label := "Adjective one-replacement", meanZ := 360, sdZ := 630 }

def exp2_adv : ExpCondition :=
  { label := "Adverb one-replacement", meanZ := -490, sdZ := 720 }

/-- Adjective one-replacement is more acceptable than adverb
    one-replacement. -/
theorem exp2_adj_better_than_adv :
    exp2_adj.meanZ > exp2_adv.meanZ := by native_decide

/-- Adverb one-replacement is less acceptable than grammatical fillers
    but more acceptable than ungrammatical fillers. -/
theorem exp2_adv_intermediate :
    exp2_adv.meanZ > exp2_filler_ungram.meanZ ∧
    exp2_adv.meanZ < exp2_filler_gram.meanZ :=
  ⟨by native_decide, by native_decide⟩

/-- Experiment 2 paired t-test (Adj vs Adv): t=6.895, df=7.67, p<.001. -/
def exp2_tValue : Int := 6895
def exp2_df : Int := 7670

-- ============================================================================
-- § 5: Shared Controls Across Experiments 1a and 1b
-- ============================================================================

/-- Experiments 1a and 1b share the same participants and filler items.
    The identical control/ungrammatical baselines confirm this. -/
theorem shared_controls :
    exp1a_control.meanZ = exp1b_control.meanZ ∧
    exp1a_ungram.meanZ = exp1b_ungram.meanZ := ⟨rfl, rfl⟩

-- ============================================================================
-- § 6: C-Selection Irreducibility (§4.1)
-- ============================================================================

/-!
Five change-of-state verbs have identical semantics (transition to
property state) but different c-selectional profiles (§4.1):

- *become*: AP ✓, NP ✓ ("became rich", "became a doctor")
- *grow* (copular sense): AP ✓ only ("grew tired"; distinct from
  agentive *grow* "grow potatoes" which takes NP)
- *get*: AP ✓, PP ✓ ("got tired", "got into trouble")
- *end up*: AP ✓, PP ✓ ("ended up tired", "ended up in trouble")
- *turn out*: CP ✓ ("It turned out that...")

Since s-selection is identical (all select for a property state), the
variation must be c-selectional. This proves c-selection is irreducible
to s-selection, contra @cite{przepiorkowski-2024} who argue that
category mismatches in coordination reflect semantic rather than
syntactic selection.
-/

/-- C-selectional profile of a change-of-state predicate. -/
structure CSelProfile where
  verb : String
  takesAP : Bool
  takesNP : Bool
  takesPP : Bool
  takesCP : Bool
  deriving DecidableEq, Repr, BEq

def become : CSelProfile :=
  { verb := "become", takesAP := true, takesNP := true, takesPP := false, takesCP := false }

def grow_ : CSelProfile :=
  { verb := "grow", takesAP := true, takesNP := false, takesPP := false, takesCP := false }

def get_ : CSelProfile :=
  { verb := "get", takesAP := true, takesNP := false, takesPP := true, takesCP := false }

def endUp : CSelProfile :=
  { verb := "end up", takesAP := true, takesNP := false, takesPP := true, takesCP := false }

def turnOut : CSelProfile :=
  { verb := "turn out", takesAP := false, takesNP := false, takesPP := false, takesCP := true }

def changeOfStateVerbs : List CSelProfile :=
  [become, grow_, get_, endUp, turnOut]

/-- *turn out* and *become* have complementary c-selection profiles
    despite identical semantics: *become* takes AP/NP but not CP,
    *turn out* takes CP but not AP/NP. -/
theorem become_turnOut_complementary :
    become.takesAP = true ∧ become.takesCP = false ∧
    turnOut.takesAP = false ∧ turnOut.takesCP = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Not all five verbs share the same c-selection profile. -/
theorem cselection_varies :
    ¬(changeOfStateVerbs.all (· == become)) := by native_decide

/-- *get* and *end up* pattern together (both take AP and PP). -/
theorem get_endUp_same_profile :
    get_.takesAP = endUp.takesAP ∧ get_.takesNP = endUp.takesNP ∧
    get_.takesPP = endUp.takesPP ∧ get_.takesCP = endUp.takesCP :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 7: Bridge to B&AK 2020 Theory
-- ============================================================================

/-- All three experiments confirm B&AK's two-violation restriction:
    CP↔NP (Exp 1b) and Adv↔Adj (Exp 1a, 2) are the only permitted
    selection violations in coordination. -/
theorem experiments_confirm_two_violations :
    permittedViolations.length = 2 ∧
    -- Exp 1b confirms CP↔NP violation is real (coordination rescues)
    exp1b_coord.meanZ > exp1b_simple.meanZ ∧
    -- Exp 1a confirms Adv↔Adj violation is real (above ungrammatical)
    exp1a_adv.meanZ > exp1a_ungram.meanZ :=
  ⟨rfl, by native_decide, by native_decide⟩

/-- The coordination rescue effect in Exp 1b is exactly the CP↔NP
    violation type: a CP that cannot appear alone in a DP-selecting
    position becomes acceptable when coordinated with a DP.
    Grounded in `coordExtension`: NP ∈ coordExtension CP. -/
theorem exp1b_tests_cpAsNp :
    permittedViolations.contains .cpAsNp = true ∧
    SelectionViolationType.cpAsNp.cats = (.CP, NP) := ⟨by native_decide, rfl⟩

/-- The prenominal adverb effect in Exp 1a is the Adv↔Adj violation
    type: a non-*ly* adverb in an adjective-selecting position.
    Grounded in `coordExtension`: AdjP ∈ coordExtension AdvP. -/
theorem exp1a_tests_advAsAdj :
    permittedViolations.contains .advAsAdj = true ∧
    SelectionViolationType.advAsAdj.cats = (AdvP, AdjP) := ⟨by native_decide, rfl⟩

end Bruening2025
