import Linglib.Phenomena.Islands.Studies.Ross1967
import Linglib.Theories.Processing.Cost.Profile

/-!
# Cognitive Constraints and Island Effects
@cite{hofmeister-sag-2010}

@cite{hofmeister-sag-2010} argue that island effects are gradient along
multiple dimensions and that acceptability varies systematically with
nonstructural manipulations (filler complexity, referential load) that
leave island configurations intact. This challenges every categorical
island constraint proposed: Subjacency, Complex NP Constraint, Barriers,
and the Minimal Link Condition.

## Key findings

1. More complex fillers (*which*-N phrases) improve acceptability inside
   islands relative to bare wh-words (*who*, *what*) — counterintuitively,
   richer representations resist interference and aid memory retrieval.
2. Indefinite/plural island NPs improve acceptability relative to definite
   NPs, consistent with lower referential processing cost.
3. Even the best island condition remains below non-island baselines:
   islands are ameliorated, not eliminated.

The cross-theory comparison (competence vs. performance vs. discourse) lives in
`Phenomena.FillerGap.Studies.LuPanDegen2025`, which integrates these findings
with @cite{lu-pan-degen-2025}'s discourse-based account.
-/

namespace Phenomena.Islands.Studies.HofmeisterSag2010

open ProcessingModel

-- ============================================================================
-- §1. Processing factors
-- ============================================================================

/-- Processing factors that independently contribute to the difficulty of
filler-gap dependencies inside islands. -/
inductive ProcessingFactor where
  /-- Distance between filler and gap increases memory load (section 3.1).
  Confirmed by processing studies. -/
  | locality
  /-- Referential processing of intervening constituents depletes resources (section 3.2).
  Definites trigger referent search; proper names > definites > indefinites > pronouns
  in processing cost. -/
  | referentialLoad
  /-- Clause boundaries impose processing cost independent of extraction (section 3.3).
  Even in yes-no questions, different complementizers elicit different neurological
  responses and acceptability. -/
  | clauseBoundary
  /-- Syntactic/semantic complexity of the filler phrase affects retrieval (section 3.4).
  Counterintuitively, MORE complex fillers REDUCE processing difficulty
  because richer representations resist interference and aid retrieval. -/
  | fillerComplexity
  deriving Repr, DecidableEq

-- ============================================================================
-- §2. Experimental condition types
-- ============================================================================

/-- Complexity of the displaced wh-phrase.
More complex fillers (*which*-N phrases) facilitate processing inside islands,
because richer representations aid memory retrieval (section 3.4). -/
inductive FillerType where
  /-- Bare wh-word: *who*, *what* -/
  | bare
  /-- Complex wh-phrase: *which convict*, *which employee* -/
  | whichN
  deriving Repr, DecidableEq

/-- Type of the island-forming NP (Experiment 1 only).
Definite NPs trigger referent search and presupposition accommodation,
consuming resources needed for dependency resolution (section 3.2). -/
inductive IslandNPType where
  /-- Definite singular: *the report* -/
  | definite
  /-- Indefinite plural: *reports* -/
  | plural
  /-- Indefinite singular: *a report* -/
  | indefinite
  deriving Repr, DecidableEq

/-- An experimental condition from @cite{hofmeister-sag-2010}.
Acceptability stored as Nat (judgment ratio x 100, so 78 means 0.78). -/
structure IslandCondition where
  island : ConstraintType
  filler : FillerType
  npType : Option IslandNPType
  /-- Mean judgment ratio x 100 -/
  acceptability : Nat
  citation : String
  deriving Repr

-- ============================================================================
-- §3. Experimental data
-- ============================================================================

/-- Experiment 1: CNPC violations (section 5). 36 items, (2 x 3) + 1 design.
Acceptability ratings on 1-8 scale, normalized as ratio of subject mean.
Data from Figure 3 (p. 393). -/
def cnpcAcceptability : List IslandCondition := [
  { island := .complexNP, filler := .bare, npType := some .definite,
    acceptability := 60, citation := "H&S 2010, Exp 1, Fig. 3" },
  { island := .complexNP, filler := .bare, npType := some .indefinite,
    acceptability := 65, citation := "H&S 2010, Exp 1, Fig. 3" },
  { island := .complexNP, filler := .bare, npType := some .plural,
    acceptability := 62, citation := "H&S 2010, Exp 1, Fig. 3" },
  { island := .complexNP, filler := .whichN, npType := some .definite,
    acceptability := 78, citation := "H&S 2010, Exp 1, Fig. 3" },
  { island := .complexNP, filler := .whichN, npType := some .indefinite,
    acceptability := 82, citation := "H&S 2010, Exp 1, Fig. 3" },
  { island := .complexNP, filler := .whichN, npType := some .plural,
    acceptability := 85, citation := "H&S 2010, Exp 1, Fig. 3" }
]

/-- Experiment 2: Wh-island violations (section 6). 24 items, 2 + 1 design.
Acceptability on 1-7 scale, normalized.
Data from Figure 5 (p. 397).
Key finding: F1(1,15)=15.964, p=0.001; F2(1,19)=14.428, p=0.001. -/
def whIslandAcceptability : List IslandCondition := [
  { island := .embeddedQuestion, filler := .bare, npType := none,
    acceptability := 57, citation := "H&S 2010, Exp 2, Fig. 5" },
  { island := .embeddedQuestion, filler := .whichN, npType := none,
    acceptability := 76, citation := "H&S 2010, Exp 2, Fig. 5" }
]

/-- Non-island baseline acceptability (CNPC experiment, Figure 3). -/
def cnpcBaseline : Nat := 108

-- ============================================================================
-- §4. Key empirical generalizations
-- ============================================================================

/-- Average acceptability for a filler type across a set of conditions. -/
def avgAcceptability (conditions : List IslandCondition) (f : FillerType) : Nat :=
  let filtered := conditions.filter (·.filler == f)
  if filtered.isEmpty then 0
  else filtered.foldl (· + ·.acceptability) 0 / filtered.length

/-- **Filler complexity effect in CNPC**: which-N > bare wh (section 5.2).
F1(1,20)=48.741, p<0.0001; F2(1,35)=39.494, p<0.0001.
The structure is identical -- only the filler changes. -/
theorem cnpc_whichN_gt_bare :
    avgAcceptability cnpcAcceptability .whichN >
    avgAcceptability cnpcAcceptability .bare := by decide

/-- **Filler complexity effect in wh-islands**: which-N > bare wh (section 6.2).
F1(1,15)=15.964, p=0.001. -/
theorem whIsland_whichN_gt_bare :
    avgAcceptability whIslandAcceptability .whichN >
    avgAcceptability whIslandAcceptability .bare := by decide

/-- **NP type effect**: indefinite > definite across both filler types (section 5.2).
Consistent with lower referential processing cost for indefinites. -/
theorem cnpc_indefinite_gt_definite :
    let indef := cnpcAcceptability.filter (·.npType == some .indefinite)
    let def_ := cnpcAcceptability.filter (·.npType == some .definite)
    indef.foldl (· + ·.acceptability) 0 >
    def_.foldl (· + ·.acceptability) 0 := by decide

/-- Even the best island condition (which-PL, 85) remains below the
non-island baseline (108). Islands are ameliorated, not eliminated. -/
theorem best_island_lt_baseline :
    (85 : Nat) < cnpcBaseline := by decide

-- ============================================================================
-- §5. Pareto-comparable processing profiles
-- ============================================================================

/-! Pareto profiles re-encode H&S's key conditions in the format used by
`Theories.Processing.Cost.Profile`, supporting weight-free ordinal
comparison via Pareto dominance. -/

/-- Bare wh + definite island-forming NP: worst CNPC condition.
"I saw **who** Emma doubted **the report** that we had captured ___" -/
def cnpcBareDefProfile : ProcessingProfile :=
  { locality := 8, boundaries := 1, referentialLoad := 2, ease := 0 }

/-- Which-N + indefinite island-forming NP: best CNPC condition.
"I saw **which convict** Emma doubted **a report** that we had captured ___" -/
def cnpcWhichIndefProfile : ProcessingProfile :=
  { locality := 8, boundaries := 1, referentialLoad := 1, ease := 2 }

/-- Non-island baseline (no extraction): "I saw who Emma doubted that ___" -/
def cnpcBaselineProfile : ProcessingProfile :=
  { locality := 5, boundaries := 0, referentialLoad := 0, ease := 0 }

/-- Bare wh into wh-island: "**Who** did Albert learn whether they dismissed ___" -/
def whIslandBareProfile : ProcessingProfile :=
  { locality := 7, boundaries := 1, referentialLoad := 1, ease := 0 }

/-- Which-N into wh-island: "**Which employee** did Albert learn whether they dismissed ___" -/
def whIslandWhichProfile : ProcessingProfile :=
  { locality := 7, boundaries := 1, referentialLoad := 1, ease := 2 }

/-- Conditions tagged for use with `OrderingPrediction`. -/
inductive ProcessingCondition where
  | cnpcBareDef
  | cnpcWhichIndef
  | cnpcBaseline
  | whIslandBare
  | whIslandWhich
  deriving Repr, DecidableEq

instance : HasProcessingProfile ProcessingCondition where
  profile
    | .cnpcBareDef    => cnpcBareDefProfile
    | .cnpcWhichIndef => cnpcWhichIndefProfile
    | .cnpcBaseline   => cnpcBaselineProfile
    | .whIslandBare   => whIslandBareProfile
    | .whIslandWhich  => whIslandWhichProfile

/-- Complex fillers reduce processing difficulty in CNPC.
Pareto: cnpcWhichIndefProfile is easier than cnpcBareDefProfile because
referentialLoad is lower (1 < 2) and ease is higher (2 > 0); locality and
boundaries are equal. -/
theorem filler_reduces_cnpc_cost :
    cnpcBareDefProfile.compare cnpcWhichIndefProfile = .harder := by decide

/-- Complex fillers reduce processing difficulty in wh-islands.
Pareto: whIslandWhichProfile is easier than whIslandBareProfile because
ease is higher (2 > 0) with all other dimensions equal. -/
theorem filler_reduces_whIsland_cost :
    whIslandBareProfile.compare whIslandWhichProfile = .harder := by decide

/-- Worst CNPC condition is harder than baseline.
Pareto: cnpcBareDefProfile dominates on locality (8 > 5), boundaries (1 > 0),
and referentialLoad (2 > 0); ease is equal. -/
theorem bare_def_harder_than_baseline :
    cnpcBareDefProfile.compare cnpcBaselineProfile = .harder := by decide

/-- Worst CNPC condition (bare-def) is strictly harder than best (which-indef). -/
theorem bare_def_harder_than_which_indef :
    cnpcBareDefProfile.compare cnpcWhichIndefProfile = .harder := by decide

/-- Which-indef CNPC vs baseline is incomparable under Pareto: which-indef is
worse on locality (8 > 5), boundaries (1 > 0), and referentialLoad (1 > 0)
but better on ease (2 > 0). The trade-off is genuine — Pareto reports it as
`incomparable` rather than forcing a cardinal aggregate. -/
theorem which_indef_vs_baseline_incomparable :
    cnpcWhichIndefProfile.compare cnpcBaselineProfile = .incomparable := by decide

/-- Pareto-orderable predictions over the H&S conditions.
Which-indef CNPC vs baseline is omitted because it is incomparable under
Pareto (see `which_indef_vs_baseline_incomparable`). -/
def islandOrderingPredictions : List (OrderingPrediction ProcessingCondition) := [
  { harder := .cnpcBareDef, easier := .cnpcWhichIndef,
    description := "Bare-def CNPC harder than which-indef CNPC" },
  { harder := .cnpcBareDef, easier := .cnpcBaseline,
    description := "Bare-def CNPC harder than baseline" },
  { harder := .whIslandBare, easier := .whIslandWhich,
    description := "Bare wh-island harder than which-N wh-island" }
]

/-- Every Pareto-orderable prediction is verified by the data. -/
theorem all_ordering_predictions_verified :
    islandOrderingPredictions.all verifyOrdering = true := by decide

end Phenomena.Islands.Studies.HofmeisterSag2010
