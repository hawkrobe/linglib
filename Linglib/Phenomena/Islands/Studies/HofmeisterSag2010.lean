import Linglib.Phenomena.Islands.Studies.Ross1967

set_option autoImplicit false

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

See `Phenomena.FillerGap.Compare` for the competence vs. performance comparison.
-/

namespace Phenomena.Islands.Studies.HofmeisterSag2010

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
    avgAcceptability cnpcAcceptability .bare := by native_decide

/-- **Filler complexity effect in wh-islands**: which-N > bare wh (section 6.2).
F1(1,15)=15.964, p=0.001. -/
theorem whIsland_whichN_gt_bare :
    avgAcceptability whIslandAcceptability .whichN >
    avgAcceptability whIslandAcceptability .bare := by native_decide

/-- **NP type effect**: indefinite > definite across both filler types (section 5.2).
Consistent with lower referential processing cost for indefinites. -/
theorem cnpc_indefinite_gt_definite :
    let indef := cnpcAcceptability.filter (·.npType == some .indefinite)
    let def_ := cnpcAcceptability.filter (·.npType == some .definite)
    indef.foldl (· + ·.acceptability) 0 >
    def_.foldl (· + ·.acceptability) 0 := by native_decide

/-- Even the best island condition (which-PL, 85) remains below the
non-island baseline (108). Islands are ameliorated, not eliminated. -/
theorem best_island_lt_baseline :
    (85 : Nat) < cnpcBaseline := by native_decide

end Phenomena.Islands.Studies.HofmeisterSag2010
