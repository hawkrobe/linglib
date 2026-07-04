import Linglib.Studies.Ross1967
import Linglib.Studies.Adger2025
import Linglib.Features.Givenness
import Linglib.Semantics.Focus.Comparability

/-!
# Cartner, Kogan, Webster, Wagers & Sichel (2026)
[cartner-et-al-2026]

Subject islands do not reduce to construction-specific discourse function.
*Cognition* 271, 106467.

## Core Result

Three acceptability judgment experiments test whether subject islands arise
from an information-structural clash (the Focus Background Constraint of
[abeille-et-al-2020]) or from an abstract syntactic constraint on
movement. Using a super-additive factorial design ([sprouse-2007],
[sprouse-et-al-2012]), the paper isolates subject island effects across
wh-questions, relative clauses, and topicalization — three constructions
that share the filler-gap mechanism but differ in the IS profile of the
filler.

**Finding**: Subject island effects are present in all three constructions,
with remarkably invariant magnitude. This falsifies the FBC (and its
revised formulation in [winckel-et-al-2025]), which predict island
effects only for wh-questions. The paper explicitly notes (§8) that the
results do NOT falsify direct backgroundedness approaches
([cuneo-goldberg-2023]), only the constructional IS profile account.

## Formalization

1. IS profiles per construction, with structural uniformity/variance theorems
2. Original FBC ([abeille-et-al-2020]) and revised FBC
   ([winckel-et-al-2025]) as predicates over IS profiles
3. Both FBCs' predictions derived, then falsified by experimental DD scores
4. Explicit distinction from direct backgroundedness (BCI), which is NOT
   falsified (connecting to `BackgroundedIslands.lean`)
5. Cross-constructional invariance of the island effect
6. Bridge: subject islands have syntactic source
7. End-to-end argument chain
-/

/-- The three canonical filler-gap dependency constructions in English.
Each shares the abstract mechanism of movement (a filler displaced from a gap)
but differs in information-structural profile ([abeille-et-al-2020]).

The distinction matters for testing whether island effects are
construction-specific (as [abeille-et-al-2020] claim) or
construction-general (as [cartner-et-al-2026] argue). -/
inductive FGDConstruction where
  | whQuestion
  | relativeClause
  | topicalization
  deriving DecidableEq, Repr

/-- Extraction position within the embedded clause.
The subject/object asymmetry is the core empirical target of subject island
research ([ross-1967], [chomsky-1973]). -/
inductive ExtractionPosition where
  | subject
  | object
  deriving DecidableEq, Repr

open Features (BinaryGivenness)
open Features.InformationStructure (FocusMark)
open Semantics.Focus.Comparability

namespace CartnerEtAl2026

-- ============================================================================
-- §1. Information-Structural Profiles of Filler-Gap Constructions
-- ============================================================================

/-! Each filler-gap construction assigns distinct IS roles to its filler
(the displaced element) and its extraction domain. These profiles determine
whether the FBC predicts an IS clash.

The Krifka decomposition forces these into TWO axes: filler focus
marking (a focus-axis fact) and domain givenness (a givenness-axis
fact). WHQ fillers are focused (at-issue, introducing new
information); RC and TOP fillers are not (RC heads are presupposed,
topics are discourse-old). All three subjects are given/backgrounded.
Pre-Krifka versions of this file collapsed both into one
`DiscourseStatus → DiscourseStatus` map and had to filter the
`.focused` case for the domain. -/

/-- Focus marking of the filler in each construction.
[abeille-et-al-2020], §2; [winckel-et-al-2025]. -/
def fillerFocus : FGDConstruction → FocusMark
  | .whQuestion     => .focused      -- wh-phrase is focused (at-issue)
  | .relativeClause => .nonFocused   -- RC head is given/presupposed
  | .topicalization => .nonFocused   -- topic is discourse-old

/-- Givenness of the extraction domain (subject position).
Subjects are typically given/backgrounded across all three
constructions. -/
def subjectGivenness : FGDConstruction → BinaryGivenness
  | .whQuestion     => .given
  | .relativeClause => .given
  | .topicalization => .given

/-- **Subjects have uniform givenness across all constructions.**
This uniformity is what makes the cross-constructional comparison
informative: the extraction domain is held constant while the filler's
focus marking varies. -/
theorem subjectGivenness_uniform :
    subjectGivenness .whQuestion = subjectGivenness .relativeClause ∧
    subjectGivenness .relativeClause = subjectGivenness .topicalization :=
  ⟨rfl, rfl⟩

/-- **Fillers differ in focus marking across constructions.**
WHQ fillers are focused; RC and TOP fillers are not. This is the
variable that the FBC claims should modulate island effects. -/
theorem fillerFocus_varies :
    fillerFocus .whQuestion ≠ fillerFocus .relativeClause ∧
    fillerFocus .whQuestion ≠ fillerFocus .topicalization := by
  constructor <;> simp [fillerFocus]

-- ============================================================================
-- §2. The Focus Background Constraint ([abeille-et-al-2020])
-- ============================================================================

/-- The FBC (constraint (8) of [abeille-et-al-2020]):

    "A focused element should not be part of a backgrounded constituent."

A violation occurs when a focused filler is extracted from a backgrounded
domain. This is exactly `extractionISClash` from `Semantics/Focus/Comparability.lean`,
which unifies this constraint with [erteschik-shir-1973]'s Dominance
Condition on Extraction. -/
def fbcPredictsIsland (c : FGDConstruction) : Prop :=
  extractionISClash (fillerFocus c) (subjectGivenness c)

instance (c : FGDConstruction) : Decidable (fbcPredictsIsland c) :=
  inferInstanceAs (Decidable (extractionISClash _ _))

-- ============================================================================
-- §2b. Revised FBC ([winckel-et-al-2025])
-- ============================================================================

/-- Focus marking of the subject (governor) in each construction.
Across all three constructions in [cartner-et-al-2026]'s
materials, subjects are non-focused — the experimental design holds
the governor's focus marking constant while varying the filler's. -/
def subjectFocus : FGDConstruction → FocusMark
  | .whQuestion     => .nonFocused
  | .relativeClause => .nonFocused
  | .topicalization => .nonFocused

/-- The revised FBC (formulation (11) of [winckel-et-al-2025]):

    "An extracted element should not be more focused than its (non-local)
    governor."

[winckel-et-al-2025] state this as gradient (greater focus
difference → more degraded dependency), but in [cartner-et-al-2026]'s
materials both filler and governor are coded as binary focus marks
(`FocusMark`), so the gradient version reduces to: filler is focused
AND governor is not. Modelling the gradient case requires a richer
focus-prominence type than the binary `FocusMark`; deferred. -/
def fbcRevisedViolation (filler governor : FocusMark) : Prop :=
  filler = .focused ∧ governor = .nonFocused

instance (a b : FocusMark) : Decidable (fbcRevisedViolation a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Revised FBC predicts a subject island effect for a given construction
iff the filler is more focused than the subject governor. -/
def fbcRevisedPredictsIsland (c : FGDConstruction) : Prop :=
  fbcRevisedViolation (fillerFocus c) (subjectFocus c)

instance (c : FGDConstruction) : Decidable (fbcRevisedPredictsIsland c) :=
  inferInstanceAs (Decidable (fbcRevisedViolation _ _))

-- ============================================================================
-- §3. FBC Predictions (Both Versions)
-- ============================================================================

/-- The FBC predicts a subject island effect for wh-questions:
the wh-phrase is focused, the subject is backgrounded → clash. -/
theorem fbc_predicts_whq_island :
    fbcPredictsIsland .whQuestion := by decide

/-- The FBC predicts NO subject island effect for relative clauses. -/
theorem fbc_predicts_no_rc_island :
    ¬ fbcPredictsIsland .relativeClause := by decide

/-- The FBC predicts NO subject island effect for topicalization. -/
theorem fbc_predicts_no_top_island :
    ¬ fbcPredictsIsland .topicalization := by decide

/-- The revised FBC makes the same predictions as the original. -/
theorem both_fbcs_same_predictions :
    (fbcPredictsIsland .whQuestion ↔ fbcRevisedPredictsIsland .whQuestion) ∧
    (fbcPredictsIsland .relativeClause ↔ fbcRevisedPredictsIsland .relativeClause) ∧
    (fbcPredictsIsland .topicalization ↔ fbcRevisedPredictsIsland .topicalization) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Both FBCs predict construction-dependent island effects:
only WHQs should show subject islands. -/
theorem fbc_predicts_construction_dependence :
    fbcPredictsIsland .whQuestion ∧
    ¬ fbcPredictsIsland .relativeClause ∧
    ¬ fbcPredictsIsland .topicalization := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- §4. Super-Additive Experimental Design ([sprouse-2007], [sprouse-et-al-2012])
-- ============================================================================

/-- A super-additive DD (Differences-in-Differences) score.
Isolates the island effect by factoring out independent costs of DP
complexity and extraction. DD > 0 indicates a super-additive penalty —
the hallmark of an island effect.

Scores are z-scored by participant, rounded to ×100 integer encoding. -/
structure DDScore where
  construction : FGDConstruction
  position : ExtractionPosition
  /-- DD score × 100 (z-scored). Positive = super-additive penalty. -/
  dd : Int
  citation : String
  deriving Repr

-- ============================================================================
-- §5. Experimental Results
-- ============================================================================

/-- Experiment 1: Wh-questions (Fig. 1, n = 72).
Three-way interaction β = −0.94, 95%CrI = (−1.54, −0.32), Pr(β < 0) = 0.99. -/
def whqSubjectDD : DDScore :=
  { construction := .whQuestion, position := .subject,
    dd := 80, citation := "Cartner et al. 2026, Exp 1, Fig. 1" }

def whqObjectDD : DDScore :=
  { construction := .whQuestion, position := .object,
    dd := 33, citation := "Cartner et al. 2026, Exp 1, Fig. 1" }

/-- Experiment 2: Relative clauses (Fig. 2, n = 72).
Three-way interaction β = −0.58, 95%CrI = (−1.17, 0), Pr(β < 0) = 0.98. -/
def rcSubjectDD : DDScore :=
  { construction := .relativeClause, position := .subject,
    dd := 50, citation := "Cartner et al. 2026, Exp 2, Fig. 2" }

def rcObjectDD : DDScore :=
  { construction := .relativeClause, position := .object,
    dd := 16, citation := "Cartner et al. 2026, Exp 2, Fig. 2" }

/-- Experiment 3: Topicalization (Fig. 3, n = 72).
Three-way interaction β = −1.24, 95%CrI = (−1.90, −0.59), Pr(β < 0) = 0.99. -/
def topSubjectDD : DDScore :=
  { construction := .topicalization, position := .subject,
    dd := 29, citation := "Cartner et al. 2026, Exp 3, Fig. 3" }

def topObjectDD : DDScore :=
  { construction := .topicalization, position := .object,
    dd := -19, citation := "Cartner et al. 2026, Exp 3, Fig. 3" }

-- ============================================================================
-- §6. Key Empirical Theorems
-- ============================================================================

/-- Subject sub-extraction cost exceeds object sub-extraction cost
in ALL three constructions — not just wh-questions. -/
theorem subject_gt_object_whq : whqSubjectDD.dd > whqObjectDD.dd := by native_decide
theorem subject_gt_object_rc  : rcSubjectDD.dd > rcObjectDD.dd := by native_decide
theorem subject_gt_object_top : topSubjectDD.dd > topObjectDD.dd := by native_decide

/-- The subject island effect (Subject DD − Object DD) per construction. -/
def islandEffect (c : FGDConstruction) : Int :=
  match c with
  | .whQuestion     => whqSubjectDD.dd - whqObjectDD.dd
  | .relativeClause => rcSubjectDD.dd - rcObjectDD.dd
  | .topicalization => topSubjectDD.dd - topObjectDD.dd

/-- The island effect is positive for all three constructions. -/
theorem island_effect_positive_whq : islandEffect .whQuestion > 0 := by native_decide
theorem island_effect_positive_rc  : islandEffect .relativeClause > 0 := by native_decide
theorem island_effect_positive_top : islandEffect .topicalization > 0 := by native_decide

/-- **Cross-constructional invariance**: The island effect magnitudes are
of similar order across all three constructions (34–48 on the ×100 z-score
scale), despite the constructions having distinct IS profiles.
Each effect is within 3/2 of every other. -/
theorem island_effect_invariance :
    let whq := islandEffect .whQuestion
    let rc := islandEffect .relativeClause
    let top := islandEffect .topicalization
    -- All positive
    whq > 0 ∧ rc > 0 ∧ top > 0 ∧
    -- All pairwise within 3/2 (i.e. 2a ≤ 3b)
    2 * whq ≤ 3 * rc ∧ 2 * rc ≤ 3 * whq ∧
    2 * whq ≤ 3 * top ∧ 2 * top ≤ 3 * whq ∧
    2 * rc ≤ 3 * top ∧ 2 * top ≤ 3 * rc := by native_decide

-- ============================================================================
-- §7. Falsification of the FBC
-- ============================================================================

/-- **The FBC is falsified for RCs**: It predicts no island effect for
relative clauses, but the data shows a robust subject island effect. -/
theorem fbc_falsified_for_rc :
    ¬ fbcPredictsIsland .relativeClause ∧
    islandEffect .relativeClause > 0 := ⟨by decide, by native_decide⟩

/-- **The FBC is falsified for TOPs**: It predicts no island effect for
topicalization, but the data shows a robust subject island effect. -/
theorem fbc_falsified_for_top :
    ¬ fbcPredictsIsland .topicalization ∧
    islandEffect .topicalization > 0 := ⟨by decide, by native_decide⟩

/-- The revised FBC ([winckel-et-al-2025]) is equally falsified. -/
theorem fbc_revised_falsified_for_rc :
    ¬ fbcRevisedPredictsIsland .relativeClause ∧
    islandEffect .relativeClause > 0 := ⟨by decide, by native_decide⟩

theorem fbc_revised_falsified_for_top :
    ¬ fbcRevisedPredictsIsland .topicalization ∧
    islandEffect .topicalization > 0 := ⟨by decide, by native_decide⟩

-- ============================================================================
-- §8. Limits of Falsification: BCI Is NOT Falsified
-- ============================================================================

/-! The paper explicitly notes (§8, p.12):

    "We note that our results only speak to the FBC, and do not contradict
    direct backgroundedness approaches (Cuneo & Goldberg, 2023)."

The **constructional IS profile** account (FBC) attributes islands to the
interaction of the construction's IS profile with the filler's IS status.
The **direct backgroundedness** account (BCI, [cuneo-goldberg-2023])
attributes islands to the degree of backgroundedness of the extraction
domain itself, independent of the filler's IS profile.

Since subjects were systematically more backgrounded than objects across
all three constructions tested, direct backgroundedness could in principle
capture the results. The paper did not manipulate backgroundedness
directly, so the BCI remains unfalsified.

This matters for linglib integration: `BackgroundedIslands.lean` formalizes
the direct backgroundedness account (for MoS verbs, via QUD-determined
backgroundedness). That formalization is NOT undermined by Cartner et al.'s
findings — they target a different theory. -/

/-- Discourse-based island theories distinguished by what drives the
prediction: the construction's IS profile (FBC) or the extraction domain's
backgroundedness (BCI). -/
inductive DiscourseIslandTheory where
  /-- Island status depends on IS profile of the *construction* (filler
  status interacts with domain status). [abeille-et-al-2020]. -/
  | constructionalISProfile
  /-- Island status depends on the *degree of backgroundedness* of the
  extraction domain, independent of construction type.
  [cuneo-goldberg-2023]. -/
  | directBackgroundedness
  deriving DecidableEq, Repr

/-- Cartner et al.'s experiments test the constructional IS profile account
(by varying construction type while holding domain backgroundedness
constant), NOT the direct backgroundedness account. -/
def cartnerTestsTheory : DiscourseIslandTheory → Bool
  | .constructionalISProfile => true
  | .directBackgroundedness  => false

/-- The direct backgroundedness account (BCI) is untouched by these results.
This connects to the existing formalization in
`Semantics/Focus/BackgroundedIslands.lean`, which models
QUD-determined backgroundedness for MoS islands — a different phenomenon
that these experiments do not address. -/
theorem bci_not_falsified :
    cartnerTestsTheory .directBackgroundedness = false := rfl

-- ============================================================================
-- §9. Bridge: Syntactic Source Confirmed
-- ============================================================================

/-- An island source predicts construction-invariance iff it attributes the
island to a mechanism shared across all filler-gap constructions.

The syntactic account (Subject Condition) attributes subject islands to the
abstract movement operation, shared by WHQs, RCs, and TOPs → predicts
invariance. The discourse account (FBC) attributes subject islands to an
IS clash, which varies by construction → predicts variance. -/
def predictsInvariance : IslandSource → Bool
  | .syntactic  => true   -- same movement constraint across constructions
  | .semantic   => true   -- same binding restriction across constructions
  | .processing => true   -- same processing bottleneck across constructions
  | .discourse  => false  -- different IS profiles → different predictions

/-- Subject islands are syntactically sourced: they arise from a structural
constraint on movement (Subject Condition / Phase + anti-locality) that is
shared across all filler-gap constructions.

Derived from the construction-invariance data (§§6–7): all three FGD types
show statistically indistinguishable subject island costs. This matches
the syntactic prediction (same constraint → same cost) and falsifies the
discourse/FBC prediction (different IS profiles → different costs). -/
def subjectIslandSource : IslandSource := .syntactic

theorem syntactic_predicts_invariance :
    [subjectIslandSource].all predictsInvariance = true := rfl

/-- The discourse source would predict construction-dependent effects —
inconsistent with the data. -/
theorem discourse_predicts_variance :
    predictsInvariance .discourse = false := rfl

-- ============================================================================
-- §10. Cross-Constructional Sub-Extraction Costs (Section 7)
-- ============================================================================

/-- Sub-extraction cost relative to full extraction, from the cross-
constructional posterior analysis (Section 7, Fig. 5). Values × 100.

These are (sub-extraction cost) − (full extraction cost) for subjects,
estimated from ordinal mixed-effects regression posteriors with 95% HPDIs. -/
structure SubExtractionCost where
  construction : FGDConstruction
  /-- Point estimate × 100 -/
  cost : Nat
  /-- 95% HPDI lower bound × 100 -/
  hpdiLo : Nat
  /-- 95% HPDI upper bound × 100 -/
  hpdiHi : Nat
  citation : String
  deriving Repr

def whqSubjectSubExCost : SubExtractionCost :=
  { construction := .whQuestion, cost := 132, hpdiLo := 102, hpdiHi := 161,
    citation := "Cartner et al. 2026, §7" }

def rcSubjectSubExCost : SubExtractionCost :=
  { construction := .relativeClause, cost := 134, hpdiLo := 104, hpdiHi := 164,
    citation := "Cartner et al. 2026, §7" }

def topSubjectSubExCost : SubExtractionCost :=
  { construction := .topicalization, cost := 115, hpdiLo := 85, hpdiHi := 145,
    citation := "Cartner et al. 2026, §7" }

/-- All three 95% HPDIs exclude zero — each construction shows a reliable
additional sub-extraction cost for subjects. -/
theorem all_hpdis_exclude_zero :
    whqSubjectSubExCost.hpdiLo > 0 ∧
    rcSubjectSubExCost.hpdiLo > 0 ∧
    topSubjectSubExCost.hpdiLo > 0 :=
  ⟨by native_decide, by native_decide, by native_decide⟩

/-- The 95% HPDIs largely overlap across constructions, consistent with
a single underlying constraint of stable magnitude. -/
theorem hpdis_overlap :
    -- WHQ and RC intervals overlap
    whqSubjectSubExCost.hpdiLo < rcSubjectSubExCost.hpdiHi ∧
    rcSubjectSubExCost.hpdiLo < whqSubjectSubExCost.hpdiHi ∧
    -- WHQ and TOP intervals overlap
    whqSubjectSubExCost.hpdiLo < topSubjectSubExCost.hpdiHi ∧
    topSubjectSubExCost.hpdiLo < whqSubjectSubExCost.hpdiHi ∧
    -- RC and TOP intervals overlap
    rcSubjectSubExCost.hpdiLo < topSubjectSubExCost.hpdiHi ∧
    topSubjectSubExCost.hpdiLo < rcSubjectSubExCost.hpdiHi :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- §11. End-to-End Argument Chain
-- ============================================================================

/-- **The paper's complete argument in one theorem.**

Premises:
- Subjects have uniform IS across constructions (the controlled variable)
- Fillers differ in IS across constructions (the manipulated variable)
- Both FBC formulations predict only WHQs show subject islands
- All three constructions show subject island effects (the data)

Conclusions:
- The FBC is falsified (it predicts construction-dependence; data shows
  construction-invariance)
- The syntactic account is corroborated (it predicts invariance)
- The direct backgroundedness account (BCI) is not tested -/
theorem argument_chain :
    -- Structural premise: subjects uniform, fillers vary
    subjectGivenness .whQuestion = subjectGivenness .relativeClause ∧
    subjectGivenness .relativeClause = subjectGivenness .topicalization ∧
    fillerFocus .whQuestion ≠ fillerFocus .relativeClause ∧
    -- FBC predictions (original and revised agree)
    fbcPredictsIsland .whQuestion ∧
    ¬ fbcPredictsIsland .relativeClause ∧
    ¬ fbcPredictsIsland .topicalization ∧
    (fbcPredictsIsland .whQuestion ↔ fbcRevisedPredictsIsland .whQuestion) ∧
    (fbcPredictsIsland .relativeClause ↔ fbcRevisedPredictsIsland .relativeClause) ∧
    (fbcPredictsIsland .topicalization ↔ fbcRevisedPredictsIsland .topicalization) ∧
    -- Data: all three show island effect
    islandEffect .whQuestion > 0 ∧
    islandEffect .relativeClause > 0 ∧
    islandEffect .topicalization > 0 ∧
    -- Conclusion: syntactic account predicts this, discourse account doesn't
    subjectIslandSource = .syntactic ∧
    [subjectIslandSource].all predictsInvariance = true ∧
    predictsInvariance .discourse = false ∧
    -- Scope: BCI not tested
    cartnerTestsTheory .directBackgroundedness = false := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp [fillerFocus]
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · native_decide
  · native_decide
  · native_decide

-- ============================================================================
-- §X. Cross-framework convergence with [adger-2025]
-- ============================================================================

/-! Cartner et al.'s super-additive design (cross-constructional invariance
of subject-island costs) and Adger's Angular Locality (graph-theoretic
cross-dimensional path failure) reach the same `IslandSource.syntactic`
verdict for subject islands from incompatible foundations:

- **Cartner et al.**: `subjectIslandSource = .syntactic` because the
  invariance pattern is what an abstract syntactic constraint on movement
  would predict (and what a constructional-IS account would falsify).
- **Adger AL**: `Adger2025.adgerSubjectIslandSource = .syntactic` because
  sub-extraction from within `g_subject_island` traverses a cross-
  dimensional path (`SynGraph.subject_island_blocks`).

Convergence by `rfl` — both files independently classify subject-island
sources as syntactic; the agreement is type-level. The mechanisms remain
incompatible (graph-theoretic parthood across dimensions vs construction-
invariance over filler-gap dependencies); the convergent verdict is what
makes the agreement informative. -/

/-- **Convergence with [adger-2025]**: both Cartner et al. (cross-
    constructional invariance) and Adger AL (cross-dimensional path
    failure) classify subject-island sources as syntactic. -/
theorem subject_island_source_converges_with_adger :
    subjectIslandSource = Adger2025.adgerSubjectIslandSource := rfl

end CartnerEtAl2026
