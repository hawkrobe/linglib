import Linglib.Core.Polarity
import Linglib.Phenomena.Plurals.Homogeneity
import Linglib.Phenomena.Plurals.Studies.Magri2014

/-!
# Tieu, Križ & Chemla (2019): Children's Acquisition of Homogeneity
@cite{tieu-kriz-chemla-2019}

Children's acquisition of homogeneity in plural definite descriptions.
*Frontiers in Psychology* 10, 2329.

## Core Contribution

Two experiments testing French-speaking children (ages 4--6) on their
interpretations of plural definite descriptions in GAP contexts (where
some but not all individuals satisfy the predicate), alongside scalar
implicature controls. The experiments test predictions of the scalar
implicature account of homogeneity (@cite{magri-2014}).

## Three Interpretive Patterns

Children presented with "The trucks are blue" / "The trucks aren't blue"
in a GAP context (2 of 4 trucks blue) could respond in three ways:

1. **Homogeneous** (adult-like): reject both positive and negative
2. **Existential**: accept positive ("some are blue"), reject negative
3. **Universal**: reject positive, accept negative ("not all are blue")

## Key Finding

Three groups of children emerge:

- **EXI/−SI**: Existential interpretation, no scalar implicatures (the
  literal existential meaning predicted by @cite{magri-2014})
- **HOM/+SI**: Homogeneous with implicatures (adult-like, consistent
  with @cite{magri-2014})
- **HOM/−SI**: Homogeneous WITHOUT scalar implicatures (problematic
  for @cite{magri-2014})

The existence of the HOM/−SI group contradicts @cite{magri-2014}'s
prediction that homogeneity requires the *not-all* scalar implicature
as a subcomputation. The data suggest that homogeneity and scalar
implicatures are independent, with homogeneity acquired earlier.

## Connection to Linglib

- Imports `Homogeneity.lean` for the empirical gap pattern
- Imports `Magri2014.lean` to test the double-strengthening prediction
  (end-to-end: inner EXH → double-EXH → ALL → falsified by HOM/−SI data)
-/

namespace Phenomena.Plurals.Studies.TieuKrizChemla2019

open Core (Polarity)
open Phenomena.Plurals.Homogeneity (HomogeneityJudgment HomogeneityDatum
  switchesExample)


-- ============================================================
-- SECTION 1: Interpretive Patterns
-- ============================================================

/--
The three possible interpretations a speaker can assign to a plural
definite description like "the trucks."
-/
inductive DefinitePluralReading where
  /-- THE ≈ SOME: existential interpretation -/
  | existential
  /-- THE shows a truth-value gap: homogeneous interpretation -/
  | homogeneous
  /-- THE ≈ ALL: universal interpretation -/
  | universal
  deriving Repr, DecidableEq, BEq, Inhabited

/--
What each interpretive pattern predicts for positive and negative
definite descriptions in a GAP context (some but not all satisfy).
-/
structure GapPrediction where
  reading : DefinitePluralReading
  /-- Accept "The Xs are P" when only some Xs are P? -/
  acceptPositiveGap : Bool
  /-- Accept "The Xs aren't P" when only some Xs are P? -/
  acceptNegativeGap : Bool
  deriving Repr, DecidableEq, BEq

/-- Existential: accept positive (some are P), reject negative. -/
def existentialGap : GapPrediction :=
  ⟨.existential, true, false⟩

/-- Homogeneous: reject both positive and negative (the gap). -/
def homogeneousGap : GapPrediction :=
  ⟨.homogeneous, false, false⟩

/-- Universal: reject positive (not all are P), accept negative. -/
def universalGap : GapPrediction :=
  ⟨.universal, false, true⟩

def allGapPredictions : List GapPrediction :=
  [existentialGap, homogeneousGap, universalGap]

/-- The three patterns are mutually exclusive: no two agree on both responses. -/
theorem patterns_distinct_responses :
    existentialGap.acceptPositiveGap ≠ homogeneousGap.acceptPositiveGap ∧
    homogeneousGap.acceptNegativeGap ≠ universalGap.acceptNegativeGap := by
  exact ⟨by decide, by decide⟩

/-- The homogeneous pattern matches the empirical gap data in Homogeneity.lean:
    both positive and negative are judged "neither true nor false." -/
theorem homogeneous_matches_gap_data :
    homogeneousGap.acceptPositiveGap = false ∧
    homogeneousGap.acceptNegativeGap = false ∧
    switchesExample.positiveInGap = .neitherTrueNorFalse ∧
    switchesExample.negativeInGap = .neitherTrueNorFalse := by
  exact ⟨rfl, rfl, rfl, rfl⟩


-- ============================================================
-- SECTION 2: Participant Groups (Reading × Implicature Status)
-- ============================================================

/--
A participant group defined by their definite plural interpretation
and whether they compute scalar implicatures.
-/
structure ParticipantGroup where
  /-- How they interpret the definite plural -/
  reading : DefinitePluralReading
  /-- Whether they compute the "not-all" scalar implicature -/
  computesImplicatures : Bool
  deriving Repr, DecidableEq, BEq

/-- The six logically possible groups. -/
def allGroups : List ParticipantGroup :=
  [ ⟨.existential, false⟩, ⟨.existential, true⟩
  , ⟨.homogeneous, false⟩, ⟨.homogeneous, true⟩
  , ⟨.universal, false⟩, ⟨.universal, true⟩ ]

/-- Shorthand for the key groups. -/
def exiMinusSI : ParticipantGroup := ⟨.existential, false⟩
def exiPlusSI  : ParticipantGroup := ⟨.existential, true⟩
def homMinusSI : ParticipantGroup := ⟨.homogeneous, false⟩
def homPlusSI  : ParticipantGroup := ⟨.homogeneous, true⟩
def uniMinusSI : ParticipantGroup := ⟨.universal, false⟩
def uniPlusSI  : ParticipantGroup := ⟨.universal, true⟩


-- ============================================================
-- SECTION 3: Magri's Acquisition Predictions
-- ============================================================

/--
The scalar implicature account of homogeneity (@cite{magri-2014})
makes specific predictions about the developmental trajectory.

Since homogeneity is derived via double exhaustification, and the
inner EXH computes the "not-all" scalar implicature, two predictions
follow:

1. **SI-prerequisite**: Children who cannot compute the "not-all"
   implicature cannot derive homogeneous readings. Therefore the
   HOM/−SI group should not exist.

2. **SI-not-rarer**: The "not-all" implicature is a subcomputation
   of the homogeneity implicature. So homogeneous readings should
   not be *more* frequent than scalar implicatures.
-/
structure ImplicatureAccountPrediction where
  /-- SI is a prerequisite for homogeneity -/
  siPrerequisite : Bool
  /-- Therefore HOM/−SI should not exist -/
  homWithoutSIPossible : Bool
  /-- SI should not be rarer than homogeneity -/
  siNotRarerThanHom : Bool
  deriving Repr, DecidableEq, BEq

def magriPrediction : ImplicatureAccountPrediction :=
  { siPrerequisite := true
  , homWithoutSIPossible := false
  , siNotRarerThanHom := true }


-- ============================================================
-- SECTION 4: Experiment 1 — Binary TVJT
-- ============================================================

/--
Experiment 1: Truth Value Judgment Task with binary (yes/no) responses.

Participants: 24 French-speaking children (ages 4;04–5;03, M = 4;09)
and 22 adults. Children tested at preschools in Paris.

Materials: 6 homogeneity targets (3 positive + 3 negative THE-sentences
in GAP contexts), 8 definite description controls, 6 universal
quantification controls, 4 scalar implicature targets.
-/
structure Exp1GroupCounts where
  /-- Group label -/
  group : String
  /-- Number of adults in this group -/
  adults : Nat
  /-- Number of children in this group -/
  children : Nat
  deriving Repr

/-- Experiment 1, Table 1: Distribution of participants by homogeneity
    pattern and implicature status.

    Categories defined by majority response (≥2/3 trials). -/
def exp1_table1 : List Exp1GroupCounts :=
  [ ⟨"HOM/−SI", 5, 6⟩
  , ⟨"HOM/+SI", 10, 10⟩
  , ⟨"EXI/−SI", 0, 7⟩
  , ⟨"EXI/+SI", 0, 1⟩
  , ⟨"UNI/−SI", 5, 0⟩
  , ⟨"UNI/+SI", 1, 0⟩ ]

/-- Experiment 1, Table 3: Bayesian model group assignments for children.

    The model confirmed the descriptive categorization: children were
    unambiguously assigned to groups with posterior probability > 0.92. -/
structure Exp1BayesianGroups where
  /-- HOM/−SI children -/
  homMinusSI : Nat
  /-- HOM/+SI children -/
  homPlusSI : Nat
  /-- EXI/−SI children -/
  exiMinusSI : Nat
  /-- EXI/+SI children -/
  exiPlusSI : Nat
  deriving Repr

def exp1Children : Exp1BayesianGroups :=
  { homMinusSI := 6
  , homPlusSI := 10
  , exiMinusSI := 7
  , exiPlusSI := 1 }

/-- Total children in Experiment 1. -/
theorem exp1_total_children :
    exp1Children.homMinusSI + exp1Children.homPlusSI +
    exp1Children.exiMinusSI + exp1Children.exiPlusSI = 24 := by
  native_decide


-- ============================================================
-- SECTION 5: Experiment 2 — Ternary Judgment
-- ============================================================

/--
Experiment 2: Ternary reward task (minimal / intermediate / maximal).

The ternary paradigm distinguishes truly homogeneous readings from
wide-scope universals: a homogeneous reading yields intermediate
rewards for both positive and negative GAP sentences, while a
wide-scope universal yields minimal for both.

Participants: 24 French-speaking children (ages 4;07–6;04, M = 5;03)
and 25 adults. Additional controls for incomplete description,
partial truth, and scope ambiguity effects.

Categorization criteria (ternary):
- EXISTENTIAL: maximal for ≥2/3 positive GAP, minimal for ≥2/3 negative GAP
- HOMOGENEOUS: ≤ intermediate for ≥2/3 positive AND ≥2/3 negative GAP
- UNIVERSAL: minimal for ≥2/3 positive GAP, maximal for ≥2/3 negative GAP
-/
structure Exp2GroupCounts where
  /-- Group label -/
  group : String
  /-- Number of adults -/
  adults : Nat
  /-- Number of children -/
  children : Nat
  deriving Repr

/-- Experiment 2, Table 6: Distribution of participants by homogeneity
    pattern and implicature status. -/
def exp2_table6 : List Exp2GroupCounts :=
  [ ⟨"HOM/−SI", 2, 5⟩
  , ⟨"HOM/+SI", 21, 7⟩
  , ⟨"EXI/−SI", 0, 10⟩
  , ⟨"EXI/+SI", 0, 0⟩
  , ⟨"UNI/−SI", 2, 0⟩
  , ⟨"UNI/+SI", 0, 0⟩ ]

/-- Experiment 2, Table 7: After conservative exclusions (eliminating
    participants with potential biases for incomplete description,
    partial truth, or scope ambiguity). -/
def exp2_table7 : List Exp2GroupCounts :=
  [ ⟨"HOM/−SI", 2, 2⟩
  , ⟨"HOM/+SI", 18, 2⟩
  , ⟨"EXI/−SI", 0, 5⟩
  , ⟨"EXI/+SI", 0, 0⟩
  , ⟨"UNI/−SI", 1, 0⟩
  , ⟨"UNI/+SI", 0, 0⟩ ]


-- ============================================================
-- SECTION 6: Key Findings
-- ============================================================

/--
The central empirical finding, replicated across both experiments:
three distinct groups of children.
-/
structure ThreeGroupFinding where
  /-- EXI/−SI: existential, no implicatures (literal meaning) -/
  existentialNoSI : Nat
  /-- HOM/+SI: homogeneous with implicatures (adult-like) -/
  homogeneousPlusSI : Nat
  /-- HOM/−SI: homogeneous WITHOUT implicatures (problematic for Magri) -/
  homogeneousNoSI : Nat
  deriving Repr

def exp1Finding : ThreeGroupFinding :=
  { existentialNoSI := 7
  , homogeneousPlusSI := 10
  , homogeneousNoSI := 6 }

def exp2Finding : ThreeGroupFinding :=
  { existentialNoSI := 10
  , homogeneousPlusSI := 7
  , homogeneousNoSI := 5 }

/-- Cross-consistency: ThreeGroupFinding (Section 6) matches
    BayesianGroups (Table 3). Changing either without updating the
    other will break this theorem. -/
theorem exp1_findings_consistent :
    exp1Finding.homogeneousNoSI = exp1Children.homMinusSI ∧
    exp1Finding.homogeneousPlusSI = exp1Children.homPlusSI ∧
    exp1Finding.existentialNoSI = exp1Children.exiMinusSI := by
  exact ⟨rfl, rfl, rfl⟩

/-- Total categorized children in Experiment 2
    (2 children gave inconsistent responses and are excluded). -/
theorem exp2_total_categorized :
    exp2Finding.existentialNoSI + exp2Finding.homogeneousPlusSI +
    exp2Finding.homogeneousNoSI = 22 := by native_decide

/-- The HOM/−SI group exists in BOTH experiments. -/
theorem hom_without_si_exists_exp1 :
    exp1Finding.homogeneousNoSI > 0 := by native_decide

theorem hom_without_si_exists_exp2 :
    exp2Finding.homogeneousNoSI > 0 := by native_decide

/-- The HOM/−SI group is non-trivial (not a single outlier).
    Table 4 confirms this: removing HOM/−SI from the Bayesian model
    degrades fit by Δ_elpd = 50.79 (se = 9.87), over 5 SEs. -/
theorem hom_without_si_nontrivial :
    exp1Finding.homogeneousNoSI ≥ 5 ∧
    exp2Finding.homogeneousNoSI ≥ 5 := by native_decide

/-- The three key groups (EXI/−SI, HOM/+SI, HOM/−SI) account for 23 of 24
    children in Exp 1 (the remaining child was EXI/+SI). No child
    showed the UNIVERSAL pattern in either experiment, ruling out
    children simply assigning universal meaning to the definite plural. -/
theorem three_groups_cover_exp1 :
    exp1Finding.existentialNoSI + exp1Finding.homogeneousPlusSI +
    exp1Finding.homogeneousNoSI = 23 := by native_decide


-- ============================================================
-- SECTION 7: Testing Magri's Predictions
-- ============================================================

/--
Magri's prediction: homogeneity requires the "not-all" scalar
implicature as a subcomputation. Therefore the HOM/−SI group
should not exist.

The data falsify this: HOM/−SI children exist in both experiments.
-/
theorem magri_prediction_falsified :
    magriPrediction.homWithoutSIPossible = false ∧
    exp1Finding.homogeneousNoSI > 0 ∧
    exp2Finding.homogeneousNoSI > 0 := by
  exact ⟨rfl, by native_decide, by native_decide⟩

/--
The second prediction — that SI should not be rarer than homogeneity —
is also challenged. Among children, homogeneous readings are more
prevalent than implicature computation:
- Exp 1: 16 homogeneous vs 11 +SI
- Exp 2: 12 homogeneous vs 7 +SI

The implication between SI and homogeneity is unidirectional in
development: implicatures imply homogeneity, but not vice versa.
-/
structure ImplicatureHomogeneityRates where
  /-- Total children with homogeneous readings -/
  totalHomogeneous : Nat
  /-- Total children computing implicatures -/
  totalPlusSI : Nat
  deriving Repr

def exp1Rates : ImplicatureHomogeneityRates :=
  { totalHomogeneous := 16  -- HOM/−SI (6) + HOM/+SI (10)
  , totalPlusSI := 11 }    -- HOM/+SI (10) + EXI/+SI (1)

def exp2Rates : ImplicatureHomogeneityRates :=
  { totalHomogeneous := 12  -- HOM/−SI (5) + HOM/+SI (7)
  , totalPlusSI := 7 }     -- HOM/+SI (7) + EXI/+SI (0)

/-- In both experiments, homogeneous readings outnumber implicatures. -/
theorem homogeneity_more_prevalent :
    exp1Rates.totalHomogeneous > exp1Rates.totalPlusSI ∧
    exp2Rates.totalHomogeneous > exp2Rates.totalPlusSI := by native_decide

/-- The implication is unidirectional: all +SI children are homogeneous
    (with one exception in Exp 1), but not all homogeneous children
    compute SI. -/
theorem unidirectional_implication :
    -- Exp 1: 10 of 11 +SI children are HOM
    exp1Children.homPlusSI = 10 ∧ exp1Children.exiPlusSI = 1 ∧
    -- Exp 2: all +SI children are HOM (7 of 7)
    exp2Finding.homogeneousPlusSI = 7 := by
  exact ⟨rfl, rfl, rfl⟩


-- ============================================================
-- SECTION 8: End-to-End Argument Against Magri2014
-- ============================================================

open Phenomena.Plurals.Studies.Magri2014 (Role exh doubleExh someMeaning
  allMeaning exh_some exh_the double_strengthening_yields_universal)

/--
End-to-end argumentation chain connecting @cite{magri-2014}'s theory
(formalized in `Magri2014.lean`) to the empirical data in this file.

**The derivation** (examples 10-11 in the paper):

  EXH(SOME)           = SOME ∧ ¬ALL                    -- inner EXH: the "not-all" SI
  EXH(THE)             = THE = SOME                     -- inner EXH: vacuous (no excludable mates)
  EXH(EXH(THE))         = SOME ∧ ¬(SOME ∧ ¬ALL) = ALL  -- outer EXH: negates the SI

**The prediction**: Since `EXH(SOME) = SOME ∧ ¬ALL` is a subcomputation
of `EXH(EXH(THE)) = ALL`, a child who cannot compute the "not-all" SI
cannot derive the universal reading. Without the SI to negate, double
exhaustification is vacuous: `EXH(EXH(THE)) = EXH(THE) = SOME`.
Such children should show the *existential* pattern, not the *homogeneous* pattern.

**The falsification**: HOM/−SI children exist in both experiments — they
show homogeneity without computing the SI. This requires an alternative
source of homogeneity independent of scalar implicatures.

This theorem imports three results from `Magri2014.lean` (the inner EXH
identity, the vacuousness of single EXH for THE, and the main double-
strengthening theorem) and combines them with the empirical data.
-/
theorem magri_derivation_requires_si :
    -- (1) Inner EXH of SOME yields the standard "not-all" SI
    (∀ s, exh .weak s = (someMeaning s && !allMeaning s)) ∧
    -- (2) Inner EXH of THE is vacuous: THE stays SOME
    (∀ s, exh .mystery s = someMeaning s) ∧
    -- (3) Double-EXH uses the SI to derive ALL (the main theorem)
    (∀ s, s.total ≥ 1 → doubleExh .mystery s = allMeaning s) ∧
    -- (4) But HOM/−SI children show homogeneity WITHOUT the SI
    exp1Finding.homogeneousNoSI > 0 ∧
    exp2Finding.homogeneousNoSI > 0 := by
  exact ⟨exh_some, exh_the, double_strengthening_yields_universal,
         by native_decide, by native_decide⟩


-- ============================================================
-- SECTION 9: Developmental Trajectory
-- ============================================================

/--
The paper proposes the following developmental trajectory:

Stage 1: Children start with the literal existential meaning of the
  definite plural (EXI pattern). This is compatible with @cite{magri-2014}'s
  assumption that the plain meaning of THE is existential.

Stage 2: Children acquire homogeneous readings, possibly through a
  mechanism independent of scalar implicatures.

Stage 3: Children acquire scalar implicatures. Those who arrived at
  homogeneity through implicatures now have both; those who arrived
  through another mechanism also have both.

The key insight: stages 2 and 3 are INDEPENDENT. Homogeneity does not
require scalar implicatures as a developmental prerequisite.
-/
inductive DevelopmentalStage where
  | existential   -- literal existential meaning
  | homogeneous   -- homogeneous reading (mechanism-independent)
  | adult         -- homogeneous + scalar implicatures
  deriving Repr, DecidableEq, BEq

/-- The developmental ordering: existential precedes homogeneous
    precedes full adult competence. -/
def stageOrder : DevelopmentalStage → Nat
  | .existential => 0
  | .homogeneous => 1
  | .adult       => 2

/-- The three attested child groups map to developmental stages.
    Returns `none` for groups not attested in children (UNI/±SI,
    EXI/+SI with only 1 child). -/
def groupToStage : ParticipantGroup → Option DevelopmentalStage
  | ⟨.existential, false⟩ => some .existential
  | ⟨.homogeneous, false⟩ => some .homogeneous
  | ⟨.homogeneous, true⟩  => some .adult
  | _                      => none

/-- The three attested groups map to the three developmental stages,
    and the stages form a monotonically increasing sequence. -/
theorem attested_groups_ordered :
    groupToStage exiMinusSI = some .existential ∧
    groupToStage homMinusSI = some .homogeneous ∧
    groupToStage homPlusSI  = some .adult ∧
    stageOrder .existential ≤ stageOrder .homogeneous ∧
    stageOrder .homogeneous ≤ stageOrder .adult := by
  exact ⟨rfl, rfl, rfl, by native_decide, by native_decide⟩


end Phenomena.Plurals.Studies.TieuKrizChemla2019
