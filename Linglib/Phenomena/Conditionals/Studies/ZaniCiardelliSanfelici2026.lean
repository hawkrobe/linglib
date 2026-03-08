import Linglib.Theories.Semantics.Conditionals.AlternativeSensitive
import Linglib.Phenomena.Plurals.Studies.TieuKrizChemla2019
import Mathlib.Data.Rat.Defs

/-!
# @cite{zani-ciardelli-sanfelici-2026} — SDA from Acquisition

Simplification of disjunctive antecedents: Insights from acquisition.
*Semantics and Pragmatics* 19(3).

## Core Contribution

Experimental study of 148 Italian children (ages 4;1–9;11) and 28 adults
on disjunctive antecedent conditionals (DACs), testing three readings:

1. **SDA** (Simplification): "if A or B, C" ≡ "(if A, C) and (if B, C)"
2. **DCR** (Disjunctive Conditional Reading): "if A or B, C" ≡ "(if A, C) or (if B, C)"
3. **AR** (Asymmetric Reading): only the more realistic disjunct matters

## Key Findings

1. SDA is the preferred reading at all ages, already dominant at age 4–5
2. AR is nearly absent (2.3% of children's responses)
3. DCR decreases with age while SDA increases — a DCR→SDA developmental
   shift strictly parallel to the existential→universal shift in plural
   definites (@cite{tieu-kriz-chemla-2019})
4. No indicative/counterfactual difference (Mode non-significant, p = 0.869)
5. SDA does not require equally realistic disjuncts (contra @cite{lewis-1973})

## Theoretical Implications

The DCR→SDA trajectory supports homogeneity-based accounts
(@cite{santorio-2018}, @cite{cariani-goldstein-2020}) over:
- **@cite{lewis-1973}**: predicts AR when disjuncts differ in realism; AR is absent
- **@cite{bar-lev-fox-2020}**: predicts AR→SDA shift; observed shift is DCR→SDA

## Connection to Linglib

- DAC readings use the alternative-sensitive conditional semantics from
  `AlternativeSensitive.lean` (@cite{santorio-2018}): `homogeneityEval`,
  `sdaEval`, `dcrEval`
- SDA/DCR correspond to conjunctive/disjunctive `ProjectionType`
- Developmental trajectory parallels @cite{tieu-kriz-chemla-2019}'s
  existential→homogeneous shift
-/

namespace Phenomena.Conditionals.Studies.ZaniCiardelliSanfelici2026

open Core.Duality (Truth3 ProjectionType)
open Semantics.Conditionals.AlternativeSensitive
open Semantics.Conditionals.Counterfactual (closestWorldsB)


-- ============================================================
-- SECTION 1: Three Readings of DACs
-- ============================================================

/-- The three theoretically predicted readings of disjunctive antecedent
    conditionals (DACs). Table 2 of the paper. -/
inductive DACReading where
  | sda   -- "if A or B, C" ≡ (if A, C) ∧ (if B, C)
  | dcr   -- "if A or B, C" ≡ (if A, C) ∨ (if B, C)
  | ar    -- "if A or B, C" ≡ (if A, C), where A is more realistic
  deriving Repr, DecidableEq, BEq

/-- Logical strength ordering: SDA ≥ AR ≥ DCR. -/
def DACReading.strength : DACReading → Nat
  | .sda => 2  | .ar => 1  | .dcr => 0

theorem sda_entails_ar : DACReading.sda.strength ≥ DACReading.ar.strength := by
  native_decide

theorem ar_entails_dcr : DACReading.ar.strength ≥ DACReading.dcr.strength := by
  native_decide


-- ============================================================
-- SECTION 2: DAC Readings ↔ Projection Types
-- ============================================================

-- Alternative-sensitive conditional semantics (altConditionalResults,
-- sdaEval, dcrEval, homogeneityEval, lewisDAC) are imported from
-- Theories/Semantics/Conditionals/AlternativeSensitive.lean

/-- SDA = conjunctive projection over alternatives.
    DCR = disjunctive projection over alternatives.
    This is the same duality as quantifier strength in
    @cite{ramotowska-santorio-2025}. -/
def dacProjection : DACReading → ProjectionType
  | .sda => .conjunctive
  | .dcr => .disjunctive
  | .ar  => .disjunctive

/-- `List.all id` on a two-element list is conjunction. -/
private theorem all_id_pair (a b : Bool) : [a, b].all id = (a && b) := by
  cases a <;> cases b <;> rfl

/-- Alternative semantics validates SDA universally (for two alternatives):
    "if {A,B}, C" ≡ ∀p ∈ {A,B}. min_w(p) ⊆ C ≡ (if A, C) ∧ (if B, C).
    Under Lewis, SDA is only contingently valid. -/
theorem alt_semantics_validates_sda {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W)
    (A B C : W → Bool) (w : W) :
    sdaEval closer domain [A, B] C w =
    (((closestWorldsB closer domain w (domain.filter A)).isEmpty ||
      (closestWorldsB closer domain w (domain.filter A)).all C) &&
     ((closestWorldsB closer domain w (domain.filter B)).isEmpty ||
      (closestWorldsB closer domain w (domain.filter B)).all C)) := by
  unfold sdaEval altConditionalResults
  exact all_id_pair _ _


-- ============================================================
-- SECTION 4: Experimental Design
-- ============================================================

/-- Conditional mode (indicative vs counterfactual). -/
inductive ConditionalMode where
  | indicative     -- "If the squirrel or the tortoise wins, it will get a hazelnut"
  | counterfactual -- "If the squirrel or the tortoise had won, it would have got a hazelnut"
  deriving Repr, DecidableEq, BEq

/-- Age groups in the study. Table 1. -/
inductive AgeGroup where
  | age4   | age5   | age6   | age7   | age8   | age9   | adult
  deriving Repr, DecidableEq, BEq

/-- Number of eligible participants per age group. Table 1. -/
def AgeGroup.n : AgeGroup → Nat
  | .age4 => 8   | .age5 => 28  | .age6 => 28
  | .age7 => 28  | .age8 => 28  | .age9 => 28  | .adult => 28

theorem total_participants :
    AgeGroup.n .age4 + AgeGroup.n .age5 + AgeGroup.n .age6 +
    AgeGroup.n .age7 + AgeGroup.n .age8 + AgeGroup.n .age9 +
    AgeGroup.n .adult = 176 := by native_decide

theorem total_children :
    AgeGroup.n .age4 + AgeGroup.n .age5 + AgeGroup.n .age6 +
    AgeGroup.n .age7 + AgeGroup.n .age8 + AgeGroup.n .age9 = 148 := by
  native_decide


-- ============================================================
-- SECTION 5: Target Item Design (Table 3)
-- ============================================================

/-- The four target items per scenario. Table 3.
    Each item has a disjunctive antecedent where the consequent
    matches one disjunct's prize (making one simplification true,
    one false). -/
structure TargetItem where
  label : String
  sdaPrediction : Bool  -- SDA: all false (both simplifications required)
  dcrPrediction : Bool  -- DCR: all true (one simplification suffices)
  arPrediction : Bool   -- AR: TTFF (true when more realistic competitor matches)
  deriving Repr

def targetItems : List TargetItem :=
  [ ⟨"if Squirrel or Tortoise, then Hazelnut", false, true, true⟩
  , ⟨"if Tortoise or Squirrel, then Hazelnut", false, true, true⟩
  , ⟨"if Squirrel or Tortoise, then Lettuce",  false, true, false⟩
  , ⟨"if Tortoise or Squirrel, then Lettuce",  false, true, false⟩ ]

-- SDA predicts FFFF.
#guard targetItems.all (·.sdaPrediction == false)
-- DCR predicts TTTT.
#guard targetItems.all (·.dcrPrediction == true)
-- AR predicts TTFF.
#guard targetItems.map (·.arPrediction) == [true, true, false, false]


-- ============================================================
-- SECTION 6: Aggregate Results
-- ============================================================

/-- Overall pattern rates (percentages, one-decimal precision as reported). -/
structure PatternRates where
  sda : ℚ
  dcr : ℚ
  ar : ℚ
  other : ℚ
  deriving Repr

/-- Children's overall rates (across modes and age groups). -/
def childrenOverall : PatternRates :=
  { sda := 450/10, dcr := 182/10, ar := 23/10, other := 345/10 }

/-- Adults' overall rates (across modes).
    From Table 6 profiles: 26 SDA, 1 DCR, 1 mixed (AR ctf / DCR ind).
    Scenario-level: SDA 92.9%, DCR 5.4%, AR 1.8%. -/
def adultsOverall : PatternRates :=
  { sda := 929/10, dcr := 54/10, ar := 18/10, other := 0 }

/-- **Finding 1**: SDA is the most frequent reading for both groups. -/
theorem sda_most_frequent :
    childrenOverall.sda > childrenOverall.dcr ∧
    childrenOverall.sda > childrenOverall.ar ∧
    adultsOverall.sda > adultsOverall.dcr := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- **Finding 2**: AR is nearly absent. -/
theorem ar_nearly_absent :
    childrenOverall.ar < 5 ∧ adultsOverall.ar < 5 := by
  exact ⟨by native_decide, by native_decide⟩


-- ============================================================
-- SECTION 7: Mode Non-Significance (Figure 5)
-- ============================================================

/-- Rates per mode (from Figure 5). All four pattern categories. -/
structure ModeRates where
  indicativeSDA : ℚ
  counterfactualSDA : ℚ
  indicativeDCR : ℚ
  counterfactualDCR : ℚ
  indicativeAR : ℚ
  counterfactualAR : ℚ
  indicativeOther : ℚ
  counterfactualOther : ℚ
  deriving Repr

def childrenByMode : ModeRates :=
  { indicativeSDA := 453/10, counterfactualSDA := 436/10
  , indicativeDCR := 196/10, counterfactualDCR := 182/10
  , indicativeAR := 20/10,   counterfactualAR := 24/10
  , indicativeOther := 331/10, counterfactualOther := 358/10 }

def adultsByMode : ModeRates :=
  { indicativeSDA := 929/10, counterfactualSDA := 929/10
  , indicativeDCR := 71/10,  counterfactualDCR := 36/10
  , indicativeAR := 0,       counterfactualAR := 36/10
  , indicativeOther := 0,    counterfactualOther := 0 }

/-- **Finding 4**: No indicative/counterfactual difference.
    Adults show identical SDA rates; children are very similar.
    (Table 4: Mode coefficient p = 0.869 for DCR vs SDA.) -/
theorem mode_nonsignificant :
    adultsByMode.indicativeSDA = adultsByMode.counterfactualSDA := by
  native_decide


-- ============================================================
-- SECTION 7b: Developmental Trajectory (Figure 4)
-- ============================================================

/-- Per-age-group pattern rates (from Figure 4 bar chart annotations).
    This is the paper's core developmental data.
    Values are approximate (read from bar chart, not tabulated in paper). -/
def ratesByAge : AgeGroup → PatternRates
  | .age4  => { sda := 344/10, dcr := 312/10, ar := 0,     other := 344/10 }
  | .age5  => { sda := 330/10, dcr := 196/10, ar := 9/10,  other := 464/10 }
  | .age6  => { sda := 357/10, dcr := 259/10, ar := 18/10, other := 366/10 }
  | .age7  => { sda := 482/10, dcr := 259/10, ar := 9/10,  other := 250/10 }
  | .age8  => { sda := 482/10, dcr := 116/10, ar := 45/10, other := 357/10 }
  | .age9  => { sda := 598/10, dcr := 54/10,  ar := 36/10, other := 312/10 }
  | .adult => { sda := 929/10, dcr := 54/10,  ar := 18/10, other := 0 }

/-- **Core developmental finding**: SDA rates increase monotonically
    from age 5 onward. -/
theorem sda_increases_from_age5 :
    (ratesByAge .age5).sda ≤ (ratesByAge .age6).sda ∧
    (ratesByAge .age6).sda ≤ (ratesByAge .age7).sda ∧
    (ratesByAge .age7).sda ≤ (ratesByAge .age8).sda ∧
    (ratesByAge .age8).sda ≤ (ratesByAge .age9).sda ∧
    (ratesByAge .age9).sda ≤ (ratesByAge .adult).sda := by
  exact ⟨by native_decide, by native_decide, by native_decide,
         by native_decide, by native_decide⟩

/-- **Core developmental finding**: DCR rates decrease from age 7 onward. -/
theorem dcr_decreases_from_age7 :
    (ratesByAge .age7).dcr ≥ (ratesByAge .age8).dcr ∧
    (ratesByAge .age8).dcr ≥ (ratesByAge .age9).dcr ∧
    (ratesByAge .age9).dcr ≥ (ratesByAge .adult).dcr := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- The developmental shift: SDA overtakes DCR. At every age,
    SDA ≥ DCR, and by adulthood SDA dominates completely. -/
theorem sda_dominates_dcr_at_all_ages :
    ∀ g : AgeGroup, (ratesByAge g).sda ≥ (ratesByAge g).dcr := by
  intro g; cases g <;> native_decide

/-- AR is marginal (< 5%) at every age group. This rules out Lewis's
    prediction that AR should be common in younger children. -/
theorem ar_marginal_at_all_ages :
    ∀ g : AgeGroup, (ratesByAge g).ar < 5 := by
  intro g; cases g <;> native_decide


-- ============================================================
-- SECTION 7c: "Half True" Refusals — Evidence for Homogeneity Gap
-- ============================================================

/-- 9.6% of children refused to judge DACs as true or false, saying
    they were "half true and half false." This is direct behavioral
    evidence for the truth-value gap predicted by homogeneity theory:
    when one simplification is true and the other false, the DAC
    lacks a definite truth value.

    10 children showed this pattern consistently across all 4 scenarios;
    6 more did so in at least one scenario. -/
def halfTrueRefusalRate : ℚ := 96/10

/-- The refusal rate is substantial — nearly 1 in 10 children. -/
theorem halfTrue_nontrivial : halfTrueRefusalRate > 5 := by native_decide


-- ============================================================
-- SECTION 8: Individual Profiles (Tables 5–6)
-- ============================================================

/-- Cross-mode consistency: children overwhelmingly derive the same
    reading in both indicative and counterfactual scenarios.
    Table 5 diagonal entries. -/
structure ProfileCounts where
  sdaSda : Nat
  dcrDcr : Nat
  arAr : Nat
  otherOther : Nat
  deriving Repr

def childProfiles : ProfileCounts :=
  { sdaSda := 52, dcrDcr := 15, arAr := 2, otherOther := 29 }

def adultProfiles : ProfileCounts :=
  { sdaSda := 26, dcrDcr := 1, arAr := 0, otherOther := 0 }

/-- Children who are consistent across modes (on the diagonal). -/
theorem children_mostly_consistent :
    let diagonal := childProfiles.sdaSda + childProfiles.dcrDcr +
                    childProfiles.arAr + childProfiles.otherOther
    -- 98 of 148 children show consistent profiles
    diagonal = 98 := by native_decide

/-- Adults are almost all SDA-consistent. -/
theorem adults_sda_dominant : adultProfiles.sdaSda = 26 := rfl


-- ============================================================
-- SECTION 9: SDA Without Equally Realistic Disjuncts (Table 8)
-- ============================================================

/-- Rates among participants who accepted the closeness evaluation item
    (indicating they regard one disjunct as MORE realistic). Table 8.
    Lewis predicts AR for these participants. -/
structure NonEquallyRealisticRates where
  adultsSDA : ℚ
  childrenSDA : ℚ
  adultsAR : ℚ
  childrenAR : ℚ
  deriving Repr

def nonEquallyRealistic : NonEquallyRealisticRates :=
  { adultsSDA := 8776/100, childrenSDA := 3934/100
  , adultsAR := 408/100,   childrenAR := 284/100 }

/-- **Finding 5**: Even among participants who regard disjuncts as
    non-equally realistic, SDA dominates and AR is marginal.
    This directly falsifies Lewis's prediction. -/
theorem sda_without_equal_realism :
    nonEquallyRealistic.adultsSDA > nonEquallyRealistic.adultsAR ∧
    nonEquallyRealistic.childrenSDA > nonEquallyRealistic.childrenAR := by
  exact ⟨by native_decide, by native_decide⟩


-- ============================================================
-- SECTION 10: Parallel with Plural Definite Acquisition
-- ============================================================

open Phenomena.Plurals.Studies.TieuKrizChemla2019
  (DefinitePluralReading DevelopmentalStage)

/-- The developmental trajectory for DACs parallels the trajectory for
    plural definites (@cite{tieu-kriz-chemla-2019}):

    | Plural definites | DACs | Resolution |
    |------------------|------|------------|
    | Existential (EXI) | DCR | ∃ (some satisfy → true) |
    | Homogeneous (HOM) | SDA | ∀ (all must satisfy) |
    | Universal (UNI) | — | — |

    Both phenomena show the same developmental pattern: younger children
    start existential (accepting when ANY element satisfies) and shift
    to universal/homogeneous (requiring ALL elements to satisfy). -/
def pluralToDACParallel : DefinitePluralReading → Option DACReading
  | .existential => some .dcr  -- existential ↔ disjunctive conditional
  | .homogeneous => some .sda  -- homogeneous ↔ simplification
  | .universal   => none       -- no direct DAC analogue

/-- The developmental parallel: both trajectories go from existential-like
    to universal-like readings. -/
def dacDevelopmentalStage : DACReading → Option DevelopmentalStage
  | .dcr => some .existential  -- DCR = existential resolution of homogeneity
  | .sda => some .homogeneous  -- SDA = universal resolution (the gap)
  | .ar  => none               -- AR has no plural parallel

/-- The parallel is structurally exact: DCR maps to the existential stage,
    SDA maps to the homogeneous stage. -/
theorem parallel_exact :
    dacDevelopmentalStage .dcr = some .existential ∧
    dacDevelopmentalStage .sda = some .homogeneous := by
  exact ⟨rfl, rfl⟩

/-- Both phenomena show the same direction of shift. In TieuKrizChemla2019,
    the EXI/−SI group (existential, no implicatures) exists in young
    children and gives way to HOM groups. Here, DCR exists in young
    children and gives way to SDA. -/
theorem shift_direction_matches :
    -- DCR is more common than SDA would predict for adults
    childrenOverall.dcr > adultsOverall.dcr ∧
    -- SDA increases toward adult levels
    adultsOverall.sda > childrenOverall.sda := by
  exact ⟨by native_decide, by native_decide⟩


-- ============================================================
-- SECTION 11: Theory Evaluation
-- ============================================================

/-- Theories of SDA and their predictions about developmental trajectory. -/
inductive SDATheory where
  | lewis             -- Lewis 1973: Boolean disjunction
  | alternativeSem    -- Alonso-Ovalle 2009, Ciardelli 2016: alt semantics
  | homogeneity       -- Santorio 2018, Cariani & Goldstein 2020: alt + homogeneity
  | exhaustification  -- Bar-Lev & Fox 2020: EXH-based
  deriving Repr, DecidableEq, BEq

/-- What each theory predicts as the pre-SDA reading in children. -/
def SDATheory.predictedPreSDA : SDATheory → Option DACReading
  | .lewis            => some .ar   -- Lewis predicts AR as the literal reading
  | .alternativeSem   => none       -- no developmental prediction
  | .homogeneity      => some .dcr  -- DCR = existential resolution of gap
  | .exhaustification => some .ar   -- AR is the literal (Lewis) reading before EXH

/-- The observed pre-SDA reading is DCR, not AR. -/
def observedPreSDA : DACReading := .dcr

/-- Homogeneity theory correctly predicts the developmental trajectory.
    Lewis and exhaustification predict AR as the pre-SDA stage,
    but AR is nearly absent. -/
theorem homogeneity_fits_trajectory :
    SDATheory.homogeneity.predictedPreSDA = some observedPreSDA ∧
    SDATheory.lewis.predictedPreSDA ≠ some observedPreSDA ∧
    SDATheory.exhaustification.predictedPreSDA ≠ some observedPreSDA := by
  exact ⟨rfl, by decide, by decide⟩


-- ============================================================
-- SECTION 12: Five Research Questions — Summary
-- ============================================================

/-!
## Answers to the Five Research Questions

**Q1: At what age does SDA arise?**
Already at age 4–5, SDA is the most frequent non-deviant reading.
This parallels the early emergence of free-choice inferences
(@cite{tieu-etal-2015}).

**Q2: Do children shift from AR to SDA?**
No. AR is nearly absent (2.3%). The two participants who consistently
showed AR were aged 8;0 and 9;7 — not young children with
undeveloped pragmatic skills. This is unexpected on
@cite{bar-lev-fox-2020}'s account.

**Q3: Do children shift from DCR to SDA?**
Yes. DCR is higher in younger children (~25% at ages 4–7) and decreases
with age, while SDA increases. This DCR→SDA shift parallels the
EXI→HOM shift in plural definites (@cite{tieu-kriz-chemla-2019}).

**Q4: Does SDA arise earlier for indicatives than counterfactuals?**
No. Mode has no significant effect (p = 0.869). Children show the
same reading in both modes (Table 5). This supports uniform
accounts of conditionals.

**Q5: Does SDA require equally realistic disjuncts?**
No. Among participants who regarded disjuncts as non-equally realistic,
SDA still dominated (87.76% adults, 39.34% children) and AR was
marginal (4.08% adults, 2.84% children). This falsifies Lewis's
prediction that non-equally-realistic disjuncts should yield AR.
-/


end Phenomena.Conditionals.Studies.ZaniCiardelliSanfelici2026
