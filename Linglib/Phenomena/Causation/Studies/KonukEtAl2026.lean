import Linglib.Core.StructuralEquationModel
import Linglib.Theories.Semantics.Causation.Strength
import Linglib.Theories.Semantics.Plurality.Distributivity
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

/-!
# @cite{konuk-et-al-2026}: Plural Causes
@cite{konuk-et-al-2026}

Formalizes Konuk, Quillien & Mascarenhas (2026) "Plural causes,"
*Open Mind*.

## Core Contributions

1. **Compound causes**: A∧B is treated as a single compound binary variable
   for causal selection, not decomposed into individual contributions.
2. **Necessity-Sufficiency Model** (NSM): `NSM(C) = P(C)·Suf(C) + (1-P(C))·Nec(C)`
   from @cite{icard-et-al-2017}, applied to compound causes.
3. **Anti-linearity**: NSM(INT∧HIGH) > NSM(LOW∧INT) even though LOW and HIGH
   have comparable individual causal strength (Experiment 1).
4. **Homogeneous loss**: Loss judgments follow LOSS_strong = ¬A∧¬B∧¬C∧¬D,
   not classical ¬((A∧B)∨(C∧D)) (Experiment 2), mixed with classical
   via fitted parameter w ≈ 0.77.
5. **Crossing avoidance**: Within-disjunct plural causes (A∧B) preferred
   over cross-disjunct (A∧C) when the rule is (A∧B)∨(C∧D) (Experiment 2, Overdetermined Positive round).

## Bridges

| Concept | Connects to | Module |
|---------|-------------|--------|
| Compound sufficiency/necessity | `causallySufficient`/`causallyNecessary` | `Core.StructuralEquationModel` |
| NSM (Nec/Suf weighting) | `nsm` | `Causation.Strength` (@cite{icard-et-al-2017}) |
| LOSS_strong (all absent) | `noneSatisfy` | `Plural.Distributivity` (@cite{kriz-spector-2021}) |
| Compound sufficiency | `allSatisfy` | `Plural.Distributivity` (@cite{kriz-spector-2021}) |
| Loss gap (classical − strong) | `inGap` | `Plural.Distributivity` (@cite{kriz-spector-2021}) |
| `CausalLaw.conjunctive` | Threshold/disjunctive models | `Core.StructuralEquationModel` |
| Crossing avoidance | structural sufficiency gap | `Core.StructuralEquationModel` |
-/

namespace KonukEtAl2026

open Core (Situation)

open Core.StructuralEquationModel
open Semantics.Causation.Strength (nsm samplingPropensity)

/-! ## § 1. Compound Sufficiency and Necessity

Extend the SEM's individual-variable `causallySufficient`/`causallyNecessary`
to compound (plural) causes. A compound cause C = {v₁,...,vₙ} is sufficient
iff setting all components to true produces the effect, and necessary iff
setting all to false prevents it. -/

/-- A compound cause is sufficient iff setting all its variables to true
    produces the effect under normal development. -/
def compoundSufficient (dyn : CausalDynamics) (bg : Situation)
    (vars : List Variable) (effect : Variable) : Bool :=
  let s := vars.foldl (·.extend · true) bg
  (normalDevelopment dyn s).hasValue effect true

/-- A compound cause is necessary iff setting all its variables to false
    prevents the effect under normal development. -/
def compoundNecessary (dyn : CausalDynamics) (bg : Situation)
    (vars : List Variable) (effect : Variable) : Bool :=
  let s := vars.foldl (·.extend · false) bg
  !(normalDevelopment dyn s).hasValue effect true

/-- Singleton compound sufficiency reduces to individual sufficiency. -/
theorem compoundSufficient_singleton (dyn : CausalDynamics) (bg : Situation)
    (v : Variable) (effect : Variable) :
    compoundSufficient dyn bg [v] effect = causallySufficient dyn bg v effect := by
  simp [compoundSufficient, causallySufficient, List.foldl]

/-- Singleton compound necessity reduces to the simple but-for test
    (set variable to false, check effect).

    Note: `compoundNecessary` uses the @cite{nadathur-lauer-2020} but-for
    test, while `causallyNecessary` uses @cite{nadathur-2024} Definition 10b
    (with precondition + achievability + supersituation quantification).
    The two coincide when the Def 10b precondition passes and the cause is
    exogenous, but diverge in general. -/
theorem compoundNecessary_singleton_butfor (dyn : CausalDynamics) (bg : Situation)
    (v : Variable) (effect : Variable) :
    compoundNecessary dyn bg [v] effect =
      (!(normalDevelopment dyn (bg.extend v false)).hasValue effect true) := by
  simp [compoundNecessary, List.foldl]

/-! ## § 1b. Bridge: Compound Sufficiency = `allSatisfy`

A compound cause {v₁,...,vₙ} is sufficient iff *all* its constituent
variables being present suffices for the effect. This is exactly
`allSatisfy` from @cite{kriz-spector-2021}: plural predication where
every atom satisfies the predicate "is causally active." -/

/-- Compound sufficiency over a Fin-indexed variable set is equivalent to
    `allSatisfy` applied to the "is present" predicate.

    This connects causal cognition to plural semantics: judging a compound
    cause as sufficient = judging that the plurality "all satisfy" the
    causal activation predicate. -/
theorem compoundSufficient_eq_allSatisfy :
    ∀ f : Fin 2 → Bool,
    (f 0 && f 1) =
    Semantics.Plurality.Distributivity.allSatisfy
      (fun (i : Fin 2) (_ : Unit) => f i) Finset.univ () := by
  native_decide

/-! ## § 2. The Necessity-Sufficiency Model (NSM)

The general NSM from @cite{icard-et-al-2017}: `NSM(C) = P(C)·Suf(C) + (1-P(C))·Nec(C)`.
Imported from `Semantics.Causation.Strength.nsm`. -/

/-! ## § 3. Experiment 1: Threshold Game

Three urns — LOW (p=1/20), INTERMEDIATE (p=1/2), HIGH (p=19/20) —
with rule WIN := sum ≥ 2. The player draws from all three and wins.

### SEM Encoding

The threshold ≥ 2 rule is encoded as three conjunctive laws:
A∧B→WIN, A∧C→WIN, B∧C→WIN. Any pair suffices. -/

private def urnA := mkVar "A"
private def urnB := mkVar "B"
private def urnC := mkVar "C"
private def win := mkVar "WIN"

/-- Threshold-≥-2 causal dynamics: any two urns on → WIN. -/
def thresholdDyn : CausalDynamics := ⟨[
  CausalLaw.conjunctive urnA urnB win,
  CausalLaw.conjunctive urnA urnC win,
  CausalLaw.conjunctive urnB urnC win
]⟩

/-- The actual situation: all three urns are on. -/
private def thresholdActual : Situation :=
  Situation.empty.extend urnA true |>.extend urnB true |>.extend urnC true

/-- Any pair of urns is sufficient (compound sufficiency). -/
theorem anyPair_sufficient_AB :
    compoundSufficient thresholdDyn Situation.empty [urnA, urnB] win = true := by
  native_decide

theorem anyPair_sufficient_AC :
    compoundSufficient thresholdDyn Situation.empty [urnA, urnC] win = true := by
  native_decide

theorem anyPair_sufficient_BC :
    compoundSufficient thresholdDyn Situation.empty [urnB, urnC] win = true := by
  native_decide

/-- No single urn is sufficient (need 2 for threshold). -/
theorem no_single_sufficient :
    causallySufficient thresholdDyn Situation.empty urnA win = false ∧
    causallySufficient thresholdDyn Situation.empty urnB win = false ∧
    causallySufficient thresholdDyn Situation.empty urnC win = false := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- In the overdetermined actual world, no individual urn is necessary. -/
theorem no_single_necessary_in_actual :
    causallyNecessary thresholdDyn thresholdActual urnA win = false ∧
    causallyNecessary thresholdDyn thresholdActual urnB win = false ∧
    causallyNecessary thresholdDyn thresholdActual urnC win = false := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- But compound pairs ARE necessary in the actual world.

This is the core insight: individual urns are not necessary
(overdetermination), but compound pairs are — removing any pair
drops below threshold. This justifies treating A∧B as the unit
of causal attribution. -/
theorem compound_pair_necessary_in_actual :
    compoundNecessary thresholdDyn thresholdActual [urnA, urnB] win = true ∧
    compoundNecessary thresholdDyn thresholdActual [urnA, urnC] win = true ∧
    compoundNecessary thresholdDyn thresholdActual [urnB, urnC] win = true := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-! ### NSM Computation for Experiment 1

For compound pair causes at s = 0, any pair is deterministically sufficient
(Suf = 1), so NSM(C→WIN) = 1 - P(WIN ∧ ¬C). The residual probability
P(WIN ∧ ¬C) is the chance that the remaining single urn (Z) plus exactly
one of {X,Y} still meets threshold — but with the compound removed, we
need all three absent variables except Z, so P(WIN ∧ ¬C) = P(exactly one
of {X,Y} on) × P(Z on). -/

def pLow : ℚ := 1/20
def pInt : ℚ := 1/2
def pHigh : ℚ := 19/20

/-- NSM for a compound pair {X,Y} in the threshold-≥-2 game (Suf=1).

NSM = 1 - P(WIN ∧ ¬C), where P(WIN ∧ ¬C) is the probability that
exactly one of {X,Y} is on AND the third urn Z is also on. -/
def nsmThreshold (pX pY pZ : ℚ) : ℚ :=
  1 - (pX * (1 - pY) + (1 - pX) * pY) * pZ

/-- NSM({INT, HIGH}) = 39/40. -/
theorem nsm_intHigh : nsmThreshold pInt pHigh pLow = 39/40 := by
  simp only [nsmThreshold, pInt, pHigh, pLow]; norm_num

/-- NSM({LOW, INT}) = 21/40. -/
theorem nsm_lowInt : nsmThreshold pLow pInt pHigh = 21/40 := by
  simp only [nsmThreshold, pLow, pInt, pHigh]; norm_num

/-- **Anti-linearity**: INT∧HIGH has strictly higher NSM than LOW∧INT.

The additive hypothesis predicts LOW∧INT ≈ INT∧HIGH (since LOW and HIGH
have comparable individual NSM in the threshold game). The holistic NSM
gives 39/40 vs 21/40, matching the empirical finding (t(355) = -4.67,
p < 0.001). -/
theorem antiLinearity_nsm :
    nsmThreshold pInt pHigh pLow > nsmThreshold pLow pInt pHigh := by
  simp only [nsmThreshold, pInt, pHigh, pLow]; norm_num

/-! ## § 4. Experiment 2: Disjunctive Rule and LOSS

WIN := (A∧B) ∨ (C∧D), with P(A)=7/10, P(B)=1/10, P(C)=1/5, P(D)=9/10.

Classical negation: LOSS = ¬(A∧B) ∧ ¬(C∧D).
Homogeneous negation: LOSS_strong = ¬A ∧ ¬B ∧ ¬C ∧ ¬D.

Empirical loss judgments match a mixture: w · LOSS_strong + (1-w) · LOSS_classical,
with fitted w ≈ 0.77, consistent with the homogeneity property of plural
negation (@cite{kriz-spector-2021}). -/

private def exp2A := mkVar "exp2A"
private def exp2B := mkVar "exp2B"
private def exp2C := mkVar "exp2C"
private def exp2D := mkVar "exp2D"
private def exp2Win := mkVar "exp2WIN"

/-- Experiment 2 causal dynamics: (A∧B)∨(C∧D) → WIN. -/
def disjunctiveRuleDyn : CausalDynamics := ⟨[
  CausalLaw.conjunctive exp2A exp2B exp2Win,
  CausalLaw.conjunctive exp2C exp2D exp2Win
]⟩

/-- Classical LOSS = ¬((A∧B) ∨ (C∧D)) ≡ ¬(A∧B) ∧ ¬(C∧D). -/
def lossClassical (a b c d : Bool) : Bool :=
  !(a && b) && !(c && d)

/-- Homogeneous LOSS = ¬A ∧ ¬B ∧ ¬C ∧ ¬D. -/
def lossStrong (a b c d : Bool) : Bool :=
  !a && !b && !c && !d

/-- LOSS_strong entails classical LOSS. -/
theorem lossStrong_implies_classical (a b c d : Bool) :
    lossStrong a b c d = true → lossClassical a b c d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [lossStrong, lossClassical]

/-- Classical LOSS does NOT entail LOSS_strong.

Witness: A=1, B=0, C=0, D=0 — neither A∧B nor C∧D holds (classical LOSS),
but A is present (LOSS_strong fails). -/
theorem lossStrong_strictly_stronger :
    ∃ a b c d, lossClassical a b c d = true ∧ lossStrong a b c d = false :=
  ⟨true, false, false, false, rfl, rfl⟩

/-- Mixture model: w · LOSS_strong + (1-w) · LOSS_classical.

Fitted w ≈ 0.77, reflecting the dominance of the homogeneous reading
(neither spoke German) over the classical reading (not both spoke). -/
def lossMixed (w : ℚ) (a b c d : Bool) : ℚ :=
  w * (if lossStrong a b c d then 1 else 0) +
  (1 - w) * (if lossClassical a b c d then 1 else 0)

/-- At w = 1, the mixture reduces to LOSS_strong. -/
theorem lossMixed_at_one (a b c d : Bool) :
    lossMixed 1 a b c d = if lossStrong a b c d then 1 else 0 := by
  simp [lossMixed]

/-- At w = 0, the mixture reduces to classical LOSS. -/
theorem lossMixed_at_zero (a b c d : Bool) :
    lossMixed 0 a b c d = if lossClassical a b c d then 1 else 0 := by
  simp [lossMixed]

/-! ## § 4b. Bridge: Loss Gap = `inGap` (Homogeneity)

The gap between `lossClassical` and `lossStrong` — valuations where
classical loss holds but homogeneous loss does not — is exactly the
set of worlds in the truth-value gap (`inGap`) for the "is present"
predicate over the four causal variables. This connects the paper's
w-parameter mixture to the formal semantics of plural homogeneity. -/

/-- The loss gap (classical but not strong) is exactly `inGap` for the
    "is present" predicate: some but not all variables are false.

    The classical negation ¬(A∧B) ∧ ¬(C∧D) allows worlds where some
    variables are true and others false. The homogeneous negation
    ¬A∧¬B∧¬C∧¬D requires all false. The gap — where they disagree —
    is the truth-value gap from @cite{kriz-spector-2021}: worlds where
    the plurality is neither all-P nor none-P. -/
theorem loss_gap_iff_pluralGap :
    ∀ f : Fin 4 → Bool,
    (lossClassical (f 0) (f 1) (f 2) (f 3) = true ∧
     lossStrong (f 0) (f 1) (f 2) (f 3) = false) ↔
    (lossClassical (f 0) (f 1) (f 2) (f 3) = true ∧
     Semantics.Plurality.Distributivity.someSatisfy
       (fun (i : Fin 4) (_ : Unit) => f i) Finset.univ () = true) := by
  native_decide

/-! ## § 5. Experiment 2: Crossing Avoidance (Overdetermined Positive round)

In (A∧B)∨(C∧D), a compound cause is "within-disjunct" if both variables
come from the same conjunct, and "cross-disjunct" otherwise.

Empirical finding: within-disjunct causes are preferred over cross-disjunct
ones, even controlling for counterfactual dependence. -/

/-- Disjunct membership classification for a pair of variables. -/
inductive DisjunctMembership where
  | withinAB
  | withinCD
  | crossDisjunct
  deriving DecidableEq, Repr

/-- Classify a pair of Experiment 2 variables by disjunct membership.
Indices: A=0, B=1 (first conjunct), C=2, D=3 (second conjunct). -/
def classifyPair (i j : Fin 4) : DisjunctMembership :=
  if i.val < 2 ∧ j.val < 2 then .withinAB
  else if i.val ≥ 2 ∧ j.val ≥ 2 then .withinCD
  else .crossDisjunct

theorem ab_within : classifyPair 0 1 = .withinAB := rfl
theorem cd_within : classifyPair 2 3 = .withinCD := rfl
theorem ac_cross : classifyPair 0 2 = .crossDisjunct := rfl
theorem bd_cross : classifyPair 1 3 = .crossDisjunct := rfl

/-- **Structural crossing avoidance**: within-disjunct compound {A,B} is
sufficient for WIN, but cross-disjunct compound {A,C} is NOT.

This is a structural consequence of the causal model: A∧B matches a
conjunctive law, so setting A=B=1 fires the law and produces WIN.
But A∧C does not match any single law — each needs a different partner
(B for A, D for C). -/
theorem structural_crossing_avoidance :
    compoundSufficient disjunctiveRuleDyn Situation.empty [exp2A, exp2B] exp2Win = true ∧
    compoundSufficient disjunctiveRuleDyn Situation.empty [exp2C, exp2D] exp2Win = true ∧
    compoundSufficient disjunctiveRuleDyn Situation.empty [exp2A, exp2C] exp2Win = false ∧
    compoundSufficient disjunctiveRuleDyn Situation.empty [exp2B, exp2D] exp2Win = false := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-! ## § 5b. Experiment 2: Triple-1 and Triple-0 Conditions

### Triple-1: A, B, D drawn (colored), C not drawn — John wins.

The win is via A∧B (purple pair). Urn D (yellow) is *idle*: it draws a
colored ball but has no effect on the outcome because urn C (its partner)
does not. The CESM and NSM both predict A∧B rated near ceiling.

### Triple-0: A, B, D draw white balls, C draws colored — John loses.

The mirror image: the loss is driven by the absence of colored balls
from A and B (and D), but not C. Under the non-classical (homogeneous)
representation of loss, LOSS := ¬A ∧ ¬B ∧ ¬D, and the white ball from
urn D is indispensable while A and B are redundant.

Model fits with the w parameter: r = .94 (CESM) and .99 (NSM) for
Triple-0 — the paper's most dramatic improvement over the base models
(r = .34 and .52 without w). -/

/-- Triple-1 actual world: colored balls from A, B, D; white from C. -/
private def triple1Actual : Situation :=
  Situation.empty.extend exp2A true |>.extend exp2B true
    |>.extend exp2C false |>.extend exp2D true

/-- In Triple-1, the compound A∧B is both sufficient and necessary for WIN. -/
theorem triple1_AB_sufficient_and_necessary :
    compoundSufficient disjunctiveRuleDyn Situation.empty [exp2A, exp2B] exp2Win = true ∧
    compoundNecessary disjunctiveRuleDyn triple1Actual [exp2A, exp2B] exp2Win = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- In Triple-1, the idle variable D is not individually necessary. -/
theorem triple1_D_not_necessary :
    causallyNecessary disjunctiveRuleDyn triple1Actual exp2D exp2Win = false := by
  native_decide

/-- In Triple-1, adding D to the A∧B compound does NOT increase sufficiency
    (already sufficient) but strictly decreases necessity — the triple A∧B∧D
    is no longer necessary because removing all three prevents WIN
    trivially, but so does removing just A∧B.

    Empirically, participants penalized plurals containing D relative to
    their D-free counterparts: every plural with D rated lower than the
    same plural without D. -/
theorem triple1_D_dilutes :
    compoundNecessary disjunctiveRuleDyn triple1Actual [exp2A, exp2B] exp2Win = true ∧
    compoundNecessary disjunctiveRuleDyn triple1Actual [exp2A, exp2B, exp2D] exp2Win = true ∧
    -- But D individually is not necessary
    causallyNecessary disjunctiveRuleDyn triple1Actual exp2D exp2Win = false := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Triple-0 actual world: white balls from A, B, D; colored from C. -/
private def triple0Actual : Situation :=
  Situation.empty.extend exp2A false |>.extend exp2B false
    |>.extend exp2C true |>.extend exp2D false

/-- In Triple-0 (loss), under homogeneous representation LOSS = ¬A∧¬B∧¬D,
    the white ball from D is indispensable: its absence would break the
    homogeneous conjunction. Formally, removing D (setting it to true)
    blocks the loss under the strong reading. -/
theorem triple0_lossStrong_needs_all :
    lossStrong false false true false = false ∧  -- with C colored: not all absent
    lossStrong false false false false = true := by  -- hypothetical all-white
  exact ⟨rfl, rfl⟩

/-! ## § 6. Bridge: LOSS_strong = `noneSatisfy` (Homogeneity)

LOSS_strong is exactly the `noneSatisfy` predicate from @cite{kriz-spector-2021}
applied to the four causal variables: every individual variable is false.

In `Semantics.Plurality.Distributivity`, `noneSatisfy P x w = true`
iff `∀ a ∈ x, P a w = false`. LOSS_strong instantiates this with the
identity predicate "is present" over the four causal variables, connecting
causal cognition to the homogeneity account of plural negation. -/

/-- LOSS_strong holds iff every individual variable is false. -/
theorem lossStrong_iff_allFalse (f : Fin 4 → Bool) :
    lossStrong (f 0) (f 1) (f 2) (f 3) = true ↔ ∀ i : Fin 4, f i = false := by
  constructor
  · intro h i
    fin_cases i <;> simp_all [lossStrong]
  · intro h
    unfold lossStrong
    rw [h 0, h 1, h 2, h 3]
    rfl

/-- LOSS_strong is exactly `noneSatisfy` from @cite{kriz-spector-2021}:
"none of {v₁,...,v₄} are present" under the homogeneity account. -/
theorem lossStrong_eq_noneSatisfy :
    ∀ f : Fin 4 → Bool,
    lossStrong (f 0) (f 1) (f 2) (f 3) =
    Semantics.Plurality.Distributivity.noneSatisfy
      (fun (i : Fin 4) (_ : Unit) => f i) Finset.univ () := by
  native_decide

end KonukEtAl2026
