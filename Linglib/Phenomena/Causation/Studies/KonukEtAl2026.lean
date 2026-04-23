import Linglib.Core.Causal.V2.SEM.Bool
import Linglib.Core.Causal.V2.SEM.Counterfactual
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
   over cross-disjunct (A∧C) when the rule is (A∧B)∨(C∧D) (Experiment 2).

## V2 substrate

The two scenarios (threshold game + disjunctive rule) share a single
`KonukVar` inductive enum (9 vertices). Each scenario's win-vertex
mechanism is a Boolean function of its parents (threshold-≥-2 for
`win`; (A∧B)∨(C∧D) for `exp2Win`). Compound sufficiency/necessity
are polymorphic predicates over `BoolSEM` defined via `developOn`
with the explicit vertex list.
-/

namespace KonukEtAl2026

open Core.Causal.V2 Core.Causal.V2.Mechanism Core.Causal.V2.SEM
open Semantics.Causation.Strength (nsm samplingPropensity)

-- ════════════════════════════════════════════════════
-- § Vertex enum (combines both experiments)
-- ════════════════════════════════════════════════════

/-- All vertices used by both Konuk experiments. -/
inductive KonukVar
  -- Threshold game (Experiment 1): three urns + win
  | urnA | urnB | urnC | win
  -- Disjunctive rule (Experiment 2): four sources + win
  | exp2A | exp2B | exp2C | exp2D | exp2Win
  deriving DecidableEq, Fintype, Repr

/-- The shared causal graph for both experiments. -/
def konukGraph : CausalGraph KonukVar :=
  ⟨fun
    | .urnA | .urnB | .urnC => ∅
    | .win => {.urnA, .urnB, .urnC}
    | .exp2A | .exp2B | .exp2C | .exp2D => ∅
    | .exp2Win => {.exp2A, .exp2B, .exp2C, .exp2D}⟩

/-- Threshold-≥-2 mechanism: WIN iff at least 2 of {urnA, urnB, urnC} true.
    Equivalent to (A∧B) ∨ (A∧C) ∨ (B∧C). -/
private def thresholdMech
    (ρ : ∀ u : konukGraph.parents .win, Bool) : Bool :=
  let a := ρ ⟨.urnA, by simp [konukGraph]⟩
  let b := ρ ⟨.urnB, by simp [konukGraph]⟩
  let c := ρ ⟨.urnC, by simp [konukGraph]⟩
  (a && b) || (a && c) || (b && c)

/-- Disjunctive-rule mechanism: WIN iff (A∧B) ∨ (C∧D). -/
private def disjunctiveRuleMech
    (ρ : ∀ u : konukGraph.parents .exp2Win, Bool) : Bool :=
  let a := ρ ⟨.exp2A, by simp [konukGraph]⟩
  let b := ρ ⟨.exp2B, by simp [konukGraph]⟩
  let c := ρ ⟨.exp2C, by simp [konukGraph]⟩
  let d := ρ ⟨.exp2D, by simp [konukGraph]⟩
  (a && b) || (c && d)

/-- The shared BoolSEM for both Konuk experiments. -/
noncomputable def konukSEM : BoolSEM KonukVar :=
  { graph := konukGraph
    mech := fun v => match v with
      | .urnA | .urnB | .urnC => const (G := konukGraph) false
      | .win => deterministic thresholdMech
      | .exp2A | .exp2B | .exp2C | .exp2D => const (G := konukGraph) false
      | .exp2Win => deterministic disjunctiveRuleMech }

noncomputable instance : SEM.IsDeterministic konukSEM where
  mech_det v := match v with
    | .urnA | .urnB | .urnC | .exp2A | .exp2B | .exp2C | .exp2D =>
      inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .win | .exp2Win =>
      inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Topologically-ordered vertex list (roots before win-vertices). -/
def konukVarList : List KonukVar :=
  [.urnA, .urnB, .urnC, .exp2A, .exp2B, .exp2C, .exp2D, .win, .exp2Win]

-- ════════════════════════════════════════════════════
-- § Compound sufficiency and necessity (polymorphic)
-- ════════════════════════════════════════════════════

/-- A compound cause is **sufficient** iff setting all its variables to
    true produces the effect under `developOn`. -/
noncomputable def compoundSufficient (M : BoolSEM KonukVar)
    [SEM.IsDeterministic M] (bg : Valuation (fun _ : KonukVar => Bool))
    (causes : List KonukVar) (effect : KonukVar) : Prop :=
  (developOn M konukVarList 1
    (causes.foldl (fun s' v => s'.extend v true) bg)).hasValue effect true

noncomputable instance (M : BoolSEM KonukVar) [SEM.IsDeterministic M]
    (bg : Valuation _) (causes : List KonukVar) (effect : KonukVar) :
    Decidable (compoundSufficient M bg causes effect) :=
  Classical.dec _

/-- A compound cause is **necessary** iff setting all its variables to
    false prevents the effect under `developOn`. -/
noncomputable def compoundNecessary (M : BoolSEM KonukVar)
    [SEM.IsDeterministic M] (bg : Valuation (fun _ : KonukVar => Bool))
    (causes : List KonukVar) (effect : KonukVar) : Prop :=
  ¬ (developOn M konukVarList 1
    (causes.foldl (fun s' v => s'.extend v false) bg)).hasValue effect true

noncomputable instance (M : BoolSEM KonukVar) [SEM.IsDeterministic M]
    (bg : Valuation _) (causes : List KonukVar) (effect : KonukVar) :
    Decidable (compoundNecessary M bg causes effect) :=
  Classical.dec _

-- ════════════════════════════════════════════════════
-- § 3. Experiment 1: Threshold Game
-- ════════════════════════════════════════════════════

/-- The actual situation: all three urns are on. -/
private def thresholdActual : Valuation (fun _ : KonukVar => Bool) :=
  Valuation.empty.extend .urnA true |>.extend .urnB true |>.extend .urnC true

/-- Any pair of urns is sufficient (compound sufficiency). -/
theorem anyPair_sufficient_AB :
    compoundSufficient konukSEM Valuation.empty [.urnA, .urnB] .win := by
  unfold compoundSufficient; rfl

theorem anyPair_sufficient_AC :
    compoundSufficient konukSEM Valuation.empty [.urnA, .urnC] .win := by
  unfold compoundSufficient; rfl

theorem anyPair_sufficient_BC :
    compoundSufficient konukSEM Valuation.empty [.urnB, .urnC] .win := by
  unfold compoundSufficient; rfl

/-- But compound pairs ARE necessary in the actual world.

    Individual urns are not necessary (overdetermination), but compound
    pairs are — removing any pair drops below threshold. This justifies
    treating A∧B as the unit of causal attribution. -/
theorem compound_pair_necessary_in_actual :
    compoundNecessary konukSEM thresholdActual [.urnA, .urnB] .win ∧
    compoundNecessary konukSEM thresholdActual [.urnA, .urnC] .win ∧
    compoundNecessary konukSEM thresholdActual [.urnB, .urnC] .win := by
  refine ⟨?_, ?_, ?_⟩
  all_goals (unfold compoundNecessary; intro h; exact Bool.false_ne_true (Option.some.inj h))

-- ════════════════════════════════════════════════════
-- § NSM Computation for Experiment 1 (unchanged — pure ℚ arithmetic)
-- ════════════════════════════════════════════════════

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
    gives 39/40 vs 21/40, matching the empirical finding. -/
theorem antiLinearity_nsm :
    nsmThreshold pInt pHigh pLow > nsmThreshold pLow pInt pHigh := by
  simp only [nsmThreshold, pInt, pHigh, pLow]; norm_num

-- ════════════════════════════════════════════════════
-- § 4. Experiment 2: Disjunctive Rule and LOSS
-- ════════════════════════════════════════════════════

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
    over the classical reading. -/
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

/-- The loss gap (classical but not strong) is exactly `someSatisfy` for the
    "is present" predicate: some but not all variables are false.

    The classical negation ¬(A∧B) ∧ ¬(C∧D) allows worlds where some
    variables are true and others false. The homogeneous negation
    ¬A∧¬B∧¬C∧¬D requires all false. The gap is the truth-value gap from
    @cite{kriz-spector-2021}. -/
theorem loss_gap_iff_pluralGap :
    ∀ f : Fin 4 → Bool,
    (lossClassical (f 0) (f 1) (f 2) (f 3) = true ∧
     lossStrong (f 0) (f 1) (f 2) (f 3) = false) ↔
    (lossClassical (f 0) (f 1) (f 2) (f 3) = true ∧
     Semantics.Plurality.Distributivity.someSatisfy
       (fun (i : Fin 4) (_ : Unit) => f i) Finset.univ () = true) := by
  decide

-- ════════════════════════════════════════════════════
-- § 5. Experiment 2: Crossing Avoidance
-- ════════════════════════════════════════════════════

/-- Disjunct membership classification for a pair of variables. -/
inductive DisjunctMembership where
  | withinAB
  | withinCD
  | crossDisjunct
  deriving DecidableEq, Repr

/-- Classify a pair of Experiment 2 variables by disjunct membership. -/
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

    A∧B matches a conjunctive law, so setting A=B=1 fires the law and
    produces WIN. But A∧C does not match any single law. -/
theorem structural_crossing_avoidance :
    compoundSufficient konukSEM Valuation.empty [.exp2A, .exp2B] .exp2Win ∧
    compoundSufficient konukSEM Valuation.empty [.exp2C, .exp2D] .exp2Win ∧
    ¬ compoundSufficient konukSEM Valuation.empty [.exp2A, .exp2C] .exp2Win ∧
    ¬ compoundSufficient konukSEM Valuation.empty [.exp2B, .exp2D] .exp2Win := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold compoundSufficient; rfl
  · unfold compoundSufficient; rfl
  · unfold compoundSufficient; intro h; exact Bool.false_ne_true (Option.some.inj h)
  · unfold compoundSufficient; intro h; exact Bool.false_ne_true (Option.some.inj h)

-- ════════════════════════════════════════════════════
-- § Triple-1 / Triple-0 conditions
-- ════════════════════════════════════════════════════

/-- Triple-1 actual world: colored balls from A, B, D; white from C. -/
private def triple1Actual : Valuation (fun _ : KonukVar => Bool) :=
  Valuation.empty.extend .exp2A true |>.extend .exp2B true
    |>.extend .exp2C false |>.extend .exp2D true

/-- In Triple-1, the compound A∧B is both sufficient (in empty bg) and
    necessary (in actual world). -/
theorem triple1_AB_sufficient_and_necessary :
    compoundSufficient konukSEM Valuation.empty [.exp2A, .exp2B] .exp2Win ∧
    compoundNecessary konukSEM triple1Actual [.exp2A, .exp2B] .exp2Win := by
  refine ⟨?_, ?_⟩
  · unfold compoundSufficient; rfl
  · unfold compoundNecessary; intro h; exact Bool.false_ne_true (Option.some.inj h)

/-- Triple-0 actual world: white balls from A, B, D; colored from C. -/
private def triple0Actual : Valuation (fun _ : KonukVar => Bool) :=
  Valuation.empty.extend .exp2A false |>.extend .exp2B false
    |>.extend .exp2C true |>.extend .exp2D false

/-- In Triple-0 (loss), under homogeneous representation LOSS = ¬A∧¬B∧¬D,
    the white ball from D is indispensable. -/
theorem triple0_lossStrong_needs_all :
    lossStrong false false true false = false ∧
    lossStrong false false false false = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. Bridge: LOSS_strong = `noneSatisfy` (Homogeneity)
-- ════════════════════════════════════════════════════

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

/-- LOSS_strong is exactly `noneSatisfy` from @cite{kriz-spector-2021}. -/
theorem lossStrong_eq_noneSatisfy :
    ∀ f : Fin 4 → Bool,
    lossStrong (f 0) (f 1) (f 2) (f 3) =
    Semantics.Plurality.Distributivity.noneSatisfy
      (fun (i : Fin 4) (_ : Unit) => f i) Finset.univ () := by
  decide

end KonukEtAl2026
