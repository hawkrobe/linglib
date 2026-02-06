/-
# Causative Verb Acceptability Data (Cao, White & Lassiter 2025)

Experimental data from a tic-tac-toe-based judgment study of
*cause*, *make*, and *force* in periphrastic causative constructions.

## Design

- 30 stimuli: 3-frame tic-tac-toe sequences with varying ALT, INT, SUF
- 109 participants (90 after exclusions), Prolific, US/UK English speakers
- Binary forced-choice: "Accurate" / "Inaccurate" for sentences like
  "Player X {caused/made/forced} Player O to place at location N"

## References

- Cao, A., White, A. S. & Lassiter, D. (2025). Cause, make, and force
  as graded causatives. Proceedings of ELM 3, 88-103.
-/

namespace Phenomena.Causatives

/-! ## Overall Acceptance Rates (Figure 4)

Proportion of "Yes" (Accurate) responses by verb.
Ordering: caused > made > forced.

Rates stored as percentages (Nat) to avoid heavy Mathlib imports. -/

/-- An experimental observation: verb form paired with acceptance rate (%). -/
structure AcceptanceRate where
  verb : String
  ratePct : Nat      -- Proportion of "Yes" responses (percentage)
  deriving Repr, DecidableEq, BEq

def causedRate : AcceptanceRate := { verb := "caused", ratePct := 48 }
def madeRate : AcceptanceRate := { verb := "made", ratePct := 40 }
def forcedRate : AcceptanceRate := { verb := "forced", ratePct := 35 }

/-- Acceptance ordering: *caused* > *made* > *forced* (Figure 4). -/
theorem acceptance_ordering :
    causedRate.ratePct > madeRate.ratePct ∧
    madeRate.ratePct > forcedRate.ratePct := by decide

/-! ## Main Effect Coefficients (Model I, Table 2)

Bayesian logistic regression with verb × SUFresidALT × INT × ALT.

Coefficients stored as (numerator, denominator=100) to avoid ℚ imports. -/

/-- A regression coefficient with its 95% credible interval.
Values are × 100 (e.g., 119 means 1.19). -/
structure Coefficient where
  name : String
  estimate100 : Int   -- Estimate × 100
  lowerCI100 : Int    -- Lower 95% CI × 100
  upperCI100 : Int    -- Upper 95% CI × 100
  deriving Repr, DecidableEq, BEq

/-- A coefficient is reliable when its 95% CI excludes 0. -/
def Coefficient.isReliable (c : Coefficient) : Bool :=
  (c.lowerCI100 > 0 && c.upperCI100 > 0) || (c.lowerCI100 < 0 && c.upperCI100 < 0)

def coeff_sufResidAlt : Coefficient :=
  { name := "SUFresidALT", estimate100 := 119, lowerCI100 := 89, upperCI100 := 150 }

def coeff_int : Coefficient :=
  { name := "INT", estimate100 := 54, lowerCI100 := 28, upperCI100 := 81 }

def coeff_alt : Coefficient :=
  { name := "ALT", estimate100 := -82, lowerCI100 := -111, upperCI100 := -55 }

theorem suf_reliable : coeff_sufResidAlt.isReliable = true := by native_decide
theorem int_reliable : coeff_int.isReliable = true := by native_decide
theorem alt_reliable : coeff_alt.isReliable = true := by native_decide

/-- SUF has the largest absolute main effect. -/
theorem suf_largest_main_effect :
    coeff_sufResidAlt.estimate100 > coeff_int.estimate100 ∧
    coeff_sufResidAlt.estimate100 > -coeff_alt.estimate100 := by decide

/-- ALT has a negative main effect (more alternatives → less acceptable). -/
theorem alt_negative : coeff_alt.estimate100 < 0 := by decide

/-! ## Per-Verb Interaction Reliability (Table 1)

Estimates of interaction intercepts by verb. Light grey = unreliable. -/

/-- Per-verb reliable interaction from Table 1.
    `positive` = reliable positive effect. -/
structure VerbInteraction where
  verb : String
  interaction : String
  positive : Bool   -- CI entirely above 0
  deriving Repr

/-- *made* uniquely has a reliable SUFresidALT×INT interaction (Table 1). -/
def made_sufInt : VerbInteraction :=
  { verb := "made", interaction := "SUFresidALT:INT", positive := true }

/-- All verbs share reliable SUFresidALT×ALT interaction. -/
def caused_sufAlt : VerbInteraction :=
  { verb := "caused", interaction := "SUFresidALT:ALT", positive := true }
def made_sufAlt : VerbInteraction :=
  { verb := "made", interaction := "SUFresidALT:ALT", positive := true }
def forced_sufAlt : VerbInteraction :=
  { verb := "forced", interaction := "SUFresidALT:ALT", positive := true }

/-- All verbs share reliable INT×ALT interaction. -/
def caused_intAlt : VerbInteraction :=
  { verb := "caused", interaction := "INT:ALT", positive := true }
def made_intAlt : VerbInteraction :=
  { verb := "made", interaction := "INT:ALT", positive := true }
def forced_intAlt : VerbInteraction :=
  { verb := "forced", interaction := "INT:ALT", positive := true }

/-! ## Acceptability Contrasts (examples 3-7)

From the paper's examples showing non-interchangeability. -/

/-- Acceptability judgment for a causative verb in context. -/
inductive Acceptability where
  | acceptable       -- ✓
  | marginal         -- ?
  | unacceptable     -- *
  deriving DecidableEq, Repr, BEq

/-- A single acceptability judgment: verb + context + status. -/
structure CausativeJudgment where
  verb : String
  context : String
  judgment : Acceptability
  source : String  -- Paper example number
  deriving Repr

/-- Example (5): mentioning a habit (low sufficiency, low intention). -/
def ex5a : CausativeJudgment :=
  { verb := "caused", context := "go to gym by mentioning how habit helped"
  , judgment := .acceptable, source := "ex. 5a" }
def ex5b : CausativeJudgment :=
  { verb := "made", context := "go to gym by mentioning how habit helped"
  , judgment := .unacceptable, source := "ex. 5b" }
def ex5c : CausativeJudgment :=
  { verb := "forced", context := "go to gym by mentioning how habit helped"
  , judgment := .unacceptable, source := "ex. 5c" }

/-- Example (7): holding child hostage (high sufficiency, high intention, low alternatives). -/
def ex7a : CausativeJudgment :=
  { verb := "caused", context := "go to gym by holding child hostage"
  , judgment := .acceptable, source := "ex. 7a" }
def ex7b : CausativeJudgment :=
  { verb := "made", context := "go to gym by holding child hostage"
  , judgment := .acceptable, source := "ex. 7b" }
def ex7c : CausativeJudgment :=
  { verb := "forced", context := "go to gym by holding child hostage"
  , judgment := .acceptable, source := "ex. 7c" }

/-- In high-SUF, high-INT, low-ALT contexts, all three verbs are acceptable. -/
theorem all_acceptable_high_suf_int_low_alt :
    ex7a.judgment = .acceptable ∧
    ex7b.judgment = .acceptable ∧
    ex7c.judgment = .acceptable := by decide

/-- In low-SUF contexts, only *cause* is acceptable. -/
theorem only_cause_low_suf :
    ex5a.judgment = .acceptable ∧
    ex5b.judgment = .unacceptable ∧
    ex5c.judgment = .unacceptable := by decide

end Phenomena.Causatives
