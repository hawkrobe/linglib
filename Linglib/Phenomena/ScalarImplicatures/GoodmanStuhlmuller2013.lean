import Linglib.Core.Empirical
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Domains.Quantities
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics

/-!
# Goodman & Stuhlmuller (2013): Knowledge and Implicature @cite{goodman-stuhlmuller-2013}

"Knowledge and Implicature: Modeling Language Understanding as Social Cognition"
Topics in Cognitive Science 5(1): 173-184

## Paradigm

Three objects that may have a property. Speaker observes a subset (access = 1, 2,
or 3) and makes a quantified or numeral statement. Listener divides $100 among
world states (0-3 objects have property). Speaker access is common knowledge.

Trials with knowledgeability bet <= 70 excluded from primary analysis.

## Architecture

A single `gsCfg` constructor parametric in the meaning function serves both
experiments (quantifiers and lower-bound numerals). They share the same
observation model, speaker belief, and S1 structure — the only thing that varies
is the utterance type and literal semantics.

S1(u | obs) ∝ exp(α · E_belief[log L0(s | u)])

The quality filter (utterances must be true at all believed worlds) is
explicit because `Real.log 0 = 0` in Lean/Mathlib, unlike WebPPL where
`log(0) = -∞` makes quality emerge from the expected utility computation.

## Qualitative Findings

The paper's central finding: scalar implicature and upper-bounded numeral
interpretations are modulated by speaker knowledge. When the speaker has full
access, listeners draw upper-bounded inferences; when access is partial, these
inferences weaken or disappear.

| # | Finding | Word | Access | Comparison | Evidence |
|---|---------|------|--------|------------|----------|
| 1 | Implicature present | "some" | 3 | state 2 > state 3 | t(43)=-10.2, p<.001 |
| 2 | Implicature canceled | "some" | 1 | state 2 not > state 3 | t(31)=0.77, p=.78 |
| 3 | Implicature canceled | "some" | 2 | state 2 not > state 3 | t(28)=-0.82, p=.21 |
| 4 | Upper-bounded | "two" | 3 | state 2 > state 3 | t(43)=-10.2, p<.001 |
| 5 | Not upper-bounded | "two" | 2 | state 2 not > state 3 | t(24)=1.1, p=.87 |
| 6 | Upper-bounded | "one" | 3 | state 1 > state 2 | t(42)=-13.1, p<.001 |
| 7 | Upper-bounded | "one" | 3 | state 1 > state 3 | t(42)=-17.1, p<.001 |
| 8 | Not upper-bounded | "one" | 1 | state 1 not > state 2 | t(24)=1.9, p=.96 |
| 9 | Not upper-bounded | "one" | 1 | state 1 not > state 3 | t(24)=3.2, p=1.0 |
| 10 | Partial | "one" | 2 | state 1 > state 3 | t(25)=-3.9, p<.001 |
| 11 | Partial | "one" | 2 | state 1 not > state 2 | t(25)=1.5, p=.92 |

The model reproduces all 11 findings. All proofs use `rsa_predict`.

## References

- Goodman, N.D. & Stuhlmuller, A. (2013). Knowledge and implicature. *TopiCS* 5(1).
- Kennedy, C. (2015). A "de-Fregean" semantics for modified and unmodified numerals.
  *Semantics & Pragmatics* 8(10), 1-44.
-/

set_option autoImplicit false

namespace Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013

open Phenomena

-- ============================================================================
-- §1. Empirical Data
-- ============================================================================

def citation : String :=
  "Goodman & Stuhlmuller (2013). Topics in Cognitive Science 5(1): 173-184."

def measure : MeasureSpec :=
  { scale := .continuous, task := .forcedChoice, unit := "dollars (out of $100)" }

def nPerExperiment : Nat := 50
def nObjects : Nat := 3

/-- The 11 qualitative findings from Goodman & Stuhlmuller (2013) Experiments 1-2.
    Each finding is a pairwise bet comparison between world states under a specific
    (word, access) condition. -/
inductive Finding where
  -- Experiment 1: "some" x speaker access (Fig 2A)
  /-- Full access: bets on state 2 > state 3 (scalar implicature present).
      Evidence: t(43) = -10.2, p < .001. -/
  | some_full_implicature
  /-- Minimal access (a=1): state 2 does not exceed state 3 (canceled).
      Evidence: t(31) = 0.77, p = .78. -/
  | some_minimal_canceled
  /-- Partial access (a=2): state 2 does not exceed state 3 (canceled).
      Evidence: t(28) = -0.82, p = .21. -/
  | some_partial_canceled
  -- Experiment 2: "two" x speaker access (Fig 2B)
  /-- Full access: "two" -> state 2 > state 3 (upper-bounded reading).
      Evidence: t(43) = -10.2, p < .001. -/
  | two_full_upper_bounded
  /-- Partial access (a=2): state 2 does not exceed state 3 (weakened).
      Evidence: t(24) = 1.1, p = .87. -/
  | two_partial_weakened
  -- Experiment 2: "one" x speaker access (Fig 2B)
  /-- Full access: "one" -> state 1 > state 2.
      Evidence: t(42) = -13.1, p < .001. -/
  | one_full_1v2
  /-- Full access: "one" -> state 1 > state 3.
      Evidence: t(42) = -17.1, p < .001. -/
  | one_full_1v3
  /-- Minimal access (a=1): state 1 does not exceed state 2 (canceled).
      Evidence: t(24) = 1.9, p = .96. -/
  | one_minimal_1v2_canceled
  /-- Minimal access (a=1): state 1 does not exceed state 3 (canceled).
      Evidence: t(24) = 3.2, p = 1.0. -/
  | one_minimal_1v3_canceled
  /-- Partial access (a=2): state 1 > state 3 (partial implicature holds).
      Evidence: t(25) = -3.9, p < .001. -/
  | one_partial_1v3
  /-- Partial access (a=2): state 1 does not exceed state 2 (still canceled).
      Evidence: t(25) = 1.5, p = .92. -/
  | one_partial_1v2_canceled
  deriving DecidableEq, BEq, Repr

/-- All findings from the paper. -/
def findings : List Finding :=
  [.some_full_implicature, .some_minimal_canceled, .some_partial_canceled,
   .two_full_upper_bounded, .two_partial_weakened,
   .one_full_1v2, .one_full_1v3,
   .one_minimal_1v2_canceled, .one_minimal_1v3_canceled,
   .one_partial_1v3, .one_partial_1v2_canceled]

-- ============================================================================
-- §2. Statistical Evidence
-- ============================================================================

/-- A pairwise comparison of bets on two world states in a condition.

The key observable: did participants allocate significantly more money to
world state `stateA` than to `stateB`? A theory that predicts the listener's
posterior P(state | word, access) can be checked against this. -/
structure BetComparison where
  experiment : Nat
  word : String
  /-- How many of 3 objects the speaker observed -/
  access : Nat
  stateA : Nat
  stateB : Nat
  /-- Did bets on stateA significantly exceed bets on stateB? -/
  aExceedsB : Bool
  evidence : String
  deriving Repr

-- Experiment 1: "some" x access (N = 50)

/-- Access = 3: bets on state 2 > bets on state 3. -/
def exp1_some_a3_2v3 : BetComparison :=
  { experiment := 1, word := "some", access := 3, stateA := 2, stateB := 3
    aExceedsB := true, evidence := "t(43) = -10.2, p < .001" }

/-- Access = 1: bets on state 2 did NOT exceed bets on state 3. -/
def exp1_some_a1_2v3 : BetComparison :=
  { experiment := 1, word := "some", access := 1, stateA := 2, stateB := 3
    aExceedsB := false, evidence := "t(31) = 0.77, p = .78" }

/-- Access = 2: bets on state 2 did NOT exceed bets on state 3. -/
def exp1_some_a2_2v3 : BetComparison :=
  { experiment := 1, word := "some", access := 2, stateA := 2, stateB := 3
    aExceedsB := false, evidence := "t(28) = -0.82, p = .21" }

/-- Bets on state 3 at access = 3 significantly lower than at access = 1. -/
def exp1_a3_vs_a1_on_state3 : BetComparison :=
  { experiment := 1, word := "some", access := 3, stateA := 3, stateB := 3
    aExceedsB := false
    evidence := "access 3 < access 1 on state 3: t(47) = -4.0, p < .001" }

-- Experiment 2: number words x access (N = 50)

/-- "two", access = 3: bets on state 2 > bets on state 3. -/
def exp2_two_a3_2v3 : BetComparison :=
  { experiment := 2, word := "two", access := 3, stateA := 2, stateB := 3
    aExceedsB := true, evidence := "t(43) = -10.2, p < .001" }

/-- "two", access = 2: bets on state 2 did NOT exceed bets on state 3. -/
def exp2_two_a2_2v3 : BetComparison :=
  { experiment := 2, word := "two", access := 2, stateA := 2, stateB := 3
    aExceedsB := false, evidence := "t(24) = 1.1, p = .87" }

/-- "one", access = 3: bets on state 1 > bets on state 2. -/
def exp2_one_a3_1v2 : BetComparison :=
  { experiment := 2, word := "one", access := 3, stateA := 1, stateB := 2
    aExceedsB := true, evidence := "t(42) = -13.1, p < .001" }

/-- "one", access = 3: bets on state 1 > bets on state 3. -/
def exp2_one_a3_1v3 : BetComparison :=
  { experiment := 2, word := "one", access := 3, stateA := 1, stateB := 3
    aExceedsB := true, evidence := "t(42) = -17.1, p < .001" }

/-- "one", access = 1: bets on state 1 did NOT exceed bets on state 2. -/
def exp2_one_a1_1v2 : BetComparison :=
  { experiment := 2, word := "one", access := 1, stateA := 1, stateB := 2
    aExceedsB := false, evidence := "t(24) = 1.9, p = .96" }

/-- "one", access = 1: bets on state 1 did NOT exceed bets on state 3. -/
def exp2_one_a1_1v3 : BetComparison :=
  { experiment := 2, word := "one", access := 1, stateA := 1, stateB := 3
    aExceedsB := false, evidence := "t(24) = 3.2, p = 1.0" }

/-- "one", access = 2: bets on state 1 > bets on state 3 (partial). -/
def exp2_one_a2_1v3 : BetComparison :=
  { experiment := 2, word := "one", access := 2, stateA := 1, stateB := 3
    aExceedsB := true, evidence := "t(25) = -3.9, p < .001" }

/-- "one", access = 2: bets on state 1 did NOT exceed bets on state 2. -/
def exp2_one_a2_1v2 : BetComparison :=
  { experiment := 2, word := "one", access := 2, stateA := 1, stateB := 2
    aExceedsB := false, evidence := "t(25) = 1.5, p = .92" }

-- Omnibus effects

structure OmnibusTest where
  description : String
  testType : String
  statistic : Float
  p : Float
  deriving Repr

def exp1_access_effect : OmnibusTest :=
  { description := "Effect of access on bets on state 3"
    testType := "one-way ANOVA, F(2, 102)", statistic := 10.18, p := 0.001 }

def exp2_access_main : OmnibusTest :=
  { description := "Main effect of access"
    testType := "ANOVA, F(2, 205)", statistic := 6.57, p := 0.01 }

def exp2_word_main : OmnibusTest :=
  { description := "Main effect of word"
    testType := "ANOVA, F(2, 205)", statistic := 269.8, p := 0.001 }

def exp2_interaction : OmnibusTest :=
  { description := "Word x access interaction"
    testType := "ANOVA, F(1, 205)", statistic := 34.7, p := 0.001 }

-- Manipulation check

structure KnowledgeabilityCheck where
  access : Nat
  meanBet : Float
  sd : Float
  deriving Repr

def knowledge_a1 : KnowledgeabilityCheck := { access := 1, meanBet := 27.1, sd := 4.9 }
def knowledge_a2 : KnowledgeabilityCheck := { access := 2, meanBet := 34.8, sd := 5.7 }
def knowledge_a3 : KnowledgeabilityCheck := { access := 3, meanBet := 93.0, sd := 2.7 }

-- Finding → Evidence linking

/-- The statistical evidence for each finding. -/
def Finding.evidence : Finding → BetComparison
  | .some_full_implicature => exp1_some_a3_2v3
  | .some_minimal_canceled => exp1_some_a1_2v3
  | .some_partial_canceled => exp1_some_a2_2v3
  | .two_full_upper_bounded => exp2_two_a3_2v3
  | .two_partial_weakened => exp2_two_a2_2v3
  | .one_full_1v2 => exp2_one_a3_1v2
  | .one_full_1v3 => exp2_one_a3_1v3
  | .one_minimal_1v2_canceled => exp2_one_a1_1v2
  | .one_minimal_1v3_canceled => exp2_one_a1_1v3
  | .one_partial_1v3 => exp2_one_a2_1v3
  | .one_partial_1v2_canceled => exp2_one_a2_1v2

/-- Does this finding predict that the comparison holds (stateA > stateB)? -/
def Finding.predicted : Finding → Bool
  | .some_full_implicature | .two_full_upper_bounded
  | .one_full_1v2 | .one_full_1v3 | .one_partial_1v3 => true
  | _ => false

/-- The statistical evidence matches the predicted direction for every finding. -/
theorem evidence_matches_prediction :
    ∀ f : Finding, f.evidence.aExceedsB = f.predicted := by
  intro f; cases f <;> rfl

-- ============================================================================
-- §3. Domain Types
-- ============================================================================

/-- World states: how many of 3 objects have the property. -/
inductive WorldState where
  | s0 | s1 | s2 | s3
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

def WorldState.toNat : WorldState → Nat
  | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3

/-- Speaker access: how many of 3 objects the speaker can observe. -/
inductive Access where
  | a1 | a2 | a3
  deriving DecidableEq, BEq, Repr

/-- Observations: (number seen with property, access level).
    Latent variable in L1 — L1 marginalizes over observations. -/
inductive Obs where
  | o0a1 | o1a1                      -- access=1: saw 0 or 1
  | o0a2 | o1a2 | o2a2              -- access=2: saw 0, 1, or 2
  | o0a3 | o1a3 | o2a3 | o3a3      -- access=3: saw 0, 1, 2, or 3
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

def Obs.access : Obs → Access
  | .o0a1 | .o1a1 => .a1
  | .o0a2 | .o1a2 | .o2a2 => .a2
  | .o0a3 | .o1a3 | .o2a3 | .o3a3 => .a3

/-- Number of objects with the property in the sample. -/
def Obs.count : Obs → Nat
  | .o0a1 | .o0a2 | .o0a3 => 0
  | .o1a1 | .o1a2 | .o1a3 => 1
  | .o2a2 | .o2a3 => 2
  | .o3a3 => 3

/-- Sample size (= access level as ℕ). -/
def Obs.sampleSize : Obs → Nat
  | .o0a1 | .o1a1 => 1
  | .o0a2 | .o1a2 | .o2a2 => 2
  | .o0a3 | .o1a3 | .o2a3 | .o3a3 => 3

-- ============================================================================
-- §4. Observation Model (Hypergeometric)
-- ============================================================================

/-- Hypergeometric feasibility: can you draw `obs.count` successes when
    sampling `obs.sampleSize` from a population of 3 with `s.toNat` successes?
    True iff C(K, k) > 0 and C(3−K, n−k) > 0, i.e. `k ≤ K` and `n−k ≤ 3−K`.
    Derived from the combinatorial constraint rather than stipulated. -/
def obsCompatible (obs : Obs) (s : WorldState) : Bool :=
  obs.count ≤ s.toNat && obs.sampleSize - obs.count ≤ 3 - s.toNat

/-- P(obs | access, world). Hypergeometric probability of observing k successes
    when sampling n from 3 total with K successes:
    P(k | N=3, K, n) = C(K,k) · C(3−K, n−k) / C(3,n).
    Defined as a match table for `extractRat` compatibility. -/
noncomputable def obsPriorTable (a : Access) (w : WorldState) (obs : Obs) : ℝ :=
  if obs.access != a then 0 else
  match a, w, obs with
  -- access=1: C(K,k) · C(3-K,1-k) / C(3,1)
  | .a1, .s0, .o0a1 => 1     | .a1, .s0, .o1a1 => 0
  | .a1, .s1, .o0a1 => 2/3   | .a1, .s1, .o1a1 => 1/3
  | .a1, .s2, .o0a1 => 1/3   | .a1, .s2, .o1a1 => 2/3
  | .a1, .s3, .o0a1 => 0     | .a1, .s3, .o1a1 => 1
  -- access=2: C(K,k) · C(3-K,2-k) / C(3,2)
  | .a2, .s0, .o0a2 => 1     | .a2, .s0, .o1a2 => 0     | .a2, .s0, .o2a2 => 0
  | .a2, .s1, .o0a2 => 1/3   | .a2, .s1, .o1a2 => 2/3   | .a2, .s1, .o2a2 => 0
  | .a2, .s2, .o0a2 => 0     | .a2, .s2, .o1a2 => 2/3   | .a2, .s2, .o2a2 => 1/3
  | .a2, .s3, .o0a2 => 0     | .a2, .s3, .o1a2 => 0     | .a2, .s3, .o2a2 => 1
  -- access=3: deterministic (full knowledge)
  | .a3, .s0, .o0a3 => 1     | .a3, .s1, .o1a3 => 1
  | .a3, .s2, .o2a3 => 1     | .a3, .s3, .o3a3 => 1
  | _, _, _ => 0

/-- Speaker's posterior over world states given observation:
    P(state | obs) ∝ P(obs | state, access) · P(state).
    With uniform world prior, this is the normalized hypergeometric.
    The access level is derived from the observation itself. -/
noncomputable def speakerBelief (obs : Obs) (s : WorldState) : ℝ :=
  obsPriorTable obs.access s obs / ∑ s' : WorldState, obsPriorTable obs.access s' obs

-- ============================================================================
-- §5. Quality Filter
-- ============================================================================

/-- Quality filter: utterance u must be true at every world the speaker
    considers possible given observation obs. Explicit because `Real.log 0 = 0`
    in Lean; in WebPPL, `log(0) = -∞` makes quality emerge from the score. -/
def qualityOk {U : Type*} (meaning : U → WorldState → Bool)
    (obs : Obs) (u : U) : Bool :=
  [.s0, .s1, .s2, .s3].all fun s => !obsCompatible obs s || meaning u s

-- ============================================================================
-- §6. RSA Config
-- ============================================================================

open RSA in
/-- GS2013 model parametric in utterance type and meaning function.

    Both experiments (quantifiers, numerals) share identical S1 structure:

        S1(u | obs) ∝ exp(α · Σ_s belief(obs, s) · log L0(s | u))

    The speaker optimizes expected log-informativity under their belief state.
    The quality filter ensures the speaker only considers utterances true at all
    worlds they consider possible.

    The `_w` parameter in `s1Score` is unused: the speaker's utility depends on
    the observation (latent variable), not the world directly. S1 is indexed by
    observation, and L1 marginalizes over observations weighted by the
    hypergeometric prior. -/
noncomputable def gsCfg {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool) (a : Access) : RSAConfig U WorldState where
  Latent := Obs
  meaning _obs u w := if meaning u w then 1 else 0
  meaning_nonneg _ _ _ := by split <;> positivity
  s1Score l0 α obs _w u :=
    if qualityOk meaning obs u then
      Real.exp (α * ∑ s : WorldState, speakerBelief obs s * Real.log (l0 u s))
    else 0
  s1Score_nonneg _ _ _ _ _ _ _ := by
    split
    · exact le_of_lt (Real.exp_pos _)
    · exact le_refl 0
  α := 1
  α_pos := one_pos
  latentPrior w obs := obsPriorTable a w obs
  latentPrior_nonneg w obs := by
    unfold obsPriorTable
    split
    · exact le_refl 0
    · (repeat' split) <;> positivity
  worldPrior_nonneg _ := by positivity

-- ============================================================================
-- §7. Quantifier Model
-- ============================================================================

inductive QUtt where
  | none_ | some_ | all
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

def qMeaning : QUtt → WorldState → Bool
  | .none_, s => s.toNat == 0
  | .some_, s => s.toNat ≥ 1
  | .all,   s => s.toNat == 3

/-- Quantifier RSA model: {none, some, all} × speaker access. -/
noncomputable abbrev gsCfgQ := gsCfg qMeaning

-- ============================================================================
-- §8. Numeral Model (Lower-Bound Semantics)
-- ============================================================================

inductive NumUtt where
  | one | two | three
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

def lbMeaning : NumUtt → WorldState → Bool
  | .one,   s => s.toNat ≥ 1
  | .two,   s => s.toNat ≥ 2
  | .three, s => s.toNat ≥ 3

/-- Lower-bound numeral RSA model: {one, two, three} × speaker access. -/
noncomputable abbrev gsCfgN := gsCfg lbMeaning

-- ============================================================================
-- §9. Grounding
-- ============================================================================

/-- Quantifier meaning derives from Montague semantics (not stipulated). -/
theorem quantifier_meaning_grounded (u : QUtt) (s : WorldState) :
    qMeaning u s =
    RSA.Domains.Quantity.meaning 3
      (match u with | .none_ => .none_ | .some_ => .some_ | .all => .all)
      ⟨s.toNat, by cases u <;> cases s <;> decide⟩ := by
  cases u <;> cases s <;> native_decide

/-- Lower-bound numeral meaning derives from NumeralTheory.meaning. -/
theorem lb_meaning_grounded (u : NumUtt) (s : WorldState) :
    lbMeaning u s =
    Semantics.Lexical.Numeral.LowerBound.meaning
      (match u with | .one => .one | .two => .two | .three => .three)
      s.toNat := by
  cases u <;> cases s <;> rfl

-- ============================================================================
-- §10. Experiment 1: "some" x access
-- ============================================================================

set_option maxHeartbeats 4000000 in
/-- Full access: L1 infers state 2 over state 3 — scalar implicature present. -/
theorem some_full_implicature :
    (gsCfgQ .a3).L1 .some_ .s2 > (gsCfgQ .a3).L1 .some_ .s3 := by
  rsa_predict

set_option maxHeartbeats 4000000 in
/-- Minimal access (a=1): implicature canceled — state 2 does not exceed state 3. -/
theorem some_minimal_canceled :
    ¬((gsCfgQ .a1).L1 .some_ .s2 > (gsCfgQ .a1).L1 .some_ .s3) := by
  rsa_predict

set_option maxHeartbeats 4000000 in
/-- Partial access (a=2): implicature canceled — state 2 does not exceed state 3. -/
theorem some_partial_canceled :
    ¬((gsCfgQ .a2).L1 .some_ .s2 > (gsCfgQ .a2).L1 .some_ .s3) := by
  rsa_predict

-- ============================================================================
-- §11. Experiment 2: "two" x access
-- ============================================================================

set_option maxHeartbeats 4000000 in
/-- Full access: "two" → upper-bounded reading, state 2 > state 3. -/
theorem two_full_upper_bounded :
    (gsCfgN .a3).L1 .two .s2 > (gsCfgN .a3).L1 .two .s3 := by
  rsa_predict

set_option maxHeartbeats 4000000 in
/-- Partial access (a=2): upper bound weakened — state 2 does not exceed state 3. -/
theorem two_partial_weakened :
    ¬((gsCfgN .a2).L1 .two .s2 > (gsCfgN .a2).L1 .two .s3) := by
  rsa_predict

-- ============================================================================
-- §12. Experiment 2: "one" x access
-- ============================================================================

set_option maxHeartbeats 4000000 in
/-- Full access: "one" → state 1 preferred over state 2. -/
theorem one_full_1v2 :
    (gsCfgN .a3).L1 .one .s1 > (gsCfgN .a3).L1 .one .s2 := by
  rsa_predict

set_option maxHeartbeats 4000000 in
/-- Full access: "one" → state 1 preferred over state 3. -/
theorem one_full_1v3 :
    (gsCfgN .a3).L1 .one .s1 > (gsCfgN .a3).L1 .one .s3 := by
  rsa_predict

set_option maxHeartbeats 4000000 in
/-- Minimal access (a=1): canceled — state 1 does not exceed state 2. -/
theorem one_minimal_1v2_canceled :
    ¬((gsCfgN .a1).L1 .one .s1 > (gsCfgN .a1).L1 .one .s2) := by
  rsa_predict

set_option maxHeartbeats 4000000 in
/-- Minimal access (a=1): canceled — state 1 does not exceed state 3. -/
theorem one_minimal_1v3_canceled :
    ¬((gsCfgN .a1).L1 .one .s1 > (gsCfgN .a1).L1 .one .s3) := by
  rsa_predict

set_option maxHeartbeats 4000000 in
/-- Partial access (a=2): state 1 > state 3 (partial implicature persists). -/
theorem one_partial_1v3 :
    (gsCfgN .a2).L1 .one .s1 > (gsCfgN .a2).L1 .one .s3 := by
  rsa_predict

set_option maxHeartbeats 4000000 in
/-- Partial access (a=2): state 1 does not exceed state 2 (still canceled). -/
theorem one_partial_1v2_canceled :
    ¬((gsCfgN .a2).L1 .one .s1 > (gsCfgN .a2).L1 .one .s2) := by
  rsa_predict

-- ============================================================================
-- §13. Verification: every finding is accounted for
-- ============================================================================

/-- Map each empirical finding to the RSA model prediction that accounts for it. -/
def formalize : Finding → Prop
  | .some_full_implicature =>
      (gsCfgQ .a3).L1 .some_ .s2 > (gsCfgQ .a3).L1 .some_ .s3
  | .some_minimal_canceled =>
      ¬((gsCfgQ .a1).L1 .some_ .s2 > (gsCfgQ .a1).L1 .some_ .s3)
  | .some_partial_canceled =>
      ¬((gsCfgQ .a2).L1 .some_ .s2 > (gsCfgQ .a2).L1 .some_ .s3)
  | .two_full_upper_bounded =>
      (gsCfgN .a3).L1 .two .s2 > (gsCfgN .a3).L1 .two .s3
  | .two_partial_weakened =>
      ¬((gsCfgN .a2).L1 .two .s2 > (gsCfgN .a2).L1 .two .s3)
  | .one_full_1v2 =>
      (gsCfgN .a3).L1 .one .s1 > (gsCfgN .a3).L1 .one .s2
  | .one_full_1v3 =>
      (gsCfgN .a3).L1 .one .s1 > (gsCfgN .a3).L1 .one .s3
  | .one_minimal_1v2_canceled =>
      ¬((gsCfgN .a1).L1 .one .s1 > (gsCfgN .a1).L1 .one .s2)
  | .one_minimal_1v3_canceled =>
      ¬((gsCfgN .a1).L1 .one .s1 > (gsCfgN .a1).L1 .one .s3)
  | .one_partial_1v3 =>
      (gsCfgN .a2).L1 .one .s1 > (gsCfgN .a2).L1 .one .s3
  | .one_partial_1v2_canceled =>
      ¬((gsCfgN .a2).L1 .one .s1 > (gsCfgN .a2).L1 .one .s2)

/-- The RSA model accounts for all 11 empirical findings from G&S (2013). -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact some_full_implicature
  · exact some_minimal_canceled
  · exact some_partial_canceled
  · exact two_full_upper_bounded
  · exact two_partial_weakened
  · exact one_full_1v2
  · exact one_full_1v3
  · exact one_minimal_1v2_canceled
  · exact one_minimal_1v3_canceled
  · exact one_partial_1v3
  · exact one_partial_1v2_canceled

end Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013
