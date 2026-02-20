import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Domains.Quantities
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics
import Linglib.Phenomena.ScalarImplicatures.Studies.GoodmanStuhlmuller2013

/-!
# Goodman & Stuhlmuller (2013): Knowledge and Implicature @cite{goodman-stuhlmuller-2013}

Topics in Cognitive Science 5(1): 173-184

Scalar implicature and upper-bounded numeral interpretations are modulated by
speaker knowledge. When the speaker has full access, listeners draw upper-bounded
inferences; when access is partial, these weaken or disappear.

## Architecture

A single `gsCfg` constructor parametric in the meaning function serves both
experiments (quantifiers and lower-bound numerals). They share the same
observation model, speaker belief, and S1 structure — the only thing that varies
is the utterance type and literal semantics.

S1(u | obs) ∝ exp(α · E_belief[log L0(s | u)])

The quality filter (utterances must be true at all believed worlds) is
explicit because `Real.log 0 = 0` in Lean/Mathlib, unlike WebPPL where
`log(0) = -∞` makes quality emerge from the expected utility computation.

## Theorems

The model reproduces all 11 qualitative findings from Experiments 1 and 2.
All proofs use `rsa_predict` on interval-arithmetic bounds.

**Experiment 1** (quantifiers): `gsCfgQ` — quantifier meaning {none, some, all}.

**Experiment 2** (number words): `gsCfgN` — lower-bound numeral meaning
{one, two, three}, where "two" means "at least two".

| # | Finding | Model prediction |
|---|---------|-----------------|
| 1 | some + full → implicature | L1("some", a=3): s2 > s3 |
| 2 | some + a=1 → canceled | L1("some", a=1): NOT (s2 > s3) |
| 3 | some + a=2 → canceled | L1("some", a=2): NOT (s2 > s3) |
| 4 | two + full → upper-bounded | L1("two", a=3): s2 > s3 |
| 5 | two + a=2 → weakened | L1("two", a=2): NOT (s2 > s3) |
| 6 | one + full → s1 > s2 | L1("one", a=3): s1 > s2 |
| 7 | one + full → s1 > s3 | L1("one", a=3): s1 > s3 |
| 8 | one + a=1 → canceled (s2) | L1("one", a=1): NOT (s1 > s2) |
| 9 | one + a=1 → canceled (s3) | L1("one", a=1): NOT (s1 > s3) |
| 10 | one + a=2 → partial (s3) | L1("one", a=2): s1 > s3 |
| 11 | one + a=2 → canceled (s2) | L1("one", a=2): NOT (s1 > s2) |

## References

- Goodman, N.D. & Stuhlmuller, A. (2013). Knowledge and implicature. *TopiCS* 5(1).
- Kennedy, C. (2015). A "de-Fregean" semantics for modified and unmodified numerals.
  *Semantics & Pragmatics* 8(10), 1-44.
-/

set_option autoImplicit false

namespace Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013

open Phenomena.ScalarImplicatures.Studies.GoodmanStuhlmuller2013 (Finding)

-- ============================================================================
-- §1. Domain Types
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
-- §2. Observation Model (Hypergeometric)
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
-- §3. Quality Filter
-- ============================================================================

/-- Quality filter: utterance u must be true at every world the speaker
    considers possible given observation obs. Explicit because `Real.log 0 = 0`
    in Lean; in WebPPL, `log(0) = -∞` makes quality emerge from the score. -/
def qualityOk {U : Type*} (meaning : U → WorldState → Bool)
    (obs : Obs) (u : U) : Bool :=
  [.s0, .s1, .s2, .s3].all fun s => !obsCompatible obs s || meaning u s

-- ============================================================================
-- §4. Unified Config Constructor
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
-- §5. Quantifier Model
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
-- §6. Numeral Model (Lower-Bound Semantics)
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
-- §7. Grounding
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
-- §8. Experiment 1: "some" x access
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
-- §9. Experiment 2: "two" x access
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
-- §10. Experiment 2: "one" x access
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
-- §11. Verification: every finding from the paper is accounted for
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
