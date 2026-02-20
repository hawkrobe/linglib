import Linglib.Theories.Pragmatics.RSA.Implementations.GoodmanStuhlmuller2013
import Linglib.Phenomena.ScalarImplicatures.Studies.GoodmanStuhlmuller2013

/-!
# Goodman & Stuhlmuller (2013) — RSA Bridge @cite{goodman-stuhlmuller-2013}

Bridge theorems verifying that the knowledge-sensitive RSA model reproduces the
qualitative findings from Experiments 1 and 2.

The model uses a quality-filtered S1 speaker (G&S Eq. 2-3) that can only utter
sentences true at every world consistent with its observations. L1 marginalizes
over observations to infer world states. All proofs are by `native_decide` on
rational arithmetic.

**Experiment 1** (quantifiers): `l1q` — L1 with quantifier meaning {none, some, all}.

**Experiment 2** (number words): `l1_lb` — L1 with lower-bound numeral meaning
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
-/

set_option autoImplicit false

namespace Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013Bridge

open RSA.GoodmanStuhlmuller2013
open RSA.GoodmanStuhlmuller2013.KnowledgeState
open Phenomena.ScalarImplicatures.Studies.GoodmanStuhlmuller2013 (Finding)

-- ============================================================================
-- Experiment 1: "some" x access
-- ============================================================================

/-- Full access: L1 infers state 2 over state 3 — scalar implicature present. -/
theorem some_full_implicature :
    getScore (l1q .some_ .a3) .s2 > getScore (l1q .some_ .a3) .s3 := by
  native_decide

/-- Minimal access (a=1): implicature canceled — state 2 does not exceed state 3. -/
theorem some_minimal_canceled :
    ¬(getScore (l1q .some_ .a1) .s2 > getScore (l1q .some_ .a1) .s3) := by
  native_decide

/-- Partial access (a=2): implicature canceled — state 2 does not exceed state 3. -/
theorem some_partial_canceled :
    ¬(getScore (l1q .some_ .a2) .s2 > getScore (l1q .some_ .a2) .s3) := by
  native_decide

-- ============================================================================
-- Experiment 2: "two" x access
-- ============================================================================

/-- Full access: "two" → upper-bounded reading, state 2 > state 3. -/
theorem two_full_upper_bounded :
    getScore (l1_lb .two .a3) .s2 > getScore (l1_lb .two .a3) .s3 := by
  native_decide

/-- Partial access (a=2): upper bound weakened — state 2 does not exceed state 3. -/
theorem two_partial_weakened :
    ¬(getScore (l1_lb .two .a2) .s2 > getScore (l1_lb .two .a2) .s3) := by
  native_decide

-- ============================================================================
-- Experiment 2: "one" x access
-- ============================================================================

/-- Full access: "one" → state 1 preferred over state 2. -/
theorem one_full_1v2 :
    getScore (l1_lb .one .a3) .s1 > getScore (l1_lb .one .a3) .s2 := by
  native_decide

/-- Full access: "one" → state 1 preferred over state 3. -/
theorem one_full_1v3 :
    getScore (l1_lb .one .a3) .s1 > getScore (l1_lb .one .a3) .s3 := by
  native_decide

/-- Minimal access (a=1): canceled — state 1 does not exceed state 2. -/
theorem one_minimal_1v2_canceled :
    ¬(getScore (l1_lb .one .a1) .s1 > getScore (l1_lb .one .a1) .s2) := by
  native_decide

/-- Minimal access (a=1): canceled — state 1 does not exceed state 3. -/
theorem one_minimal_1v3_canceled :
    ¬(getScore (l1_lb .one .a1) .s1 > getScore (l1_lb .one .a1) .s3) := by
  native_decide

/-- Partial access (a=2): state 1 > state 3 (partial implicature persists). -/
theorem one_partial_1v3 :
    getScore (l1_lb .one .a2) .s1 > getScore (l1_lb .one .a2) .s3 := by
  native_decide

/-- Partial access (a=2): state 1 does not exceed state 2 (still canceled). -/
theorem one_partial_1v2_canceled :
    ¬(getScore (l1_lb .one .a2) .s1 > getScore (l1_lb .one .a2) .s2) := by
  native_decide

-- ============================================================================
-- Verification: every finding from the paper is accounted for
-- ============================================================================

/-- Map each empirical finding to the RSA model prediction that accounts for it. -/
def formalize : Finding → Prop
  | .some_full_implicature =>
      getScore (l1q .some_ .a3) .s2 > getScore (l1q .some_ .a3) .s3
  | .some_minimal_canceled =>
      ¬(getScore (l1q .some_ .a1) .s2 > getScore (l1q .some_ .a1) .s3)
  | .some_partial_canceled =>
      ¬(getScore (l1q .some_ .a2) .s2 > getScore (l1q .some_ .a2) .s3)
  | .two_full_upper_bounded =>
      getScore (l1_lb .two .a3) .s2 > getScore (l1_lb .two .a3) .s3
  | .two_partial_weakened =>
      ¬(getScore (l1_lb .two .a2) .s2 > getScore (l1_lb .two .a2) .s3)
  | .one_full_1v2 =>
      getScore (l1_lb .one .a3) .s1 > getScore (l1_lb .one .a3) .s2
  | .one_full_1v3 =>
      getScore (l1_lb .one .a3) .s1 > getScore (l1_lb .one .a3) .s3
  | .one_minimal_1v2_canceled =>
      ¬(getScore (l1_lb .one .a1) .s1 > getScore (l1_lb .one .a1) .s2)
  | .one_minimal_1v3_canceled =>
      ¬(getScore (l1_lb .one .a1) .s1 > getScore (l1_lb .one .a1) .s3)
  | .one_partial_1v3 =>
      getScore (l1_lb .one .a2) .s1 > getScore (l1_lb .one .a2) .s3
  | .one_partial_1v2_canceled =>
      ¬(getScore (l1_lb .one .a2) .s1 > getScore (l1_lb .one .a2) .s2)

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

end Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013Bridge
