import Linglib.Theories.Pragmatics.RSA.Implementations.KaoEtAl2014_Hyperbole
import Linglib.Phenomena.Nonliteral.Hyperbole.Studies.KaoEtAl2014
import Linglib.Tactics.RSAPredict

/-!
# Kao et al. (2014) — RSA Bridge @cite{kao-etal-2014-hyperbole}

Bridge theorems verifying that the QUD-RSA model reproduces the qualitative
empirical findings from Experiments 3a–3c.

All proofs are by `rsa_predict`, which reifies 1000 S1 scores via exp-log
simplification, computes L1 bounds at meta level, and checks separation.

| # | Finding | Goal form | Theorem |
|---|---------|-----------|---------|
| 1 | affect at modal price | L1 comparison | `hyperbole_affect_at_modal` |
| 2 | marginal notable > none | L1 sum (same u) | `hyperbole_affect` |
| 3 | valence QUD > price QUD | latent inference | `hyperbole_qud` |
| 4 | "$50" → $50 > $500 | L1 comparison | `literal_correct` |
| 5 | "$50" → $50 > $10K | L1 comparison | `literal_not_hyperbolic` |
| 6 | "$501" > "$500" precision | L1 sum (cross-utterance) | `halo_sharp_500` |
-/

set_option autoImplicit false

namespace Phenomena.Nonliteral.Hyperbole.KaoEtAl2014Bridge

open RSA.KaoEtAl2014_Hyperbole
open KaoEtAl2014 (Finding)

-- ============================================================================
-- Hyperbole: "$10,000" for an electric kettle
-- ============================================================================

set_option maxHeartbeats 400000 in
/-- At the modal price ($10K), notable affect > no affect.
    The speaker saying "$10K" about a kettle signals frustration. -/
theorem hyperbole_affect_at_modal :
    kettleCfg.L1 .s10000 (.s10000, .notable) >
    kettleCfg.L1 .s10000 (.s10000, .none) := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- Marginal: notable affect dominates overall for "$10K".
    Σ_s L1(s, notable | "$10K") > Σ_s L1(s, none | "$10K"). -/
theorem hyperbole_affect :
    kettleCfg.L1 .s10000 (.s50, .notable) + kettleCfg.L1 .s10000 (.s51, .notable) +
    kettleCfg.L1 .s10000 (.s500, .notable) + kettleCfg.L1 .s10000 (.s501, .notable) +
    kettleCfg.L1 .s10000 (.s1000, .notable) + kettleCfg.L1 .s10000 (.s1001, .notable) +
    kettleCfg.L1 .s10000 (.s5000, .notable) + kettleCfg.L1 .s10000 (.s5001, .notable) +
    kettleCfg.L1 .s10000 (.s10000, .notable) + kettleCfg.L1 .s10000 (.s10001, .notable) >
    kettleCfg.L1 .s10000 (.s50, .none) + kettleCfg.L1 .s10000 (.s51, .none) +
    kettleCfg.L1 .s10000 (.s500, .none) + kettleCfg.L1 .s10000 (.s501, .none) +
    kettleCfg.L1 .s10000 (.s1000, .none) + kettleCfg.L1 .s10000 (.s1001, .none) +
    kettleCfg.L1 .s10000 (.s5000, .none) + kettleCfg.L1 .s10000 (.s5001, .none) +
    kettleCfg.L1 .s10000 (.s10000, .none) + kettleCfg.L1 .s10000 (.s10001, .none) := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- The listener infers valence QUD over price QUD. -/
theorem hyperbole_qud :
    kettleCfg.L1_latent .s10000 .valence >
    kettleCfg.L1_latent .s10000 .price := by
  rsa_predict

-- ============================================================================
-- Literal: "$50" for an electric kettle
-- ============================================================================

set_option maxHeartbeats 400000 in
/-- Hearing "$50", the listener infers $50 > $500. -/
theorem literal_correct :
    kettleCfg.L1 .s50 (.s50, .none) >
    kettleCfg.L1 .s50 (.s500, .none) := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- Literal utterances are not interpreted hyperbolically. -/
theorem literal_not_hyperbolic :
    kettleCfg.L1 .s50 (.s50, .none) >
    kettleCfg.L1 .s50 (.s10000, .none) := by
  rsa_predict

-- ============================================================================
-- Pragmatic halo: round vs sharp numbers
-- ============================================================================

set_option maxHeartbeats 400000 in
/-- Sharp "$501" is interpreted more precisely than round "$500". -/
theorem halo_sharp_500 :
    kettleCfg.L1 .s501 (.s501, .none) + kettleCfg.L1 .s501 (.s501, .notable) >
    kettleCfg.L1 .s500 (.s500, .none) + kettleCfg.L1 .s500 (.s500, .notable) := by
  rsa_predict

-- ============================================================================
-- Verification: every finding from the paper is accounted for
-- ============================================================================

/-- Map each empirical finding to the RSA model prediction that accounts for it. -/
def formalize : Finding → Prop
  | .affect_at_modal =>
      kettleCfg.L1 .s10000 (.s10000, .notable) >
      kettleCfg.L1 .s10000 (.s10000, .none)
  | .affect_marginal =>
      kettleCfg.L1 .s10000 (.s50, .notable) + kettleCfg.L1 .s10000 (.s51, .notable) +
      kettleCfg.L1 .s10000 (.s500, .notable) + kettleCfg.L1 .s10000 (.s501, .notable) +
      kettleCfg.L1 .s10000 (.s1000, .notable) + kettleCfg.L1 .s10000 (.s1001, .notable) +
      kettleCfg.L1 .s10000 (.s5000, .notable) + kettleCfg.L1 .s10000 (.s5001, .notable) +
      kettleCfg.L1 .s10000 (.s10000, .notable) + kettleCfg.L1 .s10000 (.s10001, .notable) >
      kettleCfg.L1 .s10000 (.s50, .none) + kettleCfg.L1 .s10000 (.s51, .none) +
      kettleCfg.L1 .s10000 (.s500, .none) + kettleCfg.L1 .s10000 (.s501, .none) +
      kettleCfg.L1 .s10000 (.s1000, .none) + kettleCfg.L1 .s10000 (.s1001, .none) +
      kettleCfg.L1 .s10000 (.s5000, .none) + kettleCfg.L1 .s10000 (.s5001, .none) +
      kettleCfg.L1 .s10000 (.s10000, .none) + kettleCfg.L1 .s10000 (.s10001, .none)
  | .qud_valence =>
      kettleCfg.L1_latent .s10000 .valence >
      kettleCfg.L1_latent .s10000 .price
  | .literal_correct =>
      kettleCfg.L1 .s50 (.s50, .none) >
      kettleCfg.L1 .s50 (.s500, .none)
  | .literal_not_hyperbolic =>
      kettleCfg.L1 .s50 (.s50, .none) >
      kettleCfg.L1 .s50 (.s10000, .none)
  | .halo_sharp_precise =>
      kettleCfg.L1 .s501 (.s501, .none) + kettleCfg.L1 .s501 (.s501, .notable) >
      kettleCfg.L1 .s500 (.s500, .none) + kettleCfg.L1 .s500 (.s500, .notable)

/-- The RSA model accounts for all 6 empirical findings from Kao et al. (2014). -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact hyperbole_affect_at_modal
  · exact hyperbole_affect
  · exact hyperbole_qud
  · exact literal_correct
  · exact literal_not_hyperbolic
  · exact halo_sharp_500

end Phenomena.Nonliteral.Hyperbole.KaoEtAl2014Bridge
