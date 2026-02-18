/-
# Beller & Gerstenberg (2025)

RSA model for causal expression choice based on whether-causation (W),
how-causation (H), and sufficient-causation (S).

## Main definitions

- `CausalExpression`
- `CausalWorld`
- `expressionMeaning`

## References

- Beller & Gerstenberg (2025). Causation, Meaning, and Communication.
  Psychological Review.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Config
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Linglib.Core.Causation
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity

namespace RSA.BellerGerstenberg2025

open RSA Real


/-- Causal expressions in English for describing causation. -/
inductive CausalExpression
  | affected
  | enabled
  | caused
  | madeNoDifference
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

instance : Nonempty CausalExpression := ⟨.affected⟩

instance : ToString CausalExpression where
  toString
    | .affected => "affected"
    | .enabled => "enabled"
    | .caused => "caused"
    | .madeNoDifference => "made no difference"

/--
A causal world encapsulates the three causal aspects from CSM.

## Simplification Note

This is a simplified representation. In the full paper, these aspects
are computed from structural causal models via counterfactual simulation.
Here we treat them as primitive Boolean features to focus on the
RSA pragmatic reasoning over expression choice.

See `Core.Causation` and `NadathurLauer2020` for full causal machinery.
-/
structure CausalWorld where
  /-- Whether-causation: was cause necessary? (but-for test) -/
  whether : Bool
  /-- How-causation: did cause affect *how* outcome occurred? -/
  how : Bool
  /-- Sufficient-causation: was cause sufficient? -/
  sufficient : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

instance : ToString CausalWorld where
  toString cw :=
    let w := if cw.whether then "W" else "¬W"
    let h := if cw.how then "H" else "¬H"
    let s := if cw.sufficient then "S" else "¬S"
    s!"({w}, {h}, {s})"

/-- All 8 possible causal worlds (2³ combinations of W, H, S) -/
def allCausalWorlds : List CausalWorld :=
  [ ⟨false, false, false⟩,
    ⟨false, false, true⟩,
    ⟨false, true, false⟩,
    ⟨false, true, true⟩,
    ⟨true, false, false⟩,
    ⟨true, false, true⟩,
    ⟨true, true, false⟩,
    ⟨true, true, true⟩ ]

instance : Fintype CausalWorld where
  elems := {
    ⟨false, false, false⟩,
    ⟨false, false, true⟩,
    ⟨false, true, false⟩,
    ⟨false, true, true⟩,
    ⟨true, false, false⟩,
    ⟨true, false, true⟩,
    ⟨true, true, false⟩,
    ⟨true, true, true⟩
  }
  complete := by
    intro ⟨w, h, s⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, CausalWorld.mk.injEq]
    cases w <;> cases h <;> cases s <;> simp

instance : Nonempty CausalWorld := ⟨⟨false, false, false⟩⟩


/--
Semantics of causal expressions in terms of causal aspects.

From Beller & Gerstenberg (2025):
- affected: W ∨ H ∨ S (any causal involvement)
- enabled: W ∨ S (necessity or sufficiency, but not just how)
- caused: H ∧ (W ∨ S) (process + counterfactual dependence)
- made_no_difference: ¬W ∧ ¬H ∧ ¬S (no causal involvement)
-/
def expressionMeaning (cw : CausalWorld) : CausalExpression → Bool
  | .affected => cw.whether || cw.how || cw.sufficient
  | .enabled => cw.whether || cw.sufficient
  | .caused => cw.how && (cw.whether || cw.sufficient)
  | .madeNoDifference => !cw.whether && !cw.how && !cw.sufficient


-- ============================================================================
-- RSAConfig
-- ============================================================================

/-- Belief-based speaker utility for causal expression choice. -/
noncomputable def beliefBasedUtility : SpeakerUtility CausalExpression CausalWorld where
  s1Score l0 α _w u := rpow (l0 u _w) α
  s1Score_nonneg _ _α _w u hl _ := rpow_nonneg (hl u _w) _α

/-- RSAConfig for causal expression choice.

Meaning: Boolean expression semantics (1 if expression applies, 0 otherwise).
World prior: uniform over causal worlds.
Speaker utility: belief-based (rpow). -/
noncomputable def cfg : RSAConfig CausalExpression CausalWorld where
  meaning _ u cw := if expressionMeaning cw u then 1 else 0
  meaning_nonneg _ _ _ := by split <;> positivity
  latentPrior_nonneg _ := by positivity
  worldPrior_nonneg _ := by positivity
  α := 1
  α_pos := one_pos
  speakerUtility := beliefBasedUtility


/--
"caused" implies "enabled": if H ∧ (W ∨ S) then W ∨ S.

This captures the scalar relationship: "caused" is stronger than "enabled".
-/
theorem caused_implies_enabled (cw : CausalWorld) :
    expressionMeaning cw .caused → expressionMeaning cw .enabled := by
  simp only [expressionMeaning, Bool.and_eq_true, Bool.or_eq_true]
  intro ⟨_, h_ws⟩
  exact h_ws

/--
"enabled" implies "affected": if W ∨ S then W ∨ H ∨ S.

This captures the scalar relationship: "enabled" is stronger than "affected".
-/
theorem enabled_implies_affected (cw : CausalWorld) :
    expressionMeaning cw .enabled → expressionMeaning cw .affected := by
  simp only [expressionMeaning]
  cases cw.whether <;> cases cw.how <;> cases cw.sufficient <;> decide

/--
Full scalar chain: caused → enabled → affected.
-/
theorem caused_implies_affected (cw : CausalWorld) :
    expressionMeaning cw .caused → expressionMeaning cw .affected :=
  λ h => enabled_implies_affected cw (caused_implies_enabled cw h)

/--
"madeNoDifference" is the negation of "affected".
-/
theorem madeNoDifference_iff_not_affected (cw : CausalWorld) :
    expressionMeaning cw .madeNoDifference ↔ !expressionMeaning cw .affected := by
  simp only [expressionMeaning]
  cases cw.whether <;> cases cw.how <;> cases cw.sufficient <;> decide


/-- World where cause was only necessary (W only) -/
def world_W_only : CausalWorld := ⟨true, false, false⟩

/-- World where cause was only sufficient (S only) -/
def world_S_only : CausalWorld := ⟨false, false, true⟩

/-- World where cause affected how (H only) -/
def world_H_only : CausalWorld := ⟨false, true, false⟩

/-- World with full causation (W, H, S all true) -/
def world_full : CausalWorld := ⟨true, true, true⟩

/-- World with no causal involvement -/
def world_none : CausalWorld := ⟨false, false, false⟩

/-- World where "caused" applies (H and W) -/
def world_caused : CausalWorld := ⟨true, true, false⟩


/-- In W-only world, "enabled" is true but "caused" is false -/
theorem W_only_enabled_not_caused :
    expressionMeaning world_W_only .enabled = true ∧
    expressionMeaning world_W_only .caused = false := by
  simp only [expressionMeaning, world_W_only]
  decide

/-- In H-only world, neither "caused" nor "enabled" applies -/
theorem H_only_affected_only :
    expressionMeaning world_H_only .affected = true ∧
    expressionMeaning world_H_only .enabled = false ∧
    expressionMeaning world_H_only .caused = false := by
  simp only [expressionMeaning, world_H_only]
  decide

/-- In full world, all positive expressions apply -/
theorem full_world_all_true :
    expressionMeaning world_full .affected = true ∧
    expressionMeaning world_full .enabled = true ∧
    expressionMeaning world_full .caused = true ∧
    expressionMeaning world_full .madeNoDifference = false := by
  simp only [expressionMeaning, world_full]
  decide

/-- In none world, only madeNoDifference applies -/
theorem none_world_only_negative :
    expressionMeaning world_none .affected = false ∧
    expressionMeaning world_none .enabled = false ∧
    expressionMeaning world_none .caused = false ∧
    expressionMeaning world_none .madeNoDifference = true := by
  simp only [expressionMeaning, world_none]
  decide


-- ============================================================================
-- RSA Predictions (sorry'd — require noncomputable reasoning)
-- ============================================================================

/-- In full causation world, S1 prefers "caused" (most informative). -/
theorem s1_full_prefers_caused :
    cfg.S1 () world_full .caused > cfg.S1 () world_full .enabled := by
  sorry -- TODO: prove via rpow monotonicity over L0 posteriors

/-- L1 hearing "caused" infers H is likely true. -/
theorem l1_caused_infers_how :
    cfg.L1 .caused world_caused > cfg.L1 .caused world_W_only := by
  sorry -- TODO: prove via Bayesian inversion

/-!
## How RSA Derives Causal Expression Pragmatics

### Literal Semantics (L0)
- "caused" → true in worlds with H ∧ (W ∨ S)
- "enabled" → true in worlds with W ∨ S
- "affected" → true in worlds with W ∨ H ∨ S

### Pragmatic Speaker (S1)
- In world_full (W, H, S all true): prefers "caused" (most informative)
- In world_W_only: "enabled" is more informative than "affected"
- In world_H_only: only "affected" applies

### Pragmatic Listener (L1)
- Hearing "caused": infers H is likely true
- Hearing "enabled" (not "caused"): infers H is likely false
- Hearing "affected" (not "enabled"): infers W and S both likely false

This captures the scalar implicature pattern: stronger expressions
implicate the presence of stronger causal aspects.
-/

/-! ## Bridge to Structural Causal Models (Nadathur & Lauer 2020)

Beller & Gerstenberg's W, H, S dimensions can be COMPUTED from
structural causal models, grounding the primitive Boolean features
in the counterfactual reasoning machinery of `Core.Causation`.

| B&G dimension | Structural definition |
|---------------|---------------------|
| W (whether) | `causallyNecessary` — would effect still occur without cause? |
| H (how) | `hasDirectLaw` — does a causal law directly connect cause to effect? |
| S (sufficient) | `causallySufficient` — does adding cause guarantee effect? |

This bridge reveals why certain causal scenarios yield specific
expression choices: the structural properties of the causal model
determine the W-H-S world, which determines literal semantics,
which RSA pragmatics then sharpens.

### References

- Nadathur, P. & Lauer, S. (2020). Causal necessity, causal sufficiency,
  and the implications of causative verbs. Glossa 5(1), 49.
- Levin, B. (2019). Resultatives and constraints on concealed causatives.
  In Proceedings of JerSem.
-/

section StructuralBridge

open Core.Causation

/-- Compute a `CausalWorld` from a structural causal model.

    Grounds B&G's W-H-S Booleans in `Core.Causation`:
    W = necessity, H = direct law, S = sufficiency. -/
def causalWorldFromModel (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : CausalWorld :=
  let p := extractProfile dyn bg cause effect
  { whether := p.necessary, how := p.direct, sufficient := p.sufficient }

-- Concrete models for testing the bridge
private def mA : Variable := mkVar "bg_cause"
private def mB : Variable := mkVar "bg_alt"
private def mC : Variable := mkVar "bg_effect"
private def mI : Variable := mkVar "bg_intermediate"

/-- Solo cause model: one direct law, a → c. -/
private def soloModel : CausalDynamics := ⟨[CausalLaw.simple mA mC]⟩

/-- Overdetermination model: a ∨ b → c, with b active in background. -/
private def overdetModel : CausalDynamics :=
  CausalDynamics.disjunctiveCausation mA mB mC
private def overdetBg : Situation := Situation.empty.extend mB true

/-- Causal chain model: a → intermediate → c. -/
private def chainModel : CausalDynamics :=
  CausalDynamics.causalChain mA mI mC

/-- Solo cause → full causation world (W=true, H=true, S=true).

    When there's one direct cause and no alternatives, all three
    causal dimensions are active. -/
theorem solo_cause_world :
    causalWorldFromModel soloModel Situation.empty mA mC =
    ⟨true, true, true⟩ := by native_decide

/-- Overdetermination → W=false, H=true, S=true.

    The cause is sufficient (S) and directly connected (H), but NOT
    necessary (W=false) because the alternative cause in the background
    would produce the effect anyway. -/
theorem overdetermination_world :
    causalWorldFromModel overdetModel overdetBg mA mC =
    ⟨false, true, true⟩ := by native_decide

/-- Causal chain → W=true, H=false, S=true.

    The initial cause is sufficient (S) and necessary (W), but NOT
    directly connected (H=false) — it operates through an intermediate.
    This is Levin's (2019) "intervening causer" scenario. -/
theorem chain_world :
    causalWorldFromModel chainModel Situation.empty mA mC =
    ⟨true, false, true⟩ := by native_decide

/-! ### Expression predictions from structural models

The structural bridge makes testable predictions: given a causal
model, we can compute both the W-H-S world AND the appropriate
causal expression. -/

/-- Solo cause: "caused" is literally true.

    With W, H, S all true, the strongest expression applies. -/
theorem solo_cause_expression_caused :
    expressionMeaning (causalWorldFromModel soloModel Situation.empty mA mC)
      .caused = true := by native_decide

/-- Chain causation: "caused" is NOT literally true.

    Despite sufficiency and necessity, the lack of direct connection
    (H=false) means "caused" doesn't apply. B&G predict speakers will
    use "enabled" instead — capturing Levin's (2019) intuition that
    indirect causation is expressed differently. -/
theorem chain_not_caused :
    expressionMeaning (causalWorldFromModel chainModel Situation.empty mA mC)
      .caused = false := by native_decide

/-- Chain causation: "enabled" still applies.

    W ∨ S = true ∨ true = true, so "enabled" is literally true.
    This is the weaker expression appropriate for indirect causation. -/
theorem chain_still_enabled :
    expressionMeaning (causalWorldFromModel chainModel Situation.empty mA mC)
      .enabled = true := by native_decide

/-- Overdetermination: "caused" is literally true.

    H ∧ (W ∨ S) = true ∧ (false ∨ true) = true. The cause is directly
    connected (H) and sufficient (S), so "caused" applies even without
    necessity (W=false). -/
theorem overdetermination_caused :
    expressionMeaning (causalWorldFromModel overdetModel overdetBg mA mC)
      .caused = true := by native_decide

/-- Bridge between B&G's "caused" and N&L's make/cause distinction.

    In the overdetermination scenario, `makeSem` holds (a IS sufficient)
    but `causeSem` fails (a is NOT necessary). Meanwhile B&G's "caused"
    applies (because H is true). This shows B&G's expression semantics
    and N&L's verb semantics make orthogonal predictions:

    - N&L: You can say "A made C happen" (sufficient) but NOT "A caused
      C" (not necessary)
    - B&G: Speakers would use "caused" (H ∧ S = true)

    The divergence reflects different questions: N&L model *verb choice*
    (make vs cause), B&G model *expression choice* (caused vs enabled). -/
theorem bg_caused_vs_nl_cause_diverge :
    -- B&G: "caused" applies in overdetermination
    expressionMeaning (causalWorldFromModel overdetModel overdetBg mA mC) .caused = true ∧
    -- N&L: makeSem holds (sufficient)
    causallySufficient overdetModel overdetBg mA mC = true ∧
    -- N&L: causeSem fails (not necessary)
    causallyNecessary overdetModel overdetBg mA mC = false := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

end StructuralBridge

end RSA.BellerGerstenberg2025
