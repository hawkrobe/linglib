import Mathlib.Data.Rat.Defs
import Linglib.Core.BToM
import Linglib.Theories.Semantics.Attitudes.Factivity

/-!
# Scontras & Tonhauser (2025) @cite{scontras-tonhauser-2025}

Projection emerges from RSA over speaker's private assumptions, not lexical
presupposition. L1 infers what speaker takes for granted (dcS in F&B terms).

This is a BToM model (Baker et al. 2017): L1 inverts S1's generative model
to jointly infer the speaker's belief state and the world state.

## Factive Semantics

Literal truth conditions derive from `Semantics.Attitudes.Factivity`:
know = `factivePos` (BEL ∧ C), think = `nonFactivePos` (BEL). This makes
the entailment properties (factivity, know ⊃ think) follow directly from
the generic theory rather than requiring per-model bridge theorems.
-/

namespace RSA.ScontrasTonhauser2025

open Semantics.Attitudes.Factivity

-- ============================================================================
-- §1. World and Utterance Types
-- ============================================================================

/-- World state: tracks belief and complement truth.

    (BEL, C) where:
    - BEL: Cole believes the complement
    - C: The complement is actually true -/
structure WorldState where
  bel : Bool
  c : Bool
  deriving DecidableEq, Repr, BEq, Inhabited

/-- All four world states. -/
def allWorlds : List WorldState := [
  ⟨true, true⟩, ⟨true, false⟩, ⟨false, true⟩, ⟨false, false⟩
]

instance : HasComplement WorldState where c := WorldState.c
instance : HasBelief WorldState where bel := WorldState.bel

/-- Attitude verb utterances about Cole's mental state. -/
inductive Utterance where
  | knowPos     -- "Cole knows that C"
  | knowNeg     -- "Cole doesn't know that C"
  | thinkPos    -- "Cole thinks that C"
  | thinkNeg    -- "Cole doesn't think that C"
  deriving DecidableEq, Repr, BEq, Inhabited

def allUtterances : List Utterance := [.knowPos, .knowNeg, .thinkPos, .thinkNeg]

-- ============================================================================
-- §2. Literal Truth Conditions (derived from Factivity)
-- ============================================================================

/-- Literal truth conditions derived from factive/non-factive semantics.

    "know" is factive: `factivePos` = BEL ∧ C
    "think" is non-factive: `nonFactivePos` = BEL

    This makes the entailment properties (factivity, know ⊃ think) follow
    directly from the generic theory — no per-model bridge theorems needed. -/
def literalMeaning : Utterance → WorldState → Bool
  | .knowPos  => factivePos
  | .knowNeg  => factiveNeg
  | .thinkPos => nonFactivePos
  | .thinkNeg => nonFactiveNeg

/-- "know" entails C (follows from `factivePos_entails_c`). -/
theorem know_entails_c : ∀ w, literalMeaning .knowPos w = true → w.c = true :=
  factivePos_entails_c

/-- "think" does NOT entail C. -/
theorem think_not_entails_c :
    ∃ w, literalMeaning .thinkPos w = true ∧ w.c = false :=
  ⟨⟨true, false⟩, rfl, rfl⟩

-- ============================================================================
-- §3. Speaker Belief States
-- ============================================================================

/-- Speaker's private assumptions: a non-empty subset of worlds.

    We represent this as a named subset for efficiency.
    In the paper, A ranges over all non-empty subsets of W. -/
inductive BeliefState where
  | all            -- Speaker considers all worlds possible
  | cTrue          -- Speaker assumes C is true: {(1,1), (0,1)}
  | cFalse         -- Speaker assumes C is false: {(1,0), (0,0)}
  | belTrue        -- Speaker assumes Cole believes: {(1,1), (1,0)}
  | belFalse       -- Speaker assumes Cole doesn't believe: {(0,1), (0,0)}
  | cTrueBelTrue   -- {(1,1)}
  | cTrueBelFalse  -- {(0,1)}
  | cFalseBelTrue  -- {(1,0)}
  | cFalseBelFalse -- {(0,0)}
  deriving DecidableEq, Repr, BEq, Inhabited

def allBeliefStates : List BeliefState := [
  .all, .cTrue, .cFalse, .belTrue, .belFalse,
  .cTrueBelTrue, .cTrueBelFalse, .cFalseBelTrue, .cFalseBelFalse
]

/-- Membership in belief state (as credence). -/
def speakerCredenceBool : BeliefState → WorldState → Bool
  | .all, _ => true
  | .cTrue, w => w.c
  | .cFalse, w => !w.c
  | .belTrue, w => w.bel
  | .belFalse, w => !w.bel
  | .cTrueBelTrue, w => w.c && w.bel
  | .cTrueBelFalse, w => w.c && !w.bel
  | .cFalseBelTrue, w => !w.c && w.bel
  | .cFalseBelFalse, w => !w.c && !w.bel

/-- Whether C is true in all worlds of the belief state.
    This is what it means for C to be "assumed" by the speaker. -/
def assumesC : BeliefState → Bool
  | .cTrue => true
  | .cTrueBelTrue => true
  | .cTrueBelFalse => true
  | _ => false

-- ============================================================================
-- §4. Priors
-- ============================================================================

/-- World prior parameterized by P(C).

    P(BEL, C) = P(BEL | C) · P(C)

    We assume P(BEL | C) is uniform for simplicity. -/
def worldPrior (pC : ℚ) : WorldState → ℚ
  | ⟨_, true⟩ => pC / 2
  | ⟨_, false⟩ => (1 - pC) / 2

/-- Belief state prior following Section 4 of Scontras & Tonhauser (2025):
    - Knowledge of C is 4x as likely as knowledge of BEL
    - Full knowledge (singletons) is 0.5x as likely as knowledge of BEL
    - No beliefs (all) is 0.5x as likely as singletons

    This captures that speakers more often have knowledge about C than
    about BEL. -/
def beliefStatePrior : BeliefState → ℚ
  | .all => 1/4
  | .cTrue => 4
  | .cFalse => 4
  | .belTrue => 1
  | .belFalse => 1
  | _ => 1/2

-- ============================================================================
-- §5. Bridge: Pattern-Matched assumesC vs Generic assumesComplement
-- ============================================================================

/-- The pattern-matched `assumesC` agrees with the generic
    `assumesComplement` from `Factivity`. This verifies the hand-written
    classification against the derived-from-membership computation. -/
theorem assumesC_matches_generic : ∀ bs : BeliefState,
    assumesC bs = assumesComplement (speakerCredenceBool bs) allWorlds := by
  intro bs; cases bs <;> decide

-- ============================================================================
-- §6. BToM Structural Mapping
-- ============================================================================

open Core.BToM in
/-- Classification of BeliefState in BToM terms.

    The speaker's private assumptions are a mental state — what Baker et al.
    (2017) call the agent's epistemic state. The L1 listener inverts S1's
    generative model to jointly infer this belief state and the world, making
    presupposition projection an instance of BToM observer inference. -/
def beliefStateCategory : LatentCategory := .mental

open Core.BToM in
/-- Classification of QUD in BToM terms.

    The QUD is intersubjective — maintained between speaker and listener.
    This is Clark's (1996) shared state: both interlocutors track what
    question is under discussion, and the speaker optimizes informativity
    with respect to it. -/
def qudCategory : LatentCategory := .shared

/-- Characteristic function for BToM belief-expectation: does the speaker
    assume C?

    The listener's posterior probability that the speaker assumes C is a
    `BToMModel.beliefExpectation` with this indicator function:

        P_obs(assumes C | u) ∝ Σ_bs P(bs | u) · assumesCIndicator(bs)

    where P(bs | u) is the BToM belief marginal. -/
def assumesCIndicator : BeliefState → ℚ :=
  fun bs => if assumesC bs then 1 else 0

/-- Belief states that assume C have indicator 1. -/
theorem assumesCIndicator_pos (bs : BeliefState) (h : assumesC bs = true) :
    assumesCIndicator bs = 1 := by
  simp [assumesCIndicator, h]

/-- Belief states that don't assume C have indicator 0. -/
theorem assumesCIndicator_neg (bs : BeliefState) (h : assumesC bs = false) :
    assumesCIndicator bs = 0 := by
  simp [assumesCIndicator, h]

/-- The three C-entailing belief states are exactly those with indicator 1. -/
theorem assumesCIndicator_classification :
    assumesCIndicator .cTrue = 1 ∧
    assumesCIndicator .cTrueBelTrue = 1 ∧
    assumesCIndicator .cTrueBelFalse = 1 ∧
    assumesCIndicator .all = 0 ∧
    assumesCIndicator .cFalse = 0 ∧
    assumesCIndicator .belTrue = 0 ∧
    assumesCIndicator .belFalse = 0 ∧
    assumesCIndicator .cFalseBelTrue = 0 ∧
    assumesCIndicator .cFalseBelFalse = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end RSA.ScontrasTonhauser2025
