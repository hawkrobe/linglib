/-!
# Denić, Homer, Rothschild & Chemla (2021) @cite{denic-homer-rothschild-chemla-2021}

The influence of polarity items on inferential judgments.
*Cognition* 215, 104791.

## The puzzle

The standard story is unidirectional: monotonicity determines where PIs are
grammatical. If the arrow goes only from monotonicity to PIs, then PI presence
should be inert — it shouldn't change how listeners perceive the monotonicity
of the environment. This paper shows it does.

## Design

Three experiments, 4 × 4 design:
- **Environments**: UE, DE, NM (non-monotone), DN (doubly negative)
- **PI conditions**: NPI (*any/ever/at all*), PPI (*some*), no-PI simple,
  no-PI complex

Participants rated sentence pairs (related by a narrowing substitution) for
both UE-ness and DE-ness on 7-point scales. The directional rating (UE − DE)
gives a single bipolar measure.

## Core findings

1. **NPI in NM**: directional ratings shift toward DE (significant)
2. **PPI in DN**: directional ratings shift toward UE (significant)
3. **UE and DE**: no PI effects (ceiling/floor)
4. **Exp 3**: NPI effect persists when controlling for domain-widening
   semantics, arguing against a purely scalar side-effect account

## Significance for linglib

The finding that PIs distinguish DN from UE challenges `ContextPolarity`,
which maps both to `.upward`. The full `EntailmentSig` preserves the
distinction (DN = `addMult`, simple UE = `mono`), suggesting PI-sensitive
code should use `EntailmentSig` paths rather than `ContextPolarity`.
-/

namespace Phenomena.Polarity.Studies.DenicEtAl2021

-- ============================================================================
-- Environment and Condition Types
-- ============================================================================

/-- The four monotonicity environments tested.

A refinement of `Core.NaturalLogic.ContextPolarity` that keeps DN distinct
from UE. `ContextPolarity` maps both to `.upward`; the paper shows PIs
distinguish them empirically. -/
inductive MonotonicityEnv where
  | UE  -- Upward entailing (monotone)
  | DE  -- Downward entailing (antitone)
  | NM  -- Non-monotone (e.g., "exactly N")
  | DN  -- Doubly negative: globally UE, locally DE at each step
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Whether an environment is globally upward-entailing.
DN and UE both return true — the crux of the coarsening problem. -/
def MonotonicityEnv.isGloballyUE : MonotonicityEnv → Bool
  | .UE | .DN => true
  | .DE | .NM => false

#guard MonotonicityEnv.DN.isGloballyUE == true
#guard MonotonicityEnv.UE.isGloballyUE == true
#guard MonotonicityEnv.DN != MonotonicityEnv.UE

/-- The four PI conditions in the experimental design. -/
inductive PICondition where
  | npi          -- Sentence contains an NPI (any, ever, at all)
  | ppi          -- Sentence contains the PPI "some"
  | noPISimple   -- No PI, simple NP
  | noPIComplex  -- No PI, complex NP (controls for structural complexity)
  deriving DecidableEq, BEq, Repr, Inhabited

-- ============================================================================
-- Core Data: PI Influence Findings
-- ============================================================================

/-- A finding about PI influence on directional ratings within an environment.
The key observable: does PI presence significantly shift ratings relative to
the no-PI baseline, and in which direction? -/
structure PIInfluence where
  experiment : Nat
  environment : MonotonicityEnv
  piCondition : PICondition
  /-- Significant difference from no-PI baseline? -/
  significant : Bool
  /-- Direction of shift: `.UE` if toward UE, `.DE` if toward DE, none if n.s. -/
  shiftDirection : Option MonotonicityEnv
  evidence : String
  deriving Repr

-- ============================================================================
-- Experiment 1: The Core 4 × 4 Design
-- ============================================================================

/-- NPI in NM: shifts directional ratings toward DE. -/
def exp1_npi_NM : PIInfluence :=
  { experiment := 1, environment := .NM, piCondition := .npi
  , significant := true, shiftDirection := some .DE
  , evidence := "NPI < no-PI in NM; significant interaction" }

/-- PPI in DN: shifts directional ratings toward UE. -/
def exp1_ppi_DN : PIInfluence :=
  { experiment := 1, environment := .DN, piCondition := .ppi
  , significant := true, shiftDirection := some .UE
  , evidence := "PPI > no-PI in DN; significant interaction" }

/-- NPI in UE: no effect (ceiling). -/
def exp1_npi_UE : PIInfluence :=
  { experiment := 1, environment := .UE, piCondition := .npi
  , significant := false, shiftDirection := none
  , evidence := "NPI ≈ no-PI in UE; n.s." }

/-- NPI in DE: no effect (floor). -/
def exp1_npi_DE : PIInfluence :=
  { experiment := 1, environment := .DE, piCondition := .npi
  , significant := false, shiftDirection := none
  , evidence := "NPI ≈ no-PI in DE; n.s." }

/-- PPI in UE: no effect. -/
def exp1_ppi_UE : PIInfluence :=
  { experiment := 1, environment := .UE, piCondition := .ppi
  , significant := false, shiftDirection := none
  , evidence := "PPI ≈ no-PI in UE; n.s." }

/-- PPI in DE: no effect. -/
def exp1_ppi_DE : PIInfluence :=
  { experiment := 1, environment := .DE, piCondition := .ppi
  , significant := false, shiftDirection := none
  , evidence := "PPI ≈ no-PI in DE; n.s." }

/-- NPI in DN: no significant effect. -/
def exp1_npi_DN : PIInfluence :=
  { experiment := 1, environment := .DN, piCondition := .npi
  , significant := false, shiftDirection := none
  , evidence := "NPI ≈ no-PI in DN; n.s." }

/-- PPI in NM: no significant effect. -/
def exp1_ppi_NM : PIInfluence :=
  { experiment := 1, environment := .NM, piCondition := .ppi
  , significant := false, shiftDirection := none
  , evidence := "PPI ≈ no-PI in NM; n.s." }

def experiment1 : List PIInfluence :=
  [ exp1_npi_NM, exp1_ppi_DN
  , exp1_npi_UE, exp1_npi_DE, exp1_ppi_UE, exp1_ppi_DE
  , exp1_npi_DN, exp1_ppi_NM ]

-- ============================================================================
-- Experiment 3: Controlling for Scalar Side-Effects
-- ============================================================================

/-- Experiment 3 controls for mechanism (b): the scalar side-effect hypothesis.
NPIs whose semantics don't involve domain widening (e.g., "ever") still shift
NM ratings toward DE, ruling out domain widening as the sole mechanism. -/
def exp3_npi_NM_controlled : PIInfluence :=
  { experiment := 3, environment := .NM, piCondition := .npi
  , significant := true, shiftDirection := some .DE
  , evidence := "NPI effect in NM persists without domain-widening semantics" }

-- ============================================================================
-- Empirical Generalizations
-- ============================================================================

-- The two positive findings
#guard exp1_npi_NM.significant == true
#guard exp1_ppi_DN.significant == true

-- The six null findings
#guard (experiment1.filter (λ f => !f.significant)).length == 6

-- Direction: NPIs shift toward DE, PPIs shift toward UE
#guard exp1_npi_NM.shiftDirection == some .DE
#guard exp1_ppi_DN.shiftDirection == some .UE

-- Exp 3: effect persists without domain widening
#guard exp3_npi_NM_controlled.significant == true

/-- The complementary pattern: each PI type affects exactly the environment
where its associated polarity is ambiguous.

- NPIs (associated with DE) affect NM but not DN
- PPIs (associated with UE) affect DN but not NM -/
structure ComplementaryPattern where
  npi_affects_NM : Bool
  npi_affects_DN : Bool
  ppi_affects_NM : Bool
  ppi_affects_DN : Bool
  complementary : npi_affects_NM = true ∧ npi_affects_DN = false ∧
                  ppi_affects_NM = false ∧ ppi_affects_DN = true

def observedPattern : ComplementaryPattern :=
  { npi_affects_NM := exp1_npi_NM.significant
  , npi_affects_DN := exp1_npi_DN.significant
  , ppi_affects_NM := exp1_ppi_NM.significant
  , ppi_affects_DN := exp1_ppi_DN.significant
  , complementary := ⟨rfl, rfl, rfl, rfl⟩ }

-- ============================================================================
-- Mechanism Predictions
-- ============================================================================

/-- The three proposed mechanisms for PI influence on monotonicity. -/
inductive Mechanism where
  | priming            -- PIs prime/cue the monotonicity computation
  | scalarSideEffect   -- PIs' scalar semantics create inferential side-effects
  | statisticalTracking -- Listeners track PI–environment co-occurrence
  deriving DecidableEq, BEq, Repr

/-- Experiment 3 rules out the scalar side-effect as the sole mechanism. -/
structure MechanismVerdict where
  mechanism : Mechanism
  ruledOutAsSole : Bool
  evidence : String
  deriving Repr

def exp3_verdict : MechanismVerdict :=
  { mechanism := .scalarSideEffect
  , ruledOutAsSole := true
  , evidence := "NPI effect persists for non-domain-widening NPIs (Exp 3)" }

#guard exp3_verdict.ruledOutAsSole == true

-- ============================================================================
-- Items Tested
-- ============================================================================

def npiItemsTested : List String := ["any", "ever", "at all"]
def ppiItemTested : String := "some"

def citation : String :=
  "Denić, Homer, Rothschild & Chemla (2021). Cognition 215, 104791."

end Phenomena.Polarity.Studies.DenicEtAl2021
