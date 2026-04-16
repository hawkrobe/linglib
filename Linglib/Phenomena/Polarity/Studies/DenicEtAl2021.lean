import Linglib.Core.Logic.NaturalLogic
import Linglib.Core.Lexical.PolarityItem
import Linglib.Fragments.English.PolarityItems

/-!
# @cite{denic-homer-rothschild-chemla-2021}

The influence of polarity items on inferential judgments.
*Cognition* 215, 104791.

## The puzzle

The standard story is unidirectional: monotonicity determines where PIs are
grammatical. If the arrow goes only from monotonicity to PIs, then PI presence
should be inert — it shouldn't change how listeners perceive the monotonicity
of the environment. This paper shows it does.

## Design

Four experiments (§3–§7):
- **Environments**: UE, DE, NM (Exps 1–4); DN added in Exps 3–4
- **PI conditions**: NPI (*any/ever/at all*), PPI (*some*), no-PI

Participants rated sentence pairs (related by a narrowing substitution) for
both UE-ness and DE-ness on 7-point scales. The directional rating (UE − DE)
gives a single bipolar measure.

## Core findings

1. **NPI in NM**: directional ratings shift toward DE (significant across all exps)
2. **PPI in DN**: directional ratings shift toward UE (significant in Exp 3)
3. **UE and DE**: no PI effects (ceiling/floor)
4. Scalar side-effect not the sole mechanism: the NPI effect holds across
   NPIs with heterogeneous scalar properties (e.g., "ever" lacks domain
   widening; §10.2)

## Significance for linglib

The finding that PIs distinguish DN from UE challenges `ContextPolarity`,
which maps both to `.upward`. The full `EntailmentSig` preserves the
distinction (DN = `addMult`, simple UE = `mono`), suggesting PI-sensitive
code should use `EntailmentSig` paths rather than `ContextPolarity`.
-/

namespace DenicEtAl2021

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
  deriving DecidableEq, Repr, Inhabited

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
  deriving DecidableEq, Repr, Inhabited

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

/-- PPI in DN: shifts directional ratings toward UE (Exp 3, §6.3). -/
def exp1_ppi_DN : PIInfluence :=
  { experiment := 3, environment := .DN, piCondition := .ppi
  , significant := true, shiftDirection := some .UE
  , evidence := "PPI > no-PI in DN; P(β>0)=.998 (Exp 3)" }

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

/-- NPI in DN: no significant effect (Exp 3, §6.3). -/
def exp1_npi_DN : PIInfluence :=
  { experiment := 3, environment := .DN, piCondition := .npi
  , significant := false, shiftDirection := none
  , evidence := "NPI ≈ no-PI in DN; P(β<0)=.887 (Exp 3, below threshold)" }

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

/-- NPI effect in NM replicates in Experiment 3 (§6.3).
The NPI effect holds across NPIs with heterogeneous scalar properties
(any = domain widening, ever = non-domain-widening), which argues
against scalar side-effects as the sole mechanism (§10.2). -/
def exp3_npi_NM_controlled : PIInfluence :=
  { experiment := 3, environment := .NM, piCondition := .npi
  , significant := true, shiftDirection := some .DE
  , evidence := "NPI effect in NM replicates in Exp 3; P(β<0)>.95" }

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
  deriving DecidableEq, Repr

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

-- ============================================================================
-- § Entailment Signature Bridge
-- ============================================================================

open Core.NaturalLogic
open Core.Lexical.PolarityItem
open Fragments.English.PolarityItems

/-- Map the paper's environments to canonical entailment signatures. -/
def envSignature : MonotonicityEnv → Option EntailmentSig
  | .UE => some .mono
  | .DE => some .antiAdd
  | .DN => some .addMult
  | .NM => none

/-- The DE environment maps to a DE-side signature. -/
theorem de_env_is_de :
    EntailmentSig.toContextPolarity .antiAdd = .downward := by
  native_decide

/-- `isGloballyUE` is *derived* from the signature map, not stipulated. -/
theorem isGloballyUE_from_signature (env : MonotonicityEnv) :
    env.isGloballyUE = match envSignature env with
      | some sig => EntailmentSig.toContextPolarity sig == ContextPolarity.upward
      | none => false := by
  cases env <;> native_decide

/-- Any composition of two DE-side signatures is UE under `ContextPolarity`. -/
theorem de_composed_is_ue (φ ψ : EntailmentSig)
    (hφ : EntailmentSig.toContextPolarity φ = .downward)
    (hψ : EntailmentSig.toContextPolarity ψ = .downward) :
    EntailmentSig.toContextPolarity (φ * ψ) = .upward := by
  rw [EntailmentSig.toContextPolarity_compose, hφ, hψ]
  rfl

/-- `ContextPolarity` cannot distinguish ANY doubly-negative environment
from simple UE. -/
theorem contextPolarity_blind_to_dn (φ ψ : EntailmentSig)
    (hφ : EntailmentSig.toContextPolarity φ = .downward)
    (hψ : EntailmentSig.toContextPolarity ψ = .downward) :
    EntailmentSig.toContextPolarity (φ * ψ) =
    EntailmentSig.toContextPolarity .mono := by
  rw [de_composed_is_ue φ ψ hφ hψ]
  native_decide

/-- `EntailmentSig` preserves DN–UE distinctions that `ContextPolarity` erases. -/
theorem dn_signatures_vary :
    EntailmentSig.compose .antiAddMult .antiAddMult ≠
    EntailmentSig.compose .antiAdd .antiMult := by native_decide

/-- UE strength distinguishes DN from UE. -/
theorem ue_strength_distinguishes_dn_ue :
    EntailmentSig.toUEStrength .addMult = some .additive ∧
    EntailmentSig.toUEStrength .mono = some .weak :=
  ⟨by native_decide, by native_decide⟩

/-- DN has no DE strength. -/
theorem dn_has_no_de_strength :
    EntailmentSig.toDEStrength .addMult = none := by
  native_decide

/-- Central theorem: PPI effect reveals a distinction that
`ContextPolarity` provably cannot make. -/
theorem ppi_reveals_coarsening_failure :
    (∀ φ ψ : EntailmentSig,
      EntailmentSig.toContextPolarity φ = .downward →
      EntailmentSig.toContextPolarity ψ = .downward →
      EntailmentSig.toContextPolarity (φ * ψ) =
        EntailmentSig.toContextPolarity .mono) ∧
    (EntailmentSig.toUEStrength .addMult ≠ EntailmentSig.toUEStrength .mono) ∧
    exp1_ppi_DN.significant = true ∧
    exp1_ppi_UE.significant = false :=
  ⟨contextPolarity_blind_to_dn, by native_decide, rfl, rfl⟩

/-- NPI effects target environments with no determinate signature. -/
theorem npi_targets_signatureless_env :
    envSignature .NM = none ∧
    exp1_npi_NM.significant = true ∧
    exp1_npi_DN.significant = false ∧
    exp1_npi_UE.significant = false ∧
    exp1_npi_DE.significant = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- PPI effects target environments with composite UE signatures. -/
theorem ppi_targets_composite_ue_env :
    envSignature .DN = some EntailmentSig.addMult ∧
    EntailmentSig.addMult ≠ .mono ∧
    EntailmentSig.toUEStrength .addMult ≠ EntailmentSig.toUEStrength .mono ∧
    exp1_ppi_DN.significant = true ∧
    exp1_ppi_UE.significant = false ∧
    exp1_ppi_DE.significant = false ∧
    exp1_ppi_NM.significant = false :=
  ⟨rfl, by decide, by native_decide, rfl, rfl, rfl, rfl⟩

/-- The NPIs tested are classified as NPIs in the Fragment lexicon. -/
theorem tested_npis_are_npis :
    any.isNPI = true ∧ ever.isNPI = true ∧ atAll.isNPI = true :=
  ⟨rfl, rfl, rfl⟩

/-- The PPI tested is classified as a PPI in the Fragment lexicon. -/
theorem tested_ppi_is_ppi : some_ppi.isPPI = true := rfl

/-- The tested NPIs are all strengthening (@cite{israel-2001} Figure 1)
    but have heterogeneous semantic bases — the mechanism isn't
    purely about domain widening (§10.2). -/
theorem tested_npis_all_strengthening :
    any.scalarDirection = .strengthening ∧
    ever.scalarDirection = .strengthening ∧
    atAll.scalarDirection = .strengthening :=
  ⟨rfl, rfl, rfl⟩

/-- Mechanism constraints: effect persists across semantically
heterogeneous NPIs (different base forces) and without domain
widening. The heterogeneity that matters for the non-scalar argument
is in baseForce (existential vs temporal vs degree), not in scalar
direction — all three are strengthening per @cite{israel-2001}. -/
theorem mechanism_constraints :
    exp1_npi_NM.significant = true ∧
    atAll.baseForce ≠ any.baseForce ∧
    exp3_npi_NM_controlled.significant = true ∧
    ever.baseForce ≠ any.baseForce :=
  ⟨rfl, by decide, rfl, by decide⟩

/-- Predict NPI significance from signature. -/
def predictNPIEffect (env : MonotonicityEnv) : Bool :=
  match envSignature env with
  | none => true
  | some _ => false

/-- Predict PPI significance from signature. -/
def predictPPIEffect (env : MonotonicityEnv) : Bool :=
  match envSignature env with
  | some sig => match EntailmentSig.toUEStrength sig with
    | some .weak => false
    | some _ => true
    | none => false
  | none => false

/-- NPI prediction matches all 4 experimental environments. -/
theorem npi_prediction_matches_data :
    predictNPIEffect .NM = exp1_npi_NM.significant ∧
    predictNPIEffect .DN = exp1_npi_DN.significant ∧
    predictNPIEffect .UE = exp1_npi_UE.significant ∧
    predictNPIEffect .DE = exp1_npi_DE.significant :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- PPI prediction matches all 4 experimental environments. -/
theorem ppi_prediction_matches_data :
    predictPPIEffect .NM = exp1_ppi_NM.significant ∧
    predictPPIEffect .DN = exp1_ppi_DN.significant ∧
    predictPPIEffect .UE = exp1_ppi_UE.significant ∧
    predictPPIEffect .DE = exp1_ppi_DE.significant := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Algebraic predictions agree with all 8 empirical data points. -/
theorem experiment1_predictions_match :
    experiment1.all (fun f =>
      (match f.piCondition with
       | .npi => predictNPIEffect f.environment
       | .ppi => predictPPIEffect f.environment
       | _ => f.significant) == f.significant) = true := by
  native_decide

/-- Observed pattern matches signature-based predictions. -/
theorem observed_pattern_matches_predictions :
    observedPattern.npi_affects_NM = predictNPIEffect .NM ∧
    observedPattern.npi_affects_DN = predictNPIEffect .DN ∧
    observedPattern.ppi_affects_NM = predictPPIEffect .NM ∧
    observedPattern.ppi_affects_DN = predictPPIEffect .DN := by
  exact ⟨by native_decide, rfl, by native_decide, by native_decide⟩

/-- Shift directions match PI polarity. -/
theorem shift_directions_match_pi_polarity :
    exp1_npi_NM.shiftDirection = some .DE ∧
    exp1_npi_NM.piCondition = .npi ∧
    exp1_ppi_DN.shiftDirection = some .UE ∧
    exp1_ppi_DN.piCondition = .ppi :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Significant findings' environments match predicted environments. -/
theorem significant_findings_environments :
    exp1_npi_NM.environment = .NM ∧
    exp1_ppi_DN.environment = .DN :=
  ⟨rfl, rfl⟩

/-- Mechanism verdict linked to data file. -/
theorem mechanism_verdict_linked :
    exp3_verdict.mechanism = .scalarSideEffect ∧
    exp3_verdict.ruledOutAsSole = true :=
  ⟨rfl, rfl⟩

/-- NPI items match Fragment lexicon entries by surface form. -/
theorem npi_items_match_fragment :
    npiItemsTested = [any.form, ever.form, atAll.form] := rfl

end DenicEtAl2021
