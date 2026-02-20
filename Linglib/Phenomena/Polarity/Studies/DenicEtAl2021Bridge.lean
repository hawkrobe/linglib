import Linglib.Phenomena.Polarity.Studies.DenicEtAl2021
import Linglib.Core.NaturalLogic
import Linglib.Fragments.English.PolarityItems

/-!
# Bridge: Denić et al. (2021) → Entailment Signatures & Polarity Items

Connects the empirical findings to:

1. `Core.NaturalLogic.EntailmentSig` — DN environments have a distinct
   signature from plain UE
2. `Core.NaturalLogic.ContextPolarity` — the three-valued coarsening
   erases empirically relevant information
3. `Fragments.English.PolarityItems` — the tested items are properly
   classified in the Fragment lexicon

## Derivation chain

The bridge proceeds in six layers:

1. **Environment–Signature Map** (§1): Formalizes the assumption that the
   paper's environments correspond to specific `EntailmentSig` values,
   and derives `isGloballyUE` from `toContextPolarity` rather than
   stipulating it.
2. **General Coarsening Theorem** (§2): Proves that `ContextPolarity`
   conflates ALL doubly-negative environments with simple UE, for any
   choice of DE components — not just pure double negation. The proof
   uses the monoid homomorphism `toContextPolarity_compose` structurally.
3. **UE Strength as the Discriminating Dimension** (§3): The algebraic
   distinction that `ContextPolarity` erases is captured by `toUEStrength`:
   DN has `.additive` UE strength while simple UE has `.weak`.
4. **Empirical Ground** (§4): The paper's PPI data empirically validates
   the algebraic distinction — PPI behavior is significant in exactly
   the environment whose UE strength differs from `.weak`.
5. **Prediction Functions** (§8): `predictNPIEffect` and `predictPPIEffect`
   derive significance from `envSignature` + `toUEStrength` alone. Both
   functions match all 8 data points and the `experiment1` list.
6. **Data File Connections** (§9): Links to `observedPattern`,
   `shiftDirection`, `environment` fields, `exp3_verdict`, and
   `npiItemsTested`, ensuring no data file structure is orphaned.

## Scalar direction heterogeneity

The paper's three NPIs are not uniform in scalar direction: *any* and *ever*
are strengthening, *at all* is attenuating (Israel 2011, Schwab 2022). The
paper aggregates across items. Whether scalar direction modulates the
bidirectional effect is an open question connecting to Schwab's NPI illusion
asymmetry (formalized in `Studies/Schwab2022.lean`).
-/

namespace Phenomena.Polarity.Studies.DenicEtAl2021.Bridge

open Core.NaturalLogic
open Phenomena.Polarity.Studies.DenicEtAl2021
open Fragments.English.PolarityItems

-- ============================================================================
-- §1. Environment–Signature Map
-- ============================================================================

/-- Map the paper's environments to canonical entailment signatures.

- UE = `.mono` (plain monotone — weakest UE signature)
- DE = `.antiAdd` ("no" is anti-additive in both restrictor and scope)
- DN = `.addMult` (pure double negation: ◇⊟ ∘ ◇⊟ = ⊕⊞)
- NM = `none` (non-monotone environments have no algebraic signature)

The exact DN signature depends on which DE operators are composed (see §2).
We use `.addMult` (pure double negation) as the canonical case; the
coarsening problem holds for any choice (Theorem `de_composed_is_ue`). -/
def envSignature : MonotonicityEnv → Option EntailmentSig
  | .UE => some .mono
  | .DE => some .antiAdd
  | .DN => some .addMult
  | .NM => none

/-- The DE environment maps to a DE-side signature. -/
theorem de_env_is_de :
    EntailmentSig.toContextPolarity .antiAdd = .downward := by
  native_decide

/-- `isGloballyUE` is *derived* from the signature map, not stipulated.

An environment is globally UE iff its signature (when it has one) maps to
`.upward` under `toContextPolarity`. NM returns `false` because it has no
signature — its monotonicity is indeterminate. -/
theorem isGloballyUE_from_signature (env : MonotonicityEnv) :
    env.isGloballyUE = match envSignature env with
      | some sig => EntailmentSig.toContextPolarity sig == ContextPolarity.upward
      | none => false := by
  cases env <;> native_decide

-- ============================================================================
-- §2. General coarsening theorem
-- ============================================================================

/-- Any composition of two DE-side signatures is UE under `ContextPolarity`.

This follows from the monoid homomorphism `toContextPolarity_compose`:
composing polarities gives `.downward.compose .downward = .upward`.
The proof is structural — it uses the homomorphism, not case analysis
on all 4×4 = 16 DE signature pairs.

This is why ALL doubly-negative environments — regardless of which specific
DE operators are composed — are invisible to `ContextPolarity`. -/
theorem de_composed_is_ue (φ ψ : EntailmentSig)
    (hφ : EntailmentSig.toContextPolarity φ = .downward)
    (hψ : EntailmentSig.toContextPolarity ψ = .downward) :
    EntailmentSig.toContextPolarity (φ * ψ) = .upward := by
  rw [EntailmentSig.toContextPolarity_compose, hφ, hψ]
  rfl

/-- `ContextPolarity` cannot distinguish ANY doubly-negative environment
from simple UE. Corollary of `de_composed_is_ue`. -/
theorem contextPolarity_blind_to_dn (φ ψ : EntailmentSig)
    (hφ : EntailmentSig.toContextPolarity φ = .downward)
    (hψ : EntailmentSig.toContextPolarity ψ = .downward) :
    EntailmentSig.toContextPolarity (φ * ψ) =
    EntailmentSig.toContextPolarity .mono := by
  rw [de_composed_is_ue φ ψ hφ hψ]
  native_decide

/-- `EntailmentSig` preserves DN–UE distinctions that `ContextPolarity` erases.
Not all DN compositions produce the same signature:
◇⊟ ∘ ◇⊟ = ⊕⊞ (additive + multiplicative) but ◇ ∘ ⊟ = ⊕ (additive only). -/
theorem dn_signatures_vary :
    EntailmentSig.compose .antiAddMult .antiAddMult ≠
    EntailmentSig.compose .antiAdd .antiMult := by native_decide

-- ============================================================================
-- §3. UE strength as the discriminating dimension
-- ============================================================================

/-- The algebraic dimension that `ContextPolarity` erases: UE strength.

DN (pure double negation) has `.additive` UE strength — it preserves
both directions of entailment AND distributes over ∨. Simple UE has only
`.weak` UE strength — it preserves entailment direction but nothing more.

`ContextPolarity` maps both to `.upward`. `toUEStrength` preserves the
difference. -/
theorem ue_strength_distinguishes_dn_ue :
    EntailmentSig.toUEStrength .addMult = some .additive ∧
    EntailmentSig.toUEStrength .mono = some .weak :=
  ⟨by native_decide, by native_decide⟩

/-- DN has no DE strength — it's globally UE. The local DE structure
within the composition is invisible to both `ContextPolarity` and
`toDEStrength`. -/
theorem dn_has_no_de_strength :
    EntailmentSig.toDEStrength .addMult = none := by
  native_decide

-- ============================================================================
-- §4. Empirical ground for the coarsening problem
-- ============================================================================

/-- Central theorem: the empirical PPI effect reveals a distinction that
`ContextPolarity` provably cannot make.

The algebraic part (conjunct 1) is universally quantified: no choice of
DE operators in the DN composition can produce a `ContextPolarity` value
different from simple UE's `.upward`. This uses the monoid homomorphism
structurally.

The UE strength part (conjunct 2) shows that `EntailmentSig` CAN make
the distinction, via `toUEStrength`.

The empirical part (conjuncts 3–4) shows PPI behavior does distinguish
DN from UE, confirming the lost information matters. -/
theorem ppi_reveals_coarsening_failure :
    -- Algebraic: ContextPolarity CANNOT distinguish any DN from simple UE
    (∀ φ ψ : EntailmentSig,
      EntailmentSig.toContextPolarity φ = .downward →
      EntailmentSig.toContextPolarity ψ = .downward →
      EntailmentSig.toContextPolarity (φ * ψ) =
        EntailmentSig.toContextPolarity .mono) ∧
    -- But EntailmentSig CAN (via UE strength)
    (EntailmentSig.toUEStrength .addMult ≠ EntailmentSig.toUEStrength .mono) ∧
    -- Empirical: PPI behavior distinguishes them
    exp1_ppi_DN.significant = true ∧
    exp1_ppi_UE.significant = false :=
  ⟨contextPolarity_blind_to_dn, by native_decide, rfl, rfl⟩

-- ============================================================================
-- §5. The complementary pattern and signature-based prediction
-- ============================================================================

/-- NPI effects target environments with no determinate signature.

NPIs are significant only in NM, the one environment that falls outside
the `EntailmentSig` lattice entirely. In environments with determinate
signatures (UE, DE, DN), NPI presence does not shift monotonicity
perception — the algebraic structure is too unambiguous to override. -/
theorem npi_targets_signatureless_env :
    -- NM has no signature
    envSignature .NM = none ∧
    -- NPI significant only in NM
    exp1_npi_NM.significant = true ∧
    exp1_npi_DN.significant = false ∧
    exp1_npi_UE.significant = false ∧
    exp1_npi_DE.significant = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- PPI effects target environments with composite UE signatures.

PPIs are significant only in DN, the one UE-side environment whose
signature differs from `.mono`. The UE strength hierarchy captures this:
DN has `.additive` UE strength (stronger than `.weak`) because it
preserves ∨-distributivity from its DE components. -/
theorem ppi_targets_composite_ue_env :
    -- DN has a UE-side signature that isn't .mono
    envSignature .DN = some EntailmentSig.addMult ∧
    EntailmentSig.addMult ≠ .mono ∧
    EntailmentSig.toUEStrength .addMult ≠ EntailmentSig.toUEStrength .mono ∧
    -- PPI significant only in DN
    exp1_ppi_DN.significant = true ∧
    exp1_ppi_UE.significant = false ∧
    exp1_ppi_DE.significant = false ∧
    exp1_ppi_NM.significant = false :=
  ⟨rfl, by decide, by native_decide, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §6. Fragment lexicon alignment
-- ============================================================================

-- These are cross-module consistency checks: if the Fragment lexicon is
-- updated to reclassify any of these items, these theorems break,
-- surfacing the inconsistency.

/-- The NPIs tested are classified as NPIs in the Fragment lexicon. -/
theorem tested_npis_are_npis :
    any.isNPI = true ∧ ever.isNPI = true ∧ atAll.isNPI = true :=
  ⟨rfl, rfl, rfl⟩

/-- The PPI tested is classified as a PPI in the Fragment lexicon. -/
theorem tested_ppi_is_ppi : some_ppi.isPPI = true := rfl

-- ============================================================================
-- §7. Scalar direction and mechanism constraints
-- ============================================================================

/-- The tested NPIs have heterogeneous scalar directions — the paper
aggregates across items with different scalar properties. Schwab (2022)
predicts strengthening and attenuating NPIs behave differently for NPI
illusions. Whether this modulates the bidirectional effect is untestable
from the reported (aggregated) data. -/
theorem scalar_direction_heterogeneity :
    any.scalarDirection = .strengthening ∧
    ever.scalarDirection = .strengthening ∧
    atAll.scalarDirection = .attenuating :=
  ⟨rfl, rfl, rfl⟩

/-- Despite heterogeneous scalar directions, the overall NPI effect in NM
is significant. Combined with Experiment 3 (non-domain-widening NPIs still
show the effect), this constrains mechanism: the bidirectional effect is
not solely driven by scalar semantics or domain widening. -/
theorem mechanism_constraints :
    -- Effect persists across scalar direction heterogeneity
    exp1_npi_NM.significant = true ∧
    atAll.scalarDirection ≠ any.scalarDirection ∧
    -- Effect persists without domain widening (Exp 3)
    exp3_npi_NM_controlled.significant = true ∧
    -- "Ever" is strengthening (not domain-widening) and still shows effect
    ever.scalarDirection = .strengthening :=
  ⟨rfl, by decide, rfl, rfl⟩

-- ============================================================================
-- §8. Signature-based predictions verified against data
-- ============================================================================

/-- Predict NPI significance from signature: significant iff no determinate
signature (the environment's monotonicity is genuinely ambiguous). -/
def predictNPIEffect (env : MonotonicityEnv) : Bool :=
  match envSignature env with
  | none => true
  | some _ => false

/-- Predict PPI significance from signature: significant iff UE-side
signature with non-weak UE strength (the environment is globally UE but
has internal DE structure inherited from its composition). -/
def predictPPIEffect (env : MonotonicityEnv) : Bool :=
  match envSignature env with
  | some sig => match EntailmentSig.toUEStrength sig with
    | some .weak => false
    | some _ => true
    | none => false
  | none => false

/-- NPI prediction matches all 4 experimental environments.
The prediction function uses only algebraic structure (`envSignature`);
the data comes from the empirical findings. -/
theorem npi_prediction_matches_data :
    predictNPIEffect .NM = exp1_npi_NM.significant ∧
    predictNPIEffect .DN = exp1_npi_DN.significant ∧
    predictNPIEffect .UE = exp1_npi_UE.significant ∧
    predictNPIEffect .DE = exp1_npi_DE.significant :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- PPI prediction matches all 4 experimental environments.
The prediction function uses `envSignature` + `toUEStrength` (algebraic);
the data comes from the empirical findings. -/
theorem ppi_prediction_matches_data :
    predictPPIEffect .NM = exp1_ppi_NM.significant ∧
    predictPPIEffect .DN = exp1_ppi_DN.significant ∧
    predictPPIEffect .UE = exp1_ppi_UE.significant ∧
    predictPPIEffect .DE = exp1_ppi_DE.significant := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- The prediction functions match every finding in `experiment1`.
This is the capstone: the algebraic prediction (from `envSignature` +
`toUEStrength`) agrees with all 8 empirical data points, verified
against the `experiment1` list rather than individual findings. -/
theorem experiment1_predictions_match :
    experiment1.all (fun f =>
      (match f.piCondition with
       | .npi => predictNPIEffect f.environment
       | .ppi => predictPPIEffect f.environment
       | _ => f.significant) == f.significant) = true := by
  native_decide

-- ============================================================================
-- §9. Connections to data file structures
-- ============================================================================

/-- The data file's `observedPattern` captures the same complementary
pattern that the signature-based predictions (§8) derive. This links the
data file's structural claim to the algebraic analysis. -/
theorem observed_pattern_matches_predictions :
    observedPattern.npi_affects_NM = predictNPIEffect .NM ∧
    observedPattern.npi_affects_DN = predictNPIEffect .DN ∧
    observedPattern.ppi_affects_NM = predictPPIEffect .NM ∧
    observedPattern.ppi_affects_DN = predictPPIEffect .DN := by
  exact ⟨by native_decide, rfl, by native_decide, by native_decide⟩

/-- The significant findings' `shiftDirection` fields are consistent with
the PI types' associated polarities: NPIs shift toward DE (their licensing
polarity), PPIs shift toward UE (theirs). The bridge connects the
`shiftDirection` and `piCondition` fields — not just `.significant`. -/
theorem shift_directions_match_pi_polarity :
    exp1_npi_NM.shiftDirection = some .DE ∧
    exp1_npi_NM.piCondition = .npi ∧
    exp1_ppi_DN.shiftDirection = some .UE ∧
    exp1_ppi_DN.piCondition = .ppi :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The significant findings' `environment` fields match the environments
the signature analysis predicts should show effects. -/
theorem significant_findings_environments :
    exp1_npi_NM.environment = .NM ∧
    exp1_ppi_DN.environment = .DN :=
  ⟨rfl, rfl⟩

/-- The data file's `exp3_verdict` (scalar side-effect ruled out as sole
mechanism) is the same claim captured by `mechanism_constraints` (§7). -/
theorem mechanism_verdict_linked :
    exp3_verdict.mechanism = .scalarSideEffect ∧
    exp3_verdict.ruledOutAsSole = true :=
  ⟨rfl, rfl⟩

/-- The NPI items listed in the data file match the Fragment lexicon entries
by surface form. -/
theorem npi_items_match_fragment :
    npiItemsTested = [any.form, ever.form, atAll.form] := rfl

-- Note: ppiItemTested = "some" but some_ppi.form = "some (stressed)".
-- The paper's PPI is stressed SOME (not the weak determiner); the data
-- file records the base lexeme while the Fragment disambiguates the
-- prosodic form. A future cleanup should reconcile these.

-- NM environments fall outside the `EntailmentSig` lattice entirely (they
-- have no algebraic signature), which is why `ContextPolarity.nonMonotonic`
-- exists as a separate value. The NPI effect in NM is thus not about
-- shifting between signatures but about biasing the monotonicity
-- *computation* itself.

end Phenomena.Polarity.Studies.DenicEtAl2021.Bridge
