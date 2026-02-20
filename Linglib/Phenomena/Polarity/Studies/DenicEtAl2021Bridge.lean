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

## The coarsening problem

`ContextPolarity` has three values: `.upward`, `.downward`, `.nonMonotonic`.
The map `toContextPolarity` sends both DN (signature `.addMult`) and simple UE
(signature `.mono`) to `.upward`. This paper proves the lost information
matters: PPI behavior distinguishes DN from UE.

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
-- §1. DN and UE collapse under ContextPolarity
-- ============================================================================

/-- Double negation (◇⊟ ∘ ◇⊟) yields the morphism signature ⊕⊞. -/
theorem dn_composition :
    EntailmentSig.compose .antiAddMult .antiAddMult = .addMult := by
  native_decide

/-- DN maps to `.upward` — indistinguishable from simple UE. -/
theorem dn_polarity_is_upward :
    EntailmentSig.toContextPolarity .addMult = .upward := by
  native_decide

/-- `ContextPolarity` conflates DN and simple UE. -/
theorem contextPolarity_conflates_dn_and_ue :
    EntailmentSig.toContextPolarity .addMult =
    EntailmentSig.toContextPolarity .mono := by
  native_decide

/-- `EntailmentSig` preserves the distinction that `ContextPolarity` erases. -/
theorem entailmentSig_distinguishes_dn_ue :
    EntailmentSig.addMult ≠ EntailmentSig.mono := by decide

-- ============================================================================
-- §2. Empirical evidence that the distinction matters
-- ============================================================================

/-- The paper's central finding for `ContextPolarity`: PPI behavior
distinguishes DN from UE, even though both are `.upward`.

Any PI-licensing theory that uses `ContextPolarity` alone will fail to
predict the PPI effect in DN environments. -/
theorem ppi_distinguishes_what_contextPolarity_conflates :
    -- Both map to .upward...
    EntailmentSig.toContextPolarity .addMult = .upward ∧
    EntailmentSig.toContextPolarity .mono = .upward ∧
    -- ...but PPI behavior differs between them
    exp1_ppi_DN.significant = true ∧
    exp1_ppi_UE.significant = false :=
  ⟨by native_decide, by native_decide, rfl, rfl⟩

/-- NPI behavior mirrors the complementary pattern: NPIs affect NM
(which is outside the `EntailmentSig` lattice entirely) but not DN or UE
(which are both `.upward` under `ContextPolarity`). -/
theorem npi_effect_targets_nonmonotone :
    exp1_npi_NM.significant = true ∧
    exp1_npi_DN.significant = false ∧
    exp1_npi_UE.significant = false ∧
    exp1_npi_DE.significant = false :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §3. Fragment lexicon connection
-- ============================================================================

/-- The NPIs tested are classified as NPIs in the Fragment lexicon. -/
theorem tested_npis_are_npis :
    any.isNPI = true ∧ ever.isNPI = true ∧ atAll.isNPI = true :=
  ⟨rfl, rfl, rfl⟩

/-- The PPI tested is classified as a PPI in the Fragment lexicon. -/
theorem tested_ppi_is_ppi : some_ppi.isPPI = true := rfl

-- ============================================================================
-- §4. Scalar direction heterogeneity
-- ============================================================================

/-- The tested NPIs have heterogeneous scalar directions.
*any* and *ever* are strengthening; *at all* is attenuating. Schwab (2022)
predicts these classes behave differently for NPI illusions. The paper
aggregates across items, so we cannot tell from the reported data whether
scalar direction modulates the bidirectional effect. -/
theorem scalar_direction_heterogeneity :
    any.scalarDirection = .strengthening ∧
    ever.scalarDirection = .strengthening ∧
    atAll.scalarDirection = .attenuating :=
  ⟨rfl, rfl, rfl⟩

/-- Despite heterogeneous scalar directions, the overall NPI effect in NM
is significant. Either scalar direction doesn't modulate this effect, or
the strengthening items dominate the aggregate. -/
theorem npi_effect_despite_heterogeneity :
    exp1_npi_NM.significant = true ∧
    atAll.scalarDirection ≠ any.scalarDirection :=
  ⟨rfl, by decide⟩

-- ============================================================================
-- §5. Experiment 3 and domain widening
-- ============================================================================

/-- "Ever" has strengthening scalar direction but no domain-widening
semantics (it modifies temporal extent, not nominal domains). The NPI
effect persists with such items, challenging the scalar side-effect
hypothesis as the sole explanation. -/
theorem exp3_domain_widening_not_necessary :
    ever.scalarDirection = .strengthening ∧
    exp3_npi_NM_controlled.significant = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- §6. Connection to the Zwarts/Icard DE hierarchy
-- ============================================================================

/-- DN environments have no DE strength — they're globally UE. This is
expected: `toDEStrength` returns `none` for all UE-side signatures.
The DN environment's local DE structure is invisible to both
`ContextPolarity` and `toDEStrength`. -/
theorem dn_has_no_de_strength :
    EntailmentSig.toDEStrength .addMult = none := by
  native_decide

-- NM environments fall outside the `EntailmentSig` lattice entirely (they
-- have no algebraic signature), which is why `ContextPolarity.nonMonotonic`
-- exists as a separate value. The NPI effect in NM is thus not about
-- shifting between signatures but about biasing the monotonicity
-- *computation* itself.

end Phenomena.Polarity.Studies.DenicEtAl2021.Bridge
