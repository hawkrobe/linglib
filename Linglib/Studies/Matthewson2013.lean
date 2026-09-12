import Linglib.Semantics.Modality.ModalTypes
import Linglib.Fragments.Gitksan.Modals
import Linglib.Fragments.NezPerce.Modals
import Linglib.Studies.Condoravdi2002
import Linglib.Semantics.Modality.ActualityEntailments

/-!
# Matthewson (2013): Gitksan Modals

This file formalizes three claims of [matthewson-2013] about the Gitksan modal system.
Gitksan is a mixed system: it encodes modal strength in the circumstantial domain, where
*da'akhlxw* and *sgi* differ in force, but not in the epistemic domain, where *imaa* and
*gat* are variable in force. Its modals have no inherent future orientation, which comes from
the prospective marker *dim*, obligatory with circumstantial modals and optional with
epistemics, against the English analysis of [condoravdi-2002] in which prospectivity is part
of *may*. And *da'akhlxw* shows no actuality entailment, since its obligatory *dim* blocks
the perfective configuration that [hacquard-2006] predicts to yield one.

## Implementation notes

The modal inventory is the Gitksan fragment; the negation diagnostic separating the
variable-force analysis of *imaa* from the strengthened-possibility analysis of Nez Perce
*o'qa* by [deal-2011] is recorded by label only. The handbook chapter [matthewson-2016]
restates the survey-level claims.

## TODO

The paper is not on file; figure, section, and example locators are transcribed from an
earlier version of this file and are UNVERIFIED.

## References

* [matthewson-2013]
* [condoravdi-2002]
* [hacquard-2006]
* [deal-2011]
-/

namespace Matthewson2013

open Gitksan.Modals
open Modality (ForceAnalysis TemporalPerspective TemporalOrientation)

-- ============================================================================
-- §1. Mixed-system thesis (Fig. 1)
-- ============================================================================

/-- [matthewson-2013] Fig. 1: `daakhlxw` is fixed possibility. -/
@[simp] theorem forceAnalysis_daakhlxw :
    forceAnalysis daakhlxw = .fixed .possibility := rfl

/-- [matthewson-2013] Fig. 1, §4.3: `sgi` is fixed weak necessity. -/
@[simp] theorem forceAnalysis_sgi :
    forceAnalysis sgi = .fixed .weakNecessity := rfl

/-- [matthewson-2013] Fig. 1, §3.1: `imaa` is variable-force
    (Peterson 2010 analysis). -/
@[simp] theorem forceAnalysis_imaa :
    forceAnalysis imaa = .variableForce := rfl

/-- [matthewson-2013] Fig. 1, §3.2: `gat` is variable-force
    (reportative). -/
@[simp] theorem forceAnalysis_gat :
    forceAnalysis gat = .variableForce := rfl

/-- The mixed-system signature: circumstantial modals contrast in force,
    epistemic modals do not. The asymmetric encoding pattern is the
    paper's central typological observation (Fig. 1). -/
theorem mixed_system :
    forceAnalysis daakhlxw ≠ forceAnalysis sgi ∧
    forceAnalysis imaa = forceAnalysis gat := ⟨by decide, rfl⟩

-- ============================================================================
-- §2. No inherent future orientation
-- ============================================================================

/-! The flavor-keyed dim asymmetry from §3-4 lives in
    `Fragments/Gitksan/Modals.lean` (`requiresDim_imaa_*`,
    `requiresDim_gat_*`, `requiresDim_circumstantial`,
    `dim_flavor_asymmetry`). The deeper structural claim — that
    Gitksan modals evaluate at the point rather than through
    `Condoravdi2002.MAY`'s forward interval — is currently expressed in the module
    docstring above; making it a typed compositional theorem requires
    promoting `dim` to a Theories-level operator. -/

-- ============================================================================
-- §3. No actuality entailments for da'akhlxw (§4.1, fn 32)
-- ============================================================================

/-! [hacquard-2006] predicts AEs in the configuration
    `belowAsp + perfective`. [matthewson-2013] reports da'akhlxw
    lacks AEs. Per [matthewson-2012]: da'akhlxw obligatorily
    co-occurs with prospective `dim`, blocking the perfective
    configuration empirically. -/

open Modality (actualityEntailmentPredicted)

/-- [hacquard-2006]'s AE prediction for the root + perfective cell. -/
@[simp] theorem hacquard_AE_root_perfective :
    actualityEntailmentPredicted .belowAsp .perfective = true := rfl

/-- [hacquard-2006]'s AE prediction for the root + imperfective cell. -/
@[simp] theorem hacquard_no_AE_root_imperfective :
    actualityEntailmentPredicted .belowAsp .imperfective = false := rfl

/-- [hacquard-2006]'s AE prediction for the epistemic + perfective cell. -/
@[simp] theorem hacquard_no_AE_epistemic_perfective :
    actualityEntailmentPredicted .aboveAsp .perfective = false := rfl

/-! The §4.1 fn 32 explanation, schematically: da'akhlxw's obligatory
    `dim` co-occurrence (via `requiresDim_circumstantial` in
    `Fragments/Gitksan/Modals.lean`) means the perfective configuration
    that drives Hacquard's AE prediction is empirically inaccessible
    for this modal. The full structural realization — `dim` as a typed
    combinator that *blocks* the perfective configuration — requires
    the planned `dim`-as-operator refactor; currently this is asserted
    via the requiresDim policy, not derived. -/

-- ============================================================================
-- §4. Peterson vs. Deal: variable-force vs. strengthened possibility
-- ============================================================================

/-! [matthewson-2013] §3.1 follows Peterson 2010 in analyzing imaa
    as variable-force. [deal-2011] analyzes Nez Perce *o'qa* as
    strengthened possibility. The two analyses agree both modals admit
    necessity readings but disagree on the mechanism. The downward-
    entailing diagnostic (paper ex. 30) is consistent with Peterson's
    analysis for imaa: negated imaa yields "possibly not", i.e., the
    modal scopes above negation. -/

/-- Peterson 2010: `imaa` is variable-force. -/
theorem peterson_imaa : forceAnalysis imaa = .variableForce := rfl

/-- Deal 2011: Nez Perce `o'qa` is strengthened possibility. -/
theorem deal_oqa :
    NezPerce.Modals.forceAnalysis NezPerce.Modals.oqa =
      .strengthened .possibility := rfl

/-- `imaa` admits necessity readings (variable force). -/
theorem imaa_admits_necessity : (forceAnalysis imaa).AdmitsNecessity := by decide

/-- `o'qa` admits necessity readings (pragmatically strengthened). -/
theorem oqa_admits_necessity :
    (NezPerce.Modals.forceAnalysis
      NezPerce.Modals.oqa).AdmitsNecessity := by decide

-- ============================================================================
-- §5. Figure 4 paradigm: temporal perspective × orientation for imaa
-- ============================================================================

/-! [matthewson-2013] Fig. 4 (p. 369) cross-tabulates temporal
    perspective (past/present) with temporal orientation (past/present/
    future) for the two epistemic modals. The two axes are the
    canonical `Modality.TemporalPerspective` and
    `Modality.TemporalOrientation` opened above. -/

/-- A Figure 4 cell: a temporal perspective × orientation pair, with
    the paper's example number for grounding. The dim-requirement is
    NOT stored — it is derived from the orientation via the flavor-keyed
    `requiresDim` policy. -/
structure Fig4Cell where
  perspective : TemporalPerspective
  orientation : TemporalOrientation
  /-- Example number in [matthewson-2013] Fig. 4. -/
  exampleNum : Nat
  deriving Repr

/-- Whether `dim` is required at this Fig. 4 cell, derived from the
    flavor-keyed policy on imaa (epistemic → required iff future). -/
def Fig4Cell.dimRequired (c : Fig4Cell) : Bool :=
  requiresDim imaa c.orientation

/-- The six cells of Figure 4 for imaa, with example numbers verified
    against the actual figure on p. 369. The figure also shows `gat`
    entries in the past-temporal-perspective row (47, 47, dim gat 48);
    those are not encoded here — this list is `imaa`-specific. The
    future-orientation cells (44, 42) are notated "ima('a) dim" in the
    figure, encoding the obligatory co-occurrence with prospective
    `dim` (which `Fig4Cell.dimRequired` recovers from `requiresDim`). -/
def fig4Cells : List Fig4Cell := [
  ⟨.present, .past,    29⟩,
  ⟨.present, .present, 22⟩,
  ⟨.present, .future,  42⟩,
  ⟨.past,    .past,    43⟩,
  ⟨.past,    .present, 37⟩,
  ⟨.past,    .future,  44⟩
]

end Matthewson2013
