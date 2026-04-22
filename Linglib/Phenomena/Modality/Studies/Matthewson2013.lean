import Linglib.Core.Modality.TemporalAxes
import Linglib.Fragments.Gitksan.Modals
import Linglib.Fragments.NezPerce.Modals
import Linglib.Phenomena.Modality.Studies.Condoravdi2002
import Linglib.Theories.Semantics.Modality.ActualityEntailments

/-!
# @cite{matthewson-2013} — Gitksan Modals

Lisa Matthewson. "Gitksan Modals." *International Journal of American
Linguistics* 79(3): 349–394. DOI: 10.1086/670751.

Primary source for the Gitksan modal analysis. Three core contributions
are formalized here against the existing infrastructure:

1. **Mixed-system thesis** (Fig. 1): Gitksan encodes modal STRENGTH in
   the circumstantial domain (`daakhlxw` vs. `sgi`) but not the epistemic
   domain (`imaa`/`gat` are variable-force).

2. **No inherent future orientation** (§3.3, §5.3): Gitksan modals are
   not lexically future-oriented. Future orientation comes from `dim`,
   *obligatory* with circumstantial modals and *optional* (only for
   future orientation) with epistemics. This contradicts
   @cite{condoravdi-2002}'s English analysis, where prospectivity is
   baked into `may`. Structurally: Gitksan *imaa* would be modeled with
   `Condoravdi2002.mayCore` (point evaluation), English *might* with
   `Condoravdi2002.may` (forward expansion). The relationship between
   them is `Condoravdi2002.may_of_mayCore_dynamic`. We do not introduce
   alias defs for the Gitksan/English projection here — that is a
   downstream choice that should land in a typed compositional `dim`
   operator (planned, see `ProspectiveMarkerPolicy` discussion in the
   integration audit).

3. **No actuality entailments for da'akhlxw** (§4.1, fn 32):
   @cite{hacquard-2006} predicts AEs for the perfective + root-modal
   configuration. da'akhlxw's obligatory co-occurrence with `dim`
   blocks that configuration empirically. The explanation is given
   in @cite{matthewson-2012}.

Supporting comparisons: Peterson 2010's variable-force analysis of
imaa contrasts with @cite{deal-2011}'s strengthened-possibility analysis
of Nez Perce *o'qa* (§3.1, ex. 30 negation diagnostic). The diagnostic
content (which scope ¬ takes relative to the modal) is *not* yet
formalized here — currently only the labels.

The modal inventory is in `Fragments/Gitksan/Modals.lean`. The handbook
chapter @cite{matthewson-2016} (`Studies/Matthewson2016.lean`) restates
the survey-level claims; this file holds the primary-source theorems
the chapter cites.
-/

namespace Matthewson2013

open Fragments.Gitksan.Modals
open Core.Modality (ForceAnalysis TemporalPerspective TemporalOrientation)

-- ============================================================================
-- §1. Mixed-system thesis (Fig. 1)
-- ============================================================================

/-- @cite{matthewson-2013} Fig. 1: `daakhlxw` is fixed possibility. -/
@[simp] theorem forceAnalysis_daakhlxw :
    forceAnalysis daakhlxw = .fixed .possibility := rfl

/-- @cite{matthewson-2013} Fig. 1, §4.3: `sgi` is fixed weak necessity. -/
@[simp] theorem forceAnalysis_sgi :
    forceAnalysis sgi = .fixed .weakNecessity := rfl

/-- @cite{matthewson-2013} Fig. 1, §3.1: `imaa` is variable-force
    (Peterson 2010 analysis). -/
@[simp] theorem forceAnalysis_imaa :
    forceAnalysis imaa = .variableForce := rfl

/-- @cite{matthewson-2013} Fig. 1, §3.2: `gat` is variable-force
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
    Gitksan modals project to `Condoravdi2002.mayCore` rather than
    `Condoravdi2002.may` — is currently expressed in the module
    docstring above; making it a typed compositional theorem requires
    promoting `dim` to a Theories-level operator. -/

-- ============================================================================
-- §3. No actuality entailments for da'akhlxw (§4.1, fn 32)
-- ============================================================================

/-! @cite{hacquard-2006} predicts AEs in the configuration
    `belowAsp + perfective`. @cite{matthewson-2013} reports da'akhlxw
    lacks AEs. Per @cite{matthewson-2012}: da'akhlxw obligatorily
    co-occurs with prospective `dim`, blocking the perfective
    configuration empirically. -/

open Semantics.Modality.ActualityEntailments (actualityEntailmentPredicted)

/-- @cite{hacquard-2006}'s AE prediction for the root + perfective cell. -/
@[simp] theorem hacquard_AE_root_perfective :
    actualityEntailmentPredicted .belowAsp .perfective = true := rfl

/-- @cite{hacquard-2006}'s AE prediction for the root + imperfective cell. -/
@[simp] theorem hacquard_no_AE_root_imperfective :
    actualityEntailmentPredicted .belowAsp .imperfective = false := rfl

/-- @cite{hacquard-2006}'s AE prediction for the epistemic + perfective cell. -/
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

/-! @cite{matthewson-2013} §3.1 follows Peterson 2010 in analyzing imaa
    as variable-force. @cite{deal-2011} analyzes Nez Perce *o'qa* as
    strengthened possibility. The two analyses agree both modals admit
    necessity readings but disagree on the mechanism. The downward-
    entailing diagnostic (paper ex. 30) is consistent with Peterson's
    analysis for imaa: negated imaa yields "possibly not", i.e., the
    modal scopes above negation. -/

/-- Peterson 2010: `imaa` is variable-force. -/
theorem peterson_imaa : forceAnalysis imaa = .variableForce := rfl

/-- Deal 2011: Nez Perce `o'qa` is strengthened possibility. -/
theorem deal_oqa :
    Fragments.NezPerce.Modals.forceAnalysis Fragments.NezPerce.Modals.oqa =
      .strengthened .possibility := rfl

/-- `imaa` admits necessity readings (variable force). -/
theorem imaa_admits_necessity : (forceAnalysis imaa).AdmitsNecessity := by decide

/-- `o'qa` admits necessity readings (pragmatically strengthened). -/
theorem oqa_admits_necessity :
    (Fragments.NezPerce.Modals.forceAnalysis
      Fragments.NezPerce.Modals.oqa).AdmitsNecessity := by decide

-- ============================================================================
-- §5. Figure 4 paradigm: temporal perspective × orientation for imaa
-- ============================================================================

/-! @cite{matthewson-2013} Fig. 4 (p. 369) cross-tabulates temporal
    perspective (past/present) with temporal orientation (past/present/
    future) for the two epistemic modals. The two axes are the
    canonical `Core.Modality.TemporalPerspective` and
    `Core.Modality.TemporalOrientation` opened above. -/

/-- A Figure 4 cell: a temporal perspective × orientation pair, with
    the paper's example number for grounding. The dim-requirement is
    NOT stored — it is derived from the orientation via the flavor-keyed
    `requiresDim` policy. -/
structure Fig4Cell where
  perspective : TemporalPerspective
  orientation : TemporalOrientation
  /-- Example number in @cite{matthewson-2013} Fig. 4. -/
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
