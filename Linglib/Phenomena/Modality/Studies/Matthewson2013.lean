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
   baked into `may`. The structural expression: Gitksan `imaa` projects
   to `Condoravdi2002.mayCore`, not `Condoravdi2002.may`.

3. **No actuality entailments for da'akhlxw** (§4.1, fn 32):
   @cite{hacquard-2006} predicts AEs for the perfective + root-modal
   configuration. da'akhlxw's obligatory co-occurrence with `dim`
   blocks that configuration empirically.

Supporting comparisons: Peterson 2010's variable-force analysis of
imaa contrasts with @cite{deal-2011}'s strengthened-possibility analysis
of Nez Perce *o'qa* (§3.1, ex. 30 negation diagnostic).

The modal inventory is in `Fragments/Gitksan/Modals.lean`. The handbook
chapter @cite{matthewson-2016} (`Studies/Matthewson2016.lean`) restates
the survey-level claims; this file holds the primary-source theorems
the chapter cites.
-/

namespace Matthewson2013

open Fragments.Gitksan.Modals
open Core.Modality (ForceAnalysis)

-- ============================================================================
-- §1. Mixed-system thesis (Fig. 1)
-- ============================================================================

/-- Force is encoded in the circumstantial domain: `daakhlxw` is fixed
    possibility, `sgi` is fixed weak necessity. -/
theorem circumstantial_force_encoded :
    forceAnalysis daakhlxw = .fixed .possibility ∧
    forceAnalysis sgi = .fixed .weakNecessity := ⟨rfl, rfl⟩

/-- Force is NOT encoded in the epistemic domain: both epistemic modals
    are variable-force. -/
theorem epistemic_force_not_encoded :
    forceAnalysis imaa = .variableForce ∧
    forceAnalysis gat = .variableForce := ⟨rfl, rfl⟩

/-- The mixed-system signature: circumstantial modals contrast in force,
    epistemic modals do not. -/
theorem mixed_system :
    forceAnalysis daakhlxw ≠ forceAnalysis sgi ∧
    forceAnalysis imaa = forceAnalysis gat := ⟨by decide, rfl⟩

-- ============================================================================
-- §2. No inherent future orientation: anti-Condoravdi via dim
-- ============================================================================

/-! @cite{matthewson-2013} §3-4 vs @cite{condoravdi-2002}: the
    prospective component is a separable combinator, not part of the
    modal lexical entry. -/

/-- The flavor-keyed dim asymmetry from §3-4: epistemics dispense with
    `dim` for past/present orientations; circumstantials require `dim`
    for any orientation. -/
theorem dim_asymmetry :
    requiresDim imaa .past = false ∧
    requiresDim imaa .present = false ∧
    requiresDim imaa .future = true ∧
    requiresDim daakhlxw .past = true ∧
    requiresDim daakhlxw .present = true ∧
    requiresDim daakhlxw .future = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-! ### Anti-Condoravdi: imaa underlying core is `mayCore`, not `may`

The structural claim: where @cite{condoravdi-2002} models English
*might* with `Condoravdi2002.may` (which contains `atForward`),
@cite{matthewson-2013} argues Gitksan *imaa* should use
`Condoravdi2002.mayCore` (point evaluation only). The two operators
differ exactly in the temporal evaluator. -/

/-- The modal-core signature, abstracting the temporal evaluator. -/
abbrev ModalCoreSig (W Time : Type*) [LinearOrder Time] :=
  (W → Time → Set W) → Core.Verbs.Dynamicity →
    Semantics.Tense.Aspect.Core.EventPred W Time → W → Time → Prop

/-- English *might* uses Condoravdi's prospective `may`. -/
def mightCore {W Time : Type*} [LinearOrder Time] : ModalCoreSig W Time :=
  Condoravdi2002.may

/-- Gitksan *imaa* uses Condoravdi's non-prospective `mayCore`. The
    prospective marker `dim` adds the `atForward` component when
    futurity is intended. -/
def imaaCore {W Time : Type*} [LinearOrder Time] : ModalCoreSig W Time :=
  Condoravdi2002.mayCore

/-- For dynamic prejacents, `imaaCore` implies `mightCore`: the
    pointwise instantiation entails forward expansion (cf.
    `Condoravdi2002.may_of_mayCore_dynamic`). The English modal is
    weaker because it is committed to prospectivity. -/
theorem mightCore_of_imaaCore_dynamic
    {W Time : Type*} [LinearOrder Time]
    (MB : W → Time → Set W) (P : Semantics.Tense.Aspect.Core.EventPred W Time)
    (w : W) (t : Time)
    (h : imaaCore MB .dynamic P w t) : mightCore MB .dynamic P w t :=
  Condoravdi2002.may_of_mayCore_dynamic MB P w t h

-- ============================================================================
-- §3. No actuality entailments for da'akhlxw (§4.1, fn 32)
-- ============================================================================

/-! @cite{hacquard-2006} predicts AEs in the configuration
    `belowAsp + perfective`. @cite{matthewson-2013} reports da'akhlxw
    lacks AEs. The explanation @cite{matthewson-2012} gives: da'akhlxw
    obligatorily co-occurs with prospective `dim`, blocking the
    perfective configuration. -/

/-- @cite{hacquard-2006}'s AE prediction: only root + perfective. -/
theorem hacquard_AE_only_root_perfective :
    Semantics.Modality.ActualityEntailments.actualityEntailmentPredicted
      .belowAsp .perfective = true ∧
    Semantics.Modality.ActualityEntailments.actualityEntailmentPredicted
      .belowAsp .imperfective = false ∧
    Semantics.Modality.ActualityEntailments.actualityEntailmentPredicted
      .aboveAsp .perfective = false := ⟨rfl, rfl, rfl⟩

/-- da'akhlxw's obligatory dim-co-occurrence (any orientation, any
    perspective) blocks the configuration that drives Hacquard's AE
    prediction. This is the structural shape of the §4.1 fn 32
    explanation: AEs are absent because the perfective configuration
    is never realized for this modal. -/
theorem daakhlxw_dim_blocks_AE_configuration :
    requiresDim daakhlxw .past = true ∧
    requiresDim daakhlxw .present = true ∧
    requiresDim daakhlxw .future = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

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

/-- The two contrasting force analyses. -/
theorem peterson_deal_contrast :
    forceAnalysis imaa = .variableForce ∧
    Fragments.NezPerce.Modals.forceAnalysis Fragments.NezPerce.Modals.oqa =
      .strengthened .possibility := ⟨rfl, rfl⟩

/-- Both analyses make necessity readings available. -/
theorem both_admit_necessity :
    (forceAnalysis imaa).AdmitsNecessity ∧
    (Fragments.NezPerce.Modals.forceAnalysis
      Fragments.NezPerce.Modals.oqa).AdmitsNecessity := by
  refine ⟨?_, ?_⟩ <;> decide

-- ============================================================================
-- §5. Figure 4 paradigm: temporal perspective × orientation for imaa
-- ============================================================================

/-! @cite{matthewson-2013} Fig. 4 cross-tabulates temporal perspective
    (past/present) with temporal orientation (past/present/future) for
    the two epistemic modals. Each cell is filled by an example
    number. The cells encode the dim-requirement empirically observed
    for each configuration. -/

inductive TemporalPerspective where
  | past | present
  deriving DecidableEq, Repr

/-- A Figure 4 cell: a temporal perspective × orientation pair, with
    the paper's example number for grounding and the empirically
    attested dim-requirement. -/
structure Fig4Cell where
  perspective : TemporalPerspective
  orientation : TemporalOrientation
  /-- Example number in @cite{matthewson-2013}. -/
  exampleNum : Nat
  /-- Whether `dim` is required in this configuration. -/
  dimRequired : Bool
  deriving Repr

/-- The six cells of Figure 4 for imaa, with example numbers verified
    against the actual figure on p. 369. The figure also shows `gat`
    entries in the past-temporal-perspective row (47, 47, dim gat 48);
    those are not encoded here — this struct is `imaa`-specific.

    The dim-requirement in each cell is the paper's empirical report;
    `fig4_consistent_with_requiresDim` proves these match the
    flavor-keyed predicate. The future-orientation cells (44, 42)
    are notated "ima('a) dim" in the figure, encoding the obligatory
    co-occurrence with prospective `dim`. -/
def fig4Cells : List Fig4Cell := [
  ⟨.present, .past,    29, false⟩,
  ⟨.present, .present, 22, false⟩,
  ⟨.present, .future,  42, true⟩,
  ⟨.past,    .past,    43, false⟩,
  ⟨.past,    .present, 37, false⟩,
  ⟨.past,    .future,  44, true⟩
]

/-- Each Fig 4 cell's empirical dim-requirement matches the flavor-keyed
    predicate: imaa requires `dim` iff orientation is future. -/
theorem fig4_consistent_with_requiresDim :
    fig4Cells.all (fun c => c.dimRequired == requiresDim imaa c.orientation)
      = true := by decide

end Matthewson2013
