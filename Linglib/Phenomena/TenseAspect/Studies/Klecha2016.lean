import Linglib.Core.Modality.HistoricalAlternatives
import Linglib.Theories.Semantics.Tense.Basic
import Linglib.Theories.Semantics.Tense.Modal.Matrix
import Linglib.Theories.Semantics.Modality.TemporalConstraint
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.Gitksan.Modals
import Linglib.Phenomena.Modality.Studies.Matthewson2013
import Linglib.Phenomena.Modality.Studies.Hacquard2006
import Linglib.Phenomena.TenseAspect.Studies.Sharvit2014

/-!
# @cite{klecha-2016}: Modality and Embedded Temporal Operators

Klecha's central result: the temporal orientation of embedded clauses under
attitude verbs is determined by the **modal base pronoun** (DOX vs. CIR),
not by the modal or attitude verb per se.

## Empirical puzzle

Under past-tense *think* (doxastic), embedded tense cannot be future-oriented:
- "Martina thought Carissa got pregnant" → RT ≤ thinking time

Under past-tense *hope* (preferential / CIR-compatible), embedded tense
can be future-oriented:
- "Martina hoped Carissa got pregnant" → RT > hoping time (CIR reading)

## Theoretical mechanism

1. DOX returns *actual histories* ending at the eval time → RT ≤ EvalT
   (Upper Limit Constraint derived from DOX's temporal character)
2. CIR returns *future histories* departing from the eval time → RT > EvalT
   (future orientation permitted)
3. Embedded tense (PAST or NPST) composes with the modal base constraint.
   The intersection determines what temporal orientations are available:
   DOX ∧ PAST = past; DOX ∧ NPST = simultaneous; CIR ∧ NPST = future;
   CIR ∧ PAST = impossible.

## What this file verifies

- Attitude verb classifications from `Fragments.English` derive the correct
  modal base compatibility
- *think*/*believe* are DOX-only (block future)
- *hope*/*pray* permit CIR (allow future)
- The Upper Limit Constraint follows from doxastic temporal character
- Hacquard's positional analysis is complementary: position determines
  WHAT time; modal base kind determines WHICH DIRECTION
- Table 1 modal-temporal correspondence via `ModalFlavor.toModalBaseKind`
- NPST is strictly weaker than present (key to the analysis)
- Hope ambiguity: DOX → past, CIR → future

-/

namespace Klecha2016

open Core.Verbs (Attitude Preferential Veridicality)
open Core.Modality (ModalBaseKind)
open Core.Modality.HistoricalAlternatives
  (WorldHistory actualHistoryBase futureHistoryBase
   upperLimitConstraintModal upperLimitConstraintModal_implies_value)
open Semantics.Modality.TemporalConstraint (attitudeTemporalConstraint
  doxConstrainsRT cirConstrainsRT Attitude.toModalBaseKind
  dox_compatible_with_past dox_incompatible_with_future cir_compatible_with_future
  permitsCirc_iff_cir ModalFlavor.toModalBaseKind
  epistemic_blocks_future circumstantial_permits_future deontic_permits_future
  non_epistemic_is_cir
  attitudeTemporalConstraint_derived_doxastic
  attitudeTemporalConstraint_derived_circumstantial)
open Fragments.English.Predicates.Verbal (think believe hope pray)
open Semantics.Tense.Modal.Matrix
  (dox_past_iff dox_npst_iff cir_npst_iff cir_past_iff_false)
open Semantics.Tense (upperLimitConstraint)
open Core.Time.Tense (GramTense)
open Core.Modality (ModalFlavor)


-- ════════════════════════════════════════════════════════════════
-- § 1. Attitude verb modal base classification
-- ════════════════════════════════════════════════════════════════

/-- *think* is classified as doxastic → DOX only. -/
theorem think_is_doxastic :
    think.attitude = some (.doxastic .nonVeridical) := rfl

/-- *believe* is classified as doxastic → DOX only. -/
theorem believe_is_doxastic :
    believe.attitude = some (.doxastic .nonVeridical) := rfl

/-- *hope* is classified as preferential → can take CIR. -/
theorem hope_is_preferential :
    hope.attitude = some (.preferential (.degreeComparison .positive)) := rfl

/-- *pray* is classified as preferential → can take CIR. -/
theorem pray_is_preferential :
    pray.attitude = some (.preferential (.degreeComparison .positive)) := rfl


-- ════════════════════════════════════════════════════════════════
-- § 2. Derived modal base compatibility
-- ════════════════════════════════════════════════════════════════

/-- *think*'s attitude blocks circumstantial modal base. -/
theorem think_blocks_cir :
    ¬ (Attitude.doxastic .nonVeridical).PermitsCircumstantial := fun h => h.elim

/-- *believe*'s attitude blocks circumstantial modal base. -/
theorem believe_blocks_cir :
    ¬ (Attitude.doxastic .nonVeridical).PermitsCircumstantial := fun h => h.elim

/-- *hope*'s attitude permits circumstantial modal base. -/
theorem hope_permits_cir :
    (Attitude.preferential (.degreeComparison .positive)).PermitsCircumstantial := trivial

/-- *pray*'s attitude permits circumstantial modal base. -/
theorem pray_permits_cir :
    (Attitude.preferential (.degreeComparison .positive)).PermitsCircumstantial := trivial


-- ════════════════════════════════════════════════════════════════
-- § 3. Modal base kind derivation
-- ════════════════════════════════════════════════════════════════

/-- *think*'s derived modal base kind is doxastic. -/
theorem think_modal_base :
    Attitude.toModalBaseKind (.doxastic .nonVeridical) = ModalBaseKind.doxastic := rfl

/-- *hope*'s derived modal base kind is circumstantial. -/
theorem hope_modal_base :
    Attitude.toModalBaseKind (.preferential (.degreeComparison .positive)) =
    ModalBaseKind.circumstantial := rfl


-- ════════════════════════════════════════════════════════════════
-- § 4. Temporal orientation predictions
-- ════════════════════════════════════════════════════════════════

/-! ### "Martina thought Carissa got pregnant"

Under *think* (DOX), the embedded past tense is genuine past: RT < thinking time.
Future-oriented readings are blocked. -/

/-- Past reading under *think* is compatible. -/
theorem thought_pregnant_past (thinkTime embRT : ℤ) (h : embRT < thinkTime) :
    attitudeTemporalConstraint .doxastic thinkTime embRT :=
  dox_compatible_with_past thinkTime embRT h

/-- Future reading under *think* is blocked. -/
theorem thought_pregnant_no_future (thinkTime embRT : ℤ) (h : embRT > thinkTime) :
    ¬ attitudeTemporalConstraint .doxastic thinkTime embRT :=
  dox_incompatible_with_future thinkTime embRT h


/-! ### "Martina hoped Carissa got pregnant"

Under *hope* (CIR), the "past" morphology on "got" is SOT agreement —
the embedded tense can be future-oriented: RT > hoping time.

But *hope* can also take DOX, giving a past-oriented reading:
"Martina hoped Carissa got pregnant" → RT < hoping time (DOX). -/

/-- Future reading under *hope* is permitted (via CIR). -/
theorem hoped_pregnant_future (hopeTime embRT : ℤ) (h : embRT > hopeTime) :
    attitudeTemporalConstraint .circumstantial hopeTime embRT :=
  cir_compatible_with_future hopeTime embRT h

/-- Past reading under *hope* is also permitted (via DOX). -/
theorem hoped_pregnant_past (hopeTime embRT : ℤ) (h : embRT < hopeTime) :
    attitudeTemporalConstraint .doxastic hopeTime embRT :=
  dox_compatible_with_past hopeTime embRT h


-- ════════════════════════════════════════════════════════════════
-- § 5. The Upper Limit Constraint is DERIVED
-- ════════════════════════════════════════════════════════════════

/-- The ULC is not a stipulated constraint — it follows from DOX's
    temporal character. Any doxastic attitude verb imposes RT ≤ EvalT,
    blocking future orientation. -/
theorem ulc_derived_from_dox (evalTime refTime : ℤ) :
    attitudeTemporalConstraint .doxastic evalTime refTime ↔
    refTime ≤ evalTime :=
  Iff.rfl

/-- The CIR temporal constraint is the complement: RT > EvalT. -/
theorem cir_is_future (evalTime refTime : ℤ) :
    attitudeTemporalConstraint .circumstantial evalTime refTime ↔
    refTime > evalTime :=
  Iff.rfl


-- ════════════════════════════════════════════════════════════════
-- § 5b. ULC derivation through the situation-base substrate
-- ════════════════════════════════════════════════════════════════

/-! The §5 theorems prove ULC via `Iff.rfl` against
`attitudeTemporalConstraint`'s definition. The two theorems below show
the same fact via the substrate path that @cite{klecha-2016} actually
uses: `actualHistoryBase` membership (Definition 3vi + eq 35a) →
constraint, by `.2` projection.

This is what differentiates Klecha's ULC from @cite{abusch-1997}'s
stipulated one — the upper limit is a kernel-checked consequence of
DOX-pronoun's lexical entry, not a separately-asserted presupposition
on T-nodes. The substrate derivation lives in
`Core.Modality.HistoricalAlternatives` (`actualHistoryBase_time_actual`,
`futureHistoryBase_time_future`); the `attitudeTemporalConstraint`
projection in `Theories/Semantics/Modality/TemporalConstraint.lean`
delegates to it. -/

/-- ULC at ℤ via `actualHistoryBase` membership: any embedded situation
    in the matrix evaluation point's actual-history base satisfies the
    doxastic temporal constraint. The proof is Klecha's eq 35a
    derivation specialized to ℤ. -/
theorem ulc_via_history_base {W : Type*}
    (history : WorldHistory W ℤ)
    (matrix embedded : Core.WorldTimeIndex W ℤ)
    (h : embedded ∈ actualHistoryBase history matrix) :
    attitudeTemporalConstraint .doxastic matrix.time embedded.time :=
  attitudeTemporalConstraint_derived_doxastic history matrix embedded h

/-- Future orientation at ℤ via `futureHistoryBase` membership: any
    embedded situation in the matrix evaluation point's future-history
    base satisfies the circumstantial temporal constraint. Klecha eq 35b
    specialized to ℤ. -/
theorem future_via_history_base {W : Type*}
    (history : WorldHistory W ℤ)
    (matrix embedded : Core.WorldTimeIndex W ℤ)
    (h : embedded ∈ futureHistoryBase history matrix) :
    attitudeTemporalConstraint .circumstantial matrix.time embedded.time :=
  attitudeTemporalConstraint_derived_circumstantial history matrix embedded h


-- ════════════════════════════════════════════════════════════════
-- § 5c. Klecha ↔ Abusch: ULC predicate convergence
-- ════════════════════════════════════════════════════════════════

/-! @cite{klecha-2016} §4.2 last paragraph: "[my] approach to the Upper
Limit Constraint is identical in spirit, if not in implementation, to
@cite{abusch-1997}'s. Abusch relies on the exact same motivation [...]
the future viewed as inherently unsettled and therefore unknowable."

The theorem below makes the predicate-level convergence kernel-checked:
Klecha's `attitudeTemporalConstraint .doxastic` and Abusch's
`upperLimitConstraint` are *definitionally equal* (modulo argument
order). Both reduce to `refTime ≤ evalTime`. The proof is `Iff.rfl`.

The substantive content is in the *proof routes*, not in the
proposition:

- **Klecha route** (kernel-checked in §5b): the predicate reaches `≤`
  via `actualHistoryBase_time_actual : s' ∈ actualHistoryBase history s
  → s'.time ≤ s.time`, a `.2`-projection through the situation-base
  definition. The doxastic-alternative quantification is carried by
  `WorldHistory W Time` membership.

- **Abusch route** (in `Theories/Semantics/Tense/Basic.lean`): the
  predicate is stated directly as `abbrev upperLimitConstraint
  embeddedR matrixE := embeddedR ≤ matrixE`. @cite{abusch-1997} §7
  states ULC informally; @cite{heim-1994-comments} formalizes it as a
  presupposition on T-nodes, endorsed by Abusch 1997 fn 20. The
  value-level reduction here strips the modal-alternative
  quantification ("now of an epistemic alternative").

So the equivalence is strict at the value level. **It is *not* strict
at the modal-layer level**: Klecha's substrate carries doxastic
alternatives via `WorldHistory`; Abusch's bare-`≤` form has dropped
them. A modal-layer `upperLimitConstraint` over `WorldHistory W Time`
matching Abusch's original "now of an epistemic alternative" is
deferred. -/

/-- Klecha's `attitudeTemporalConstraint .doxastic` and Abusch's
    `upperLimitConstraint` are definitionally equal predicates (modulo
    argument order). Both reduce to `refTime ≤ evalTime`.

    @cite{klecha-2016} §4.2: "identical in spirit, if not in
    implementation, to @cite{abusch-1997}'s [ULC]." This theorem makes
    the implementation-level equality kernel-checked. The substantive
    spirit-level difference (derivation vs. stipulation) is recorded
    in §5b above and in the docstring. -/
theorem klecha_dox_iff_abusch_ulc {Time : Type*} [LinearOrder Time]
    (evalTime refTime : Time) :
    attitudeTemporalConstraint .doxastic evalTime refTime ↔
    upperLimitConstraint refTime evalTime :=
  Iff.rfl


-- ════════════════════════════════════════════════════════════════
-- § 6. Compositional intersection: tense × modal base
-- ════════════════════════════════════════════════════════════════

/-! The central compositional predictions. Each cell in the 2×2
matrix (DOX/CIR × PAST/NPST) has a determinate temporal orientation.
These theorems instantiate the general results from `ModalTense` at ℤ. -/

/-- DOX + PAST = past: "Martina thought Carissa got pregnant" (genuine
    past reading). RT < thinking time. -/
theorem dox_past_gives_past (t r : ℤ) :
    attitudeTemporalConstraint .doxastic t r ∧ GramTense.constrains .past r t ↔
    r < t :=
  dox_past_iff t r

/-- DOX + NPST = simultaneous: "Martina thought Carissa was pregnant"
    where "was" = SOT agreement over NPST. RT = thinking time. -/
theorem dox_npst_gives_simultaneous (t r : ℤ) :
    attitudeTemporalConstraint .doxastic t r ∧ GramTense.constrains .nonpast r t ↔
    r = t :=
  dox_npst_iff t r

/-- CIR + NPST = future: "Martina hoped Carissa got pregnant" where
    "got" = SOT agreement over NPST + CIR. RT > hoping time. -/
theorem cir_npst_gives_future (t r : ℤ) :
    attitudeTemporalConstraint .circumstantial t r ∧ GramTense.constrains .nonpast r t ↔
    r > t :=
  cir_npst_iff t r

/-- CIR + PAST = impossible: no RT can be both > t (CIR) and < t (PAST). -/
theorem cir_past_is_impossible (t r : ℤ) :
    ¬(attitudeTemporalConstraint .circumstantial t r ∧ GramTense.constrains .past r t) :=
  (cir_past_iff_false t r).mp


-- ════════════════════════════════════════════════════════════════
-- § 7. NPST is not Present
-- ════════════════════════════════════════════════════════════════

/-! A key theoretical innovation: NPST (u ≤ t, i.e., ref ≥ perspective) is
strictly weaker than present (ref = perspective). This matters because NPST
includes future-oriented readings that present would exclude. -/

/-- Present entails nonpast: if ref = persp, then ref ≥ persp. -/
theorem present_implies_nonpast (r p : ℤ) (h : GramTense.constrains .present r p) :
    GramTense.constrains .nonpast r p :=
  ge_of_eq h

/-- Nonpast does not entail present: there exist r, p where ref ≥ persp
    but ref ≠ persp (namely, any future time). -/
theorem nonpast_strictly_weaker :
    ∃ r p : ℤ, GramTense.constrains .nonpast r p ∧
              ¬ GramTense.constrains .present r p := by
  exact ⟨1, 0, by simp [GramTense.constrains],
                by simp [GramTense.constrains]⟩


-- ════════════════════════════════════════════════════════════════
-- § 8. Table 1: Modal flavor → temporal orientation
-- ════════════════════════════════════════════════════════════════

/-! @cite{klecha-2016} Table 1 shows that epistemic modals
("She has to be home by now") are past/present-oriented, while
circumstantial/deontic/bouletic modals ("She has to be home tomorrow")
are future-oriented. This follows from `ModalFlavor.toModalBaseKind`. -/

/-- Epistemic "have to" blocks future orientation. -/
theorem epistemic_haveto_no_future :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .epistemic) .future = false :=
  epistemic_blocks_future

/-- Circumstantial "have to" permits future orientation. -/
theorem circumstantial_haveto_future :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .circumstantial) .future = true :=
  circumstantial_permits_future

/-- Deontic "have to" permits future orientation. -/
theorem deontic_haveto_future :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .deontic) .future = true :=
  deontic_permits_future

/-- Bouletic modals permit future orientation. -/
theorem bouletic_modal_future :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .bouletic) .future = true := rfl

/-- All non-epistemic flavors are CIR-like. -/
theorem non_epistemic_all_cir (f : ModalFlavor) (h : f ≠ .epistemic) :
    ModalFlavor.toModalBaseKind f = ModalBaseKind.circumstantial :=
  non_epistemic_is_cir f h


-- ════════════════════════════════════════════════════════════════
-- § 9. Reportatives pattern with doxastics
-- ════════════════════════════════════════════════════════════════

/-! @cite{klecha-2016} (80): "*I told John that it rains tomorrow"
is unacceptable — *tell* imposes an upper limit, patterning with
doxastic verbs. Reportatives use DOX, blocking future orientation. -/

/-- Reportatives (tell, say) impose the upper limit like doxastics:
    the future reading is blocked. -/
theorem reportative_blocks_future (tellTime embRT : ℤ) (h : embRT > tellTime) :
    ¬ attitudeTemporalConstraint .doxastic tellTime embRT :=
  dox_incompatible_with_future tellTime embRT h


-- ════════════════════════════════════════════════════════════════
-- § 10. Classification table
-- ════════════════════════════════════════════════════════════════

/-- Klecha's classification: attitude verbs and their temporal orientation
    predictions, derived from `Attitude.permitsCircumstantial`. -/
structure AttitudeOrientationDatum where
  verb : String
  isDoxOnly : Bool
  permitsULC : Bool     -- RT ≤ EvalT (always true for all verbs)
  permitsFuture : Bool  -- RT > EvalT (only when CIR available)
  deriving Repr, DecidableEq

def thinkDatum : AttitudeOrientationDatum :=
  { verb := "think", isDoxOnly := true, permitsULC := true, permitsFuture := false }

def believeDatum : AttitudeOrientationDatum :=
  { verb := "believe", isDoxOnly := true, permitsULC := true, permitsFuture := false }

def hopeDatum : AttitudeOrientationDatum :=
  { verb := "hope", isDoxOnly := false, permitsULC := true, permitsFuture := true }

def prayDatum : AttitudeOrientationDatum :=
  { verb := "pray", isDoxOnly := false, permitsULC := true, permitsFuture := true }

def classificationTable : List AttitudeOrientationDatum :=
  [thinkDatum, believeDatum, hopeDatum, prayDatum]

/-- DOX-only verbs all block future orientation. -/
theorem dox_only_block_future :
    (classificationTable.filter (·.isDoxOnly)).all (·.permitsFuture == false) = true := by
  decide

/-- CIR-compatible verbs all permit future orientation. -/
theorem cir_compat_permit_future :
    (classificationTable.filter (! ·.isDoxOnly)).all (·.permitsFuture) = true := by
  decide


-- ════════════════════════════════════════════════════════════════
-- § 11. Cross-linguistic test: @cite{matthewson-2013} Gitksan imaa
-- ════════════════════════════════════════════════════════════════

/-! Klecha's central universal — epistemic modals are DOX, and DOX
strictly blocks future orientation (§ 8) — predicts that no language
will have a felicitous "epistemic modal + future orientation"
configuration. @cite{matthewson-2013}'s Gitksan data is the obvious
test case: the variable-force epistemic *imaa* combines with the
prospective marker *dim* to produce future-oriented epistemic claims
(Fig. 4, ex. 42 and 44). The cross-framework outcome is *refutation*,
not reconciliation: the two analyses return different Bool values for
the (epistemic, future) cell, and there is no flavor-keyed
`ProspectiveMarkerPolicy` that would unify them. -/

open Fragments.Gitksan.Modals (imaa requiresDim)

/-- Klecha's universal applied to imaa: the flavor on every meaning
    cell of imaa is epistemic, so the modal base is DOX, so future
    orientation is blocked. -/
theorem klecha_predicts_imaa_no_future :
    imaa.meaning.all (fun ff =>
      ModalBaseKind.permitsOrientation
        (ModalFlavor.toModalBaseKind ff.flavor) .future = false) = true := by
  decide

/-- @cite{matthewson-2013} Fig. 4 records two future-orientation cells
    for `imaa`: TP=PRESENT × TO=FUTURE (ex. 42) and TP=PAST × TO=FUTURE
    (ex. 44). Both require `dim`. The empirical claim is that these
    configurations are felicitous, not blocked. -/
theorem matthewson_imaa_future_attested :
    Matthewson2013.fig4Cells.filter (fun c =>
      c.orientation == Core.Modality.TemporalOrientation.future)
      = [⟨.present, .future, 42⟩, ⟨.past, .future, 44⟩] := rfl

/-- The disagreement: Klecha predicts no felicitous future-oriented
    imaa configurations exist; Matthewson reports two (Fig. 4 cells
    ex. 42 and 44). The two frameworks return different Bool values
    for the (epistemic, future) cell — the disagreement is concrete
    and source-grounded. -/
theorem gitksan_imaa_refutes_universal :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .epistemic) .future ≠
    requiresDim imaa .future := by decide

/-! ### Architectural consequence

A unified Theories-level `ProspectiveMarkerPolicy : ModalFlavor →
TemporalOrientation → Bool` would have to pick one of the two values
for the (epistemic, future) cell:

- Klecha's value: `false` (DOX cannot extend forward).
- Matthewson's value: `true` (Gitksan imaa + dim is felicitous).

The picking is a cross-linguistic theoretical commitment, not a
structural primitive. Until other modal-system Fragments (Korean
*-keyss*, Mandarin *huì*, etc.) supply additional data points that
agree with one analysis or the other, the per-Fragment `requiresDim`
in `Fragments/Gitksan/Modals.lean` should stay where it is. Promoting
it to Theories would silently impose Klecha's universal on languages
whose data refutes it. -/


-- ════════════════════════════════════════════════════════════════
-- § F1. Phase F bridge: Klecha ↔ Sharvit on the simultaneous reading
-- ════════════════════════════════════════════════════════════════

/-! @cite{sharvit-2014} derives the simultaneous reading of past-under-past
in English attitudes via SOT-deletion of a *pronominal* past
(`LexicalType.pronominal` + `english.hasSOT = true` →
`english.simultaneousAttitudeReading = true` in
`Studies/Sharvit2014.lean`). @cite{klecha-2016} derives the same reading
via DOX + NPST modal-base composition (`dox_npst_iff` below).

Different mechanisms, same value-level prediction: `embeddedEventTime =
matrixEvalTime`. The bridge below witnesses both halves: (a) Sharvit's
typology Bool prediction for English, (b) Klecha's value-level Iff. -/

open Phenomena.TenseAspect.Studies.Sharvit2014 (english)

/-- Phase F bridge — Klecha-Sharvit agreement on the simultaneous reading
    for English. @cite{sharvit-2014}'s `english.simultaneousAttitudeReading`
    Bool fact and @cite{klecha-2016}'s `dox_npst_iff` value-level
    equivalence both witness the same prediction by different mechanisms
    (Sharvit: SOT-deletion of pronominal past; Klecha: DOX + NPST
    composition). -/
theorem sharvit_klecha_agree_simultaneous_english (sayingTime sickTime : ℤ) :
    english.simultaneousAttitudeReading = true ∧
    (attitudeTemporalConstraint .doxastic sayingTime sickTime ∧
      GramTense.constrains .nonpast sickTime sayingTime ↔
      sickTime = sayingTime) :=
  ⟨rfl, dox_npst_iff sayingTime sickTime⟩


-- ════════════════════════════════════════════════════════════════
-- § F2. Phase F bridge: Klecha CIR ⊆ Condoravdi metaphysical base
-- ════════════════════════════════════════════════════════════════

/-! @cite{condoravdi-2002}'s metaphysical modal base (formalized in
`Core/Modality/HistoricalAlternatives.lean` as `metaphysicalBase`)
quantifies over historical alternatives at the eval time.
@cite{klecha-2016}'s CIR modal base (`futureHistoryBase`) quantifies
over future-history situations whose world-component lies in the same
historical-alternatives equivalence class. The world-component of
Klecha's CIR is therefore a *subset* of Condoravdi's metaphysical base.

Klecha §1.1 (PDF p. 7) explicitly identifies metaphysical as a
"special case of the circumstantial modal base"; the present bridge
makes the world-component subset relation kernel-checked. -/

/-- Phase F bridge — Klecha-Condoravdi: the world-component of any
    situation in @cite{klecha-2016}'s CIR (`futureHistoryBase`) lies
    in @cite{condoravdi-2002}'s metaphysical modal base
    (`metaphysicalBase`). The proof is `.1` projection through the
    situation-base + structural unfolding of `metaphysicalBase` /
    `histEquiv`. -/
theorem klecha_cir_world_in_condoravdi_metaphysical
    {W : Type*} (history : WorldHistory W ℤ)
    (s s' : Core.WorldTimeIndex W ℤ)
    (h : s' ∈ futureHistoryBase history s) :
    s'.world ∈
      Core.Modality.HistoricalAlternatives.metaphysicalBase history s.world s.time :=
  h.1

/-- Phase F bridge — Klecha-Condoravdi: the world-component of any
    situation in @cite{klecha-2016}'s DOX (`actualHistoryBase`) lies
    in @cite{condoravdi-2002}'s metaphysical modal base. The proof is
    `.1` projection (same as the CIR case). -/
theorem klecha_dox_world_in_condoravdi_metaphysical
    {W : Type*} (history : WorldHistory W ℤ)
    (s s' : Core.WorldTimeIndex W ℤ)
    (h : s' ∈ actualHistoryBase history s) :
    s'.world ∈
      Core.Modality.HistoricalAlternatives.metaphysicalBase history s.world s.time :=
  h.1


-- ════════════════════════════════════════════════════════════════
-- § F4. Phase F bridge: Klecha ↔ Abusch ULC at the modal layer
-- ════════════════════════════════════════════════════════════════

/-! The 0.230.451 `klecha_dox_iff_abusch_ulc` (§5c above) was honest
about being shallow: both sides reduce to `≤` at the value level, but
the *modal layer* — quantification over doxastic alternatives that
@cite{abusch-1997}'s prose statement requires — was stripped on both
sides. With the new `upperLimitConstraintModal` substrate primitive
(in `Core/Modality/HistoricalAlternatives.lean`, F4), the modal-layer
bridge becomes statable.

@cite{abusch-1997}'s modal-layer ULC: an embedded situation lies in
the actual-history base of the matrix situation
(`actualHistoryBase` membership). @cite{klecha-2016}'s modal-layer
derivation: `attitudeTemporalConstraint_derived_doxastic` shows the
same membership produces the value-level constraint via `.2`
projection.

The bridge: both predicates ARE the same membership-in-base claim
(`Iff.rfl`), but the predicates' separate names carry their respective
paper attributions. The substantive content over §5c is that *both
sides* now carry the modal-alternative quantification (via
`s'.world ∈ history s`), not just the time-component projection. -/

/-- Phase F bridge — Klecha ↔ Abusch ULC at the modal layer:
    @cite{klecha-2016}'s modal-layer doxastic predicate (membership in
    `actualHistoryBase`) and @cite{abusch-1997}'s modal-layer ULC
    (`upperLimitConstraintModal`) are the same membership claim.
    Both carry the doxastic-alternative quantification at the modal
    layer, in contrast to §5c's value-level `klecha_dox_iff_abusch_ulc`
    which strips it. -/
theorem klecha_dox_iff_abusch_ulc_modal {W : Type*}
    (history : WorldHistory W ℤ)
    (matrix embedded : Core.WorldTimeIndex W ℤ) :
    embedded ∈ actualHistoryBase history matrix ↔
    upperLimitConstraintModal history matrix embedded :=
  Iff.rfl

/-- Phase F bridge — modal-layer ULC implies value-level constraint:
    if @cite{abusch-1997}'s modal-layer ULC holds for `(matrix,
    embedded)`, then @cite{klecha-2016}'s value-level
    `attitudeTemporalConstraint .doxastic` holds for the time
    components. Composes `upperLimitConstraintModal_implies_value`
    with the substrate's `attitudeTemporalConstraint_derived_doxastic`. -/
theorem abusch_modal_ulc_implies_klecha_dox {W : Type*}
    (history : WorldHistory W ℤ)
    (matrix embedded : Core.WorldTimeIndex W ℤ)
    (h : upperLimitConstraintModal history matrix embedded) :
    attitudeTemporalConstraint .doxastic matrix.time embedded.time :=
  attitudeTemporalConstraint_derived_doxastic history matrix embedded h


-- ════════════════════════════════════════════════════════════════
-- § F6. Phase F bridge: Klecha ↔ Hacquard 2006 complementarity
-- ════════════════════════════════════════════════════════════════

/-! @cite{klecha-2016}'s analysis is *complementary* to
@cite{hacquard-2006}'s positional account: position determines WHICH
TIME (high modal = speech time = present orientation; low modal =
event time = past orientation), modal base kind determines WHICH
DIRECTION (DOX blocks future, CIR permits future). The Klecha2016
docstring §4 (line 44) records the prose claim; this bridge makes
it kernel-checked.

@cite{hacquard-2006}'s `positionToOrientation` covers past + present
but is silent on future (the position-to-orientation map has no
future case). @cite{klecha-2016}'s `ModalBaseKind.permitsOrientation`
adds the future-orientation discriminator. Together they cover all
three orientations. -/

/-- Phase F bridge — Klecha-Hacquard complementarity:
    @cite{hacquard-2006}'s `positionToOrientation` covers past +
    present from modal position; @cite{klecha-2016}'s
    `ModalBaseKind.permitsOrientation` covers future from modal base
    kind. The conjunction below confirms the four cells:
    `(aboveAsp → present)`, `(belowAsp → past)`,
    `(circumstantial permits future)`, `(doxastic blocks future)`. -/
theorem klecha_hacquard_complementary :
    Hacquard2006.positionToOrientation .aboveAsp = .present ∧
    Hacquard2006.positionToOrientation .belowAsp = .past ∧
    ModalBaseKind.permitsOrientation .circumstantial .future = true ∧
    ModalBaseKind.permitsOrientation .doxastic .future = false := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> rfl


-- ════════════════════════════════════════════════════════════════
-- § F7. Phase F bridge: Klecha covers what Ogihara lacks (hope + past)
-- ════════════════════════════════════════════════════════════════

/-! The cross-framework auditor (0.230.453) flagged the genuine
Klecha-Ogihara divergence: not past-under-past (where they
*converge* — both predict simultaneous via Ogihara's zero-tense vs
Klecha's DOX+NPST), but *hope + past with future-oriented reading*.
@cite{klecha-2016}'s CIR+NPST mechanism (cell §6 above)
uniformly handles "Martina hoped Carissa got pregnant" with the
future-oriented reading; @cite{ogihara-1996}'s `PastReading` enum
classifies past morphology only and has no machinery for
future-under-modal.

The bridge below makes Klecha's coverage of the case kernel-checked.
@cite{ogihara-1996}'s silence is the *absence* of any theorem in
`Studies/Ogihara1996.lean` covering this configuration; that absence
is a substantive empirical claim about the scope of Ogihara's
mechanism. -/

/-- Phase F bridge — Klecha covers hope + past with future-oriented
    reading via CIR + NPST (cell §6 above); @cite{ogihara-1996}'s
    machinery does not. -/
theorem klecha_covers_hope_future_oriented_reading
    (hopeTime embRT : ℤ) (h : embRT > hopeTime) :
    attitudeTemporalConstraint .circumstantial hopeTime embRT ∧
    GramTense.constrains .nonpast embRT hopeTime :=
  ⟨cir_compatible_with_future hopeTime embRT h, le_of_lt h⟩


end Klecha2016
