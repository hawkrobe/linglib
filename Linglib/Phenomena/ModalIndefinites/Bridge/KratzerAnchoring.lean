import Linglib.Theories.Semantics.Modality.EventRelativity
import Linglib.Theories.Semantics.Modality.ModalIndefinites
import Linglib.Phenomena.ModalIndefinites.Data
import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Fragments.Chuj.VerbBuilding
import Linglib.Fragments.Chuj.ModalIndefinites

/-!
# Bridge: Kratzer Anchoring ↔ Modal Indefinite Data
@cite{alonso-ovalle-royer-2024} @cite{coon-2019} @cite{hacquard-2006}

Connects the event-relative modality theory (@cite{hacquard-2006}, formalized in
`Theories/Semantics/Modality/EventRelativity`) to the empirical data on
modal indefinites (@cite{alonso-ovalle-royer-2024}, in `Phenomena/ModalIndefinites/Data`).

## Key Bridge Theorems

1. **Position → Anchor**: The syntactic position of the *yalnhej* DP
   determines which anchoring functions are semantically productive,
   which in turn determines the modal flavor.

2. **Anchor → Flavor**: Speech event anchoring yields epistemic modality;
   described event anchoring yields circumstantial/random choice.

3. **Volitionality**: The described event anchor only produces RC when
   the verb is volitional (has a decision subevent). Non-volitional
   verbs yield epistemic only even for internal arguments / adjuncts.

4. **Voice → Position**: The Chuj voice system (@cite{coon-2019}, formalized in
   `Fragments/Chuj/VerbBuilding`) determines whether a DP is external
   or internal, which feeds into (1).

5. **Cross-linguistic predictions**: The three-dimensional typology
   is instantiated with per-item bridge theorems.

-/

namespace Phenomena.ModalIndefinites.Bridge.KratzerAnchoring

open Semantics.Modality.EventRelativity
open Phenomena.ModalIndefinites.Data
open Core.ModalLogic (ModalFlavor)


-- ════════════════════════════════════════════════════
-- § 1. Position → Semantically Productive Anchors
-- ════════════════════════════════════════════════════

/-- Which anchor types are semantically productive given a syntactic
position (cross-classified with verb volitionality).

External arguments are structurally above the described event
(merged in Spec,VoiceP): they can only be anchored to the speech
event. Internal arguments and adjuncts of VOLITIONAL verbs can
be anchored to either event. Internal arguments and adjuncts of
NON-VOLITIONAL verbs only get speech event anchoring, because the
described event has no decision subevent to project normative
conditions from (§4.1).

This is A-O&R's core structural explanation for the
position-sensitivity of *yalnhej*'s modal flavor. -/
def availableAnchors : ChujDPPosition → List AnchorType
  | .externalArg => [.speechEvent]
  | .internalArgVolitional => [.speechEvent, .describedEvent]
  | .internalArgNonVolitional => [.speechEvent]
  | .adjunctVolitional => [.speechEvent, .describedEvent]
  | .adjunctNonVolitional => [.speechEvent]

/-- External arguments have only speech event anchoring. -/
theorem ext_arg_speech_only :
    availableAnchors .externalArg = [.speechEvent] := rfl

/-- Volitional internal arguments have both anchor types. -/
theorem int_arg_vol_both_anchors :
    availableAnchors .internalArgVolitional = [.speechEvent, .describedEvent] := rfl

/-- Non-volitional internal arguments have only speech event anchoring
    (§4.1, ex.66). -/
theorem int_arg_nonvol_speech_only :
    availableAnchors .internalArgNonVolitional = [.speechEvent] := rfl


-- ════════════════════════════════════════════════════
-- § 2. Anchor → Flavor (by construction)
-- ════════════════════════════════════════════════════

/-- The predicted flavors for a position = the flavors of its
available (semantically productive) anchor types. This connects the
structural account (position → anchor) to the observed flavors
(anchor → flavor). -/
def predictedFlavors (pos : ChujDPPosition) : List ModalFlavor :=
  (availableAnchors pos).map AnchorType.toFlavor

/-- Speech event anchor → epistemic flavor. -/
theorem speech_anchor_epistemic :
    AnchorType.speechEvent.toFlavor = .epistemic := rfl

/-- Described event anchor → circumstantial flavor (subsumes RC). -/
theorem described_anchor_circumstantial :
    AnchorType.describedEvent.toFlavor = .circumstantial := rfl


-- ════════════════════════════════════════════════════
-- § 3. Predictions match observed data
-- ════════════════════════════════════════════════════

/-- The anchoring theory predicts exactly the observed flavor
distribution for ALL five position types in Table 5. -/
theorem ext_arg_prediction :
    predictedFlavors .externalArg = [.epistemic] := rfl

theorem int_arg_vol_prediction :
    predictedFlavors .internalArgVolitional = [.epistemic, .circumstantial] := rfl

theorem int_arg_nonvol_prediction :
    predictedFlavors .internalArgNonVolitional = [.epistemic] := rfl

theorem adjunct_vol_prediction :
    predictedFlavors .adjunctVolitional = [.epistemic, .circumstantial] := rfl

theorem adjunct_nonvol_prediction :
    predictedFlavors .adjunctNonVolitional = [.epistemic] := rfl

/-- The predicted flavors match `yalnhejFlavorsAt` from the data file
for every position. This is the core bridge: the event-relative
anchoring theory derives the observed pattern. -/
theorem predictions_match_data :
    ∀ pos : ChujDPPosition,
      predictedFlavors pos = yalnhejFlavorsAt pos := by
  intro pos; cases pos <;> rfl


-- ════════════════════════════════════════════════════
-- § 4. Voice → Position (via Chuj voice system)
-- ════════════════════════════════════════════════════

/-- The active transitive voice (vØ) merges an overt agent (hasD = true)
as an external argument in Spec,VoiceP. Therefore a *yalnhej* DP in
agent position of a vØ-verb can only have epistemic modality. -/
theorem active_agent_is_external :
    Fragments.Chuj.vØ.hasD = true ∧
    predictedFlavors .externalArg = [.epistemic] :=
  ⟨rfl, rfl⟩

/-- The passive voice (-ch) has an implicit agent (hasD = false).
The theme is promoted to subject; a *yalnhej* DP as the internal
argument of a -ch (volitional) verb can have both epistemic and RC. -/
theorem passive_theme_is_internal :
    Fragments.Chuj.v_ch.hasD = false ∧
    predictedFlavors .internalArgVolitional = [.epistemic, .circumstantial] :=
  ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 5. Fragment → Profile Consistency
-- ════════════════════════════════════════════════════

open Fragments.Chuj.ModalIndefinites

/-- The fragment entry for *yalnhej* matches the data entry. -/
theorem fragment_matches_data_status :
    yalnhejEntry.status = yalnhej.status := rfl

theorem fragment_matches_data_flavors :
    yalnhejEntry.flavors = yalnhej.flavors := rfl

theorem fragment_matches_data_ub :
    yalnhejEntry.upperBounded = yalnhej.upperBounded := rfl


-- ════════════════════════════════════════════════════
-- § 6. Cross-Linguistic Bridge: Status Dimension
-- ════════════════════════════════════════════════════

/-- At-issue modal indefinites: the modal component is part of the
assertion. A-O&R's key diagnostic: direct denial targets the
modal content (§6.1). -/
theorem at_issue_group :
    [yalnhej, unoCualquiera, nimporteQuel, unQualsiasi].all
      (·.status == .atIssue) = true := by native_decide

/-- Not-at-issue modal indefinites: the modal component projects
(survives under negation, questions, modals). -/
theorem not_at_issue_group :
    [algún, irgendein].all (·.status == .notAtIssue) = true := by native_decide


-- ════════════════════════════════════════════════════
-- § 7. Cross-Linguistic Bridge: Upper-Boundedness
-- ════════════════════════════════════════════════════

/-- Upper-bounded modal indefinites impose an anti-singleton inference:
the speaker considers it possible that not all domain members satisfy
the scope predicate (§5). -/
theorem upper_bounded_group :
    [algún, unoCualquiera].all (·.upperBounded) = true := by native_decide

/-- Non-upper-bounded modal indefinites: no anti-singleton. -/
theorem not_upper_bounded_group :
    [yalnhej, irgendein, nimporteQuel, unQualsiasi].all
      (·.upperBounded == false) = true := by native_decide


-- ════════════════════════════════════════════════════
-- § 8. Independence of Dimensions
-- ════════════════════════════════════════════════════

/-- The three dimensions are logically independent: we find items in
multiple cells of the 2×2 (status × upper-bounded) matrix. -/
theorem at_issue_and_ub_exists :
    allEntries.any (λ e => e.status == .atIssue && e.upperBounded) = true := by
  native_decide  -- uno cualquiera

theorem at_issue_and_not_ub_exists :
    allEntries.any (λ e => e.status == .atIssue && !e.upperBounded) = true := by
  native_decide  -- yalnhej

theorem not_at_issue_and_ub_exists :
    allEntries.any (λ e => e.status == .notAtIssue && e.upperBounded) = true := by
  native_decide  -- algún

theorem not_at_issue_and_not_ub_exists :
    allEntries.any (λ e => e.status == .notAtIssue && !e.upperBounded) = true := by
  native_decide  -- irgendein


-- ════════════════════════════════════════════════════
-- § 9. Unremarkable Reading Bridge (§5)
-- ════════════════════════════════════════════════════

/-- *Yalnhej* lacks unremarkable readings (fragment entry agrees). -/
theorem yalnhej_lacks_unremarkable :
    yalnhejEntry.hasUnremarkableReading = false := rfl

/-- *Komon* has unremarkable readings (fragment entry agrees). -/
theorem komon_has_unremarkable :
    komonEntry.hasUnremarkableReading = true := rfl

/-- Predicativity correlates with unremarkable readings across all entries:
    every entry where canBePredicate = true also has unremarkable readings,
    and vice versa. This captures @cite{alonso-ovalle-royer-2024}'s (§5) generalization that
    predicativity enables plain existential readings. -/
theorem predicativity_correlates_unremarkable :
    allEntries.all (λ e =>
      e.canBePredicate == e.hasUnremarkableReading) = true := by native_decide


-- ════════════════════════════════════════════════════
-- § 10. Non-Maximality Bridge (§3.2.4)
-- ════════════════════════════════════════════════════

/-- *Yalnhej* is not upper-bounded: it does not require ¬∀P→Q.
    Non-upper-boundedness entails non-maximality (compatible with
    partial-domain scenarios) but not vice versa — non-maximality
    is a weaker property. The EventRelativity worked example
    (§6) demonstrates this concretely with `yalnhej_nonmaximal_ab`. -/
theorem yalnhej_nonmaximal :
    yalnhejEntry.upperBounded = false := rfl

/-- *Yalnhej* cannot be predicative, consistent with lacking
    unremarkable readings. -/
theorem yalnhej_not_predicative :
    yalnhejEntry.canBePredicate = false := rfl

/-- *Komon* can be predicative, consistent with having unremarkable
    readings. -/
theorem komon_predicative :
    komonEntry.canBePredicate = true := rfl


end Phenomena.ModalIndefinites.Bridge.KratzerAnchoring
