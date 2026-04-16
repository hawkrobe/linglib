import Linglib.Core.Modality.ModalIndefinite
import Linglib.Theories.Semantics.Modality.EventRelativity
import Linglib.Theories.Semantics.Modality.ModalIndefinites
import Linglib.Phenomena.Causation.Studies.Coon2019
import Linglib.Fragments.Chuj.ModalIndefinites
import Linglib.Fragments.Spanish.ModalIndefinites
import Linglib.Fragments.German.ModalIndefinites
import Linglib.Fragments.French.ModalIndefinites
import Linglib.Fragments.Italian.ModalIndefinites

/-!
# Modal Indefinites: Cross-Linguistic Typology & Event-Relative Anchoring
@cite{alonso-ovalle-royer-2024} @cite{alonso-ovalle-menendez-benito-2010}
@cite{alonso-ovalle-menendez-benito-2018} @cite{coon-2019} @cite{hacquard-2006}
@cite{alonso-ovalle-royer-2021}
@cite{chierchia-2013} @cite{jayez-tovena-2006} @cite{kratzer-shimoyama-2002}

Cross-linguistic typology of modal indefinites and bridge theorems connecting
the event-relative modality theory (@cite{hacquard-2006}, formalized in
`Theories/Semantics/Modality/EventRelativity`) to empirical observations.

Lexical entries are defined in Fragment files (single source of truth):
- `Fragments/Chuj/ModalIndefinites.lean`: *yalnhej*, *komon*
- `Fragments/Spanish/ModalIndefinites.lean`: *algún*, *uno cualquiera*
- `Fragments/German/ModalIndefinites.lean`: *irgendein*
- `Fragments/French/ModalIndefinites.lean`: *n'importe quel*
- `Fragments/Italian/ModalIndefinites.lean`: *un qualsiasi*

## Architecture

The key contribution of @cite{alonso-ovalle-royer-2024} is DERIVING the
position-sensitive flavor distribution of Chuj *yalnhej* from structural
properties of event binding, rather than stipulating it lexically:

    ChujArgPosition → accessibleBinders → miAnchorFlavor → predictedMIFlavors

1. Syntactic position determines which `EventBinder`s are accessible
2. Each binder projects a specific MI flavor via `AnchorType.toFlavor`
3. RC (random choice) additionally requires verb volitionality

## Three Dimensions of Variation (§6)

1. **Status**: at-issue vs not-at-issue
2. **Content**: which modal flavors
3. **Upper-boundedness**: anti-singleton inference

## Anchor Constraint (§4)

At-issue modal indefinites are further distinguished by their
`AnchorConstraint`: whether the anchoring function f has no definedness
condition (unrestricted — defined for any event) or presupposes normative
content (volitional-only). The anchor constraint controls where f CAN
anchor; content licensing independently determines the resulting flavor.

## Anchor Freedom (§4.1, footnote 17)

A-O&R depart from @cite{hacquard-2006} in one key respect: the event
argument of *yalnhej*'s anchoring function can be "left free" — bound
by the existential closure of the speech act event rather than by the
closest event binder. In Hacquard's system, modals are always bound by
the closest c-commanding event binder; *yalnhej* allows non-local
binding, which is how external arguments (above AspP) still access the
speech event despite intervening projections.

-/

namespace AlonsoOvalleRoyer2024

open Core.Modality (ModalFlavor)
open Core.ModalIndefinite
open Semantics.Modality.EventRelativity
open Fragments.Chuj.ModalIndefinites
open Fragments.Spanish.ModalIndefinites
open Fragments.German.ModalIndefinites
open Fragments.French.ModalIndefinites
open Fragments.Italian.ModalIndefinites


-- ════════════════════════════════════════════════════════════════
-- Part I: Cross-Linguistic Typology
-- ════════════════════════════════════════════════════════════════


-- ════════════════════════════════════════════════════
-- § 1. All Entries
-- ════════════════════════════════════════════════════

def allEntries : List ModalIndefiniteEntry :=
  [yalnhejEntry, komonEntry, algúnEntry, irgendeinEntry,
   unoCualquieraEntry, nimporteQuelEntry, unQualsiasiEntry]

theorem allEntries_count : allEntries.length = 7 := rfl


-- ════════════════════════════════════════════════════
-- § 2. Typological Generalizations (§6)
-- ════════════════════════════════════════════════════

/-- Chuj *yalnhej* and German *irgendein* share the same flavor
inventory (epistemic + random choice) but differ in status. -/
theorem yalnhej_irgendein_same_flavors :
    yalnhejEntry.flavors = irgendeinEntry.flavors := rfl

theorem yalnhej_irgendein_differ_in_status :
    yalnhejEntry.status ≠ irgendeinEntry.status := by decide

/-- The at-issue / not-at-issue split (§6.1). -/
theorem at_issue_items :
    [yalnhejEntry, unoCualquieraEntry, nimporteQuelEntry, unQualsiasiEntry].all
      (·.status == .atIssue) = true := rfl

theorem not_at_issue_items :
    [algúnEntry, irgendeinEntry].all (·.status == .notAtIssue) = true := rfl

/-- Upper-bounded items are a proper subset: only *algún* and
*uno cualquiera* impose anti-singleton inferences. -/
theorem upper_bounded_items :
    (allEntries.filter (·.upperBounded)).length = 2 := rfl

/-- *Yalnhej* is the only item that is both at-issue AND has both
epistemic and random choice flavors. This is the core empirical
contribution of @cite{alonso-ovalle-royer-2024}. -/
theorem yalnhej_unique_profile :
    (allEntries.filter (λ e =>
      e.status == .atIssue && e.hasEpistemic && e.hasCircumstantial)).length = 1 := rfl


-- ════════════════════════════════════════════════════
-- § 3. Independence of Dimensions
-- ════════════════════════════════════════════════════

/-- The three dimensions are logically independent: we find items in
multiple cells of the 2×2 (status × upper-bounded) matrix. -/
theorem at_issue_and_ub_exists :
    allEntries.any (λ e => e.status == .atIssue && e.upperBounded) = true := rfl
  -- uno cualquiera

theorem at_issue_and_not_ub_exists :
    allEntries.any (λ e => e.status == .atIssue && !e.upperBounded) = true := rfl
  -- yalnhej

theorem not_at_issue_and_ub_exists :
    allEntries.any (λ e => e.status == .notAtIssue && e.upperBounded) = true := rfl
  -- algún

theorem not_at_issue_and_not_ub_exists :
    allEntries.any (λ e => e.status == .notAtIssue && !e.upperBounded) = true := rfl
  -- irgendein


-- ════════════════════════════════════════════════════
-- § 4. AnchorConstraint Bridge
-- ════════════════════════════════════════════════════

/-- Consistency check: at-issue status aligns with anchor constraint
across all entries. At-issue items use event-relative anchoring
(`anchorConstraint = some _`); not-at-issue items use different
mechanisms (conversational implicature for *algún*, domain widening
for *irgendein*) and have `anchorConstraint = none`. This is true
by construction of the entries — verifying we encoded the paper's
§4 classification correctly. -/
theorem at_issue_iff_anchored :
    allEntries.all (λ e =>
      (e.status == .atIssue) == e.anchorConstraint.isSome) = true := rfl

/-- Volitional-only anchor constraint correlates with lacking epistemic:
*uno cualquiera*'s f requires normative content, blocking speech
event anchoring (speech acts lack normative content). -/
theorem volitional_blocks_epistemic :
    unoCualquieraEntry.anchorConstraint = some .volitionalOnly ∧
    unoCualquieraEntry.hasEpistemic = false := ⟨rfl, rfl⟩

/-- Unrestricted anchor constraint is necessary but not sufficient for
epistemic: *yalnhej* gets epistemic because f is defined for the
speech event, but *n'importe quel* and *un qualsiasi* are unrestricted
yet only have circumstantial (their lexical semantics restricts to
indiscriminacy/FC readings). -/
theorem unrestricted_with_epistemic :
    yalnhejEntry.anchorConstraint = some .unrestricted ∧
    yalnhejEntry.hasEpistemic = true := ⟨rfl, rfl⟩

theorem unrestricted_without_epistemic :
    nimporteQuelEntry.anchorConstraint = some .unrestricted ∧
    nimporteQuelEntry.hasEpistemic = false := ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- Part II: Position-Sensitive Flavor Distribution
-- ════════════════════════════════════════════════════════════════


-- ════════════════════════════════════════════════════
-- § 5. Structural Position and Accessible Binders
-- ════════════════════════════════════════════════════

/-- Structural position of a DP in the Chuj clause.
    Factored from verb volitionality (an orthogonal property of the
    predicate, not of the structural position). -/
inductive ChujArgPosition where
  /-- External argument (above vP): subject of transitive -/
  | external
  /-- Internal argument (within vP): object, complement -/
  | internal
  /-- Adjunct (adjoined to vP): locative, manner, etc. -/
  | adjunct
  deriving DecidableEq, Repr

/-- Map structural position to accessible event binders.

External args are above vP: the closest event binder is the speech
act (or attitude) event. The VP event is inaccessible because the
external argument is merged above the aspectual projection that
binds the VP event variable.

Internal args and adjuncts are within/adjoined to vP: both the
speech act event and the VP event are structurally accessible. -/
def accessibleBinders : ChujArgPosition → List EventBinder
  | .external => [.speechAct]
  | .internal => [.speechAct, .vpEvent]
  | .adjunct  => [.speechAct, .vpEvent]


-- ════════════════════════════════════════════════════
-- § 6. MI Flavor Derivation via EventBinder
-- ════════════════════════════════════════════════════

/-- The MI flavor projected by a given event binder.
Speech act events project epistemic; VP events project circumstantial.
DERIVED from `EventBinder.toAnchorType` + `AnchorType.toFlavor`
(defined in EventRelativity.lean), not stipulated. -/
def miAnchorFlavor (b : EventBinder) : ModalFlavor :=
  b.toAnchorType.toFlavor

theorem speechAct_projects_epistemic :
    miAnchorFlavor .speechAct = .epistemic := rfl

theorem vpEvent_projects_circumstantial :
    miAnchorFlavor .vpEvent = .circumstantial := rfl

/-- Base MI flavors = one flavor per accessible binder, derived from
the EventBinder infrastructure in EventRelativity.
External: [epistemic]. Internal/adjunct: [epistemic, circumstantial]. -/
def baseMIFlavors (pos : ChujArgPosition) : List ModalFlavor :=
  (accessibleBinders pos).map miAnchorFlavor

/-- Whether the random choice (RC) reading is available.
RC requires TWO conditions:
(a) VP event is structurally accessible (internal or adjunct position)
(b) verb is volitional (decision subevent provides the anchoring point)

This captures @cite{alonso-ovalle-royer-2024}'s core structural explanation:
the RC flavor comes from the VP event, but only volitional events
contain a decision subevent that can serve as the anchor. -/
def rcAvailable (pos : ChujArgPosition) (volitional : Bool) : Bool :=
  (accessibleBinders pos).any (· == .vpEvent) && volitional

/-- Predicted MI flavors for a given position and volitionality.
When RC is not available, the circumstantial flavor (projected from
the VP event) is blocked, leaving only epistemic. -/
def predictedMIFlavors (pos : ChujArgPosition) (volitional : Bool) : List ModalFlavor :=
  if rcAvailable pos volitional then
    baseMIFlavors pos
  else
    (baseMIFlavors pos).filter (· != .circumstantial)


-- ════════════════════════════════════════════════════
-- § 7. Table 5 Verification
-- ════════════════════════════════════════════════════

/-- Table 5 DERIVED from structural position + volitionality + EventBinder.
The full five-cell pattern of @cite{alonso-ovalle-royer-2024} falls
out from three orthogonal components:
(1) `accessibleBinders` (structural position)
(2) `miAnchorFlavor` (EventBinder → ModalFlavor, from EventRelativity)
(3) `rcAvailable` (volitionality constraint) -/
theorem table5_derived :
    -- External arg: epistemic only (no VP event access → no RC)
    predictedMIFlavors .external true = [.epistemic] ∧
    predictedMIFlavors .external false = [.epistemic] ∧
    -- Internal arg, volitional: epistemic + RC
    predictedMIFlavors .internal true = [.epistemic, .circumstantial] ∧
    -- Internal arg, non-volitional: epistemic only
    predictedMIFlavors .internal false = [.epistemic] ∧
    -- Adjunct, volitional: epistemic + RC
    predictedMIFlavors .adjunct true = [.epistemic, .circumstantial] ∧
    -- Adjunct, non-volitional: epistemic only
    predictedMIFlavors .adjunct false = [.epistemic] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- External args: volitionality is irrelevant (no VP event access). -/
theorem external_volitionality_irrelevant :
    predictedMIFlavors .external true = predictedMIFlavors .external false := rfl

/-- Position matters: external ≠ internal flavor sets (with volitional verb). -/
theorem position_matters :
    predictedMIFlavors .external true ≠ predictedMIFlavors .internal true := by
  decide

/-- Volitionality matters: internal volitional ≠ internal non-volitional. -/
theorem volitionality_matters :
    predictedMIFlavors .internal true ≠ predictedMIFlavors .internal false := by
  decide

/-- Internal and adjunct pattern alike (same accessible binders). -/
theorem internal_adjunct_same (v : Bool) :
    predictedMIFlavors .internal v = predictedMIFlavors .adjunct v := by
  cases v <;> rfl


-- ════════════════════════════════════════════════════
-- § 8. Voice → Position → Binders → Flavors
-- ════════════════════════════════════════════════════

/-! The full derivation chain connecting Chuj clause structure to
MI flavor predictions:

    VoiceHead.hasD → argPosition → accessibleBinders → predictedMIFlavors

`hasD` is the structural claim: Voice heads with [D] introduce a
specifier in Spec,VoiceP (above vP, hence above AspP). This DP's
event variable is bound by the speech act event (e₀), not by Asp's
∃e₂. Voice heads without [D] have no specifier — the highest DP is
the internal argument (below AspP), accessible to both e₀ and e₂. -/

open Minimalism (VoiceHead) in

/-- Derive argument position from Voice head: [+D] → external (above
AspP), [-D] → internal (below AspP). This is the structural claim
that replaces the stipulated position mapping. -/
def argPositionOf (vh : VoiceHead) : ChujArgPosition :=
  if vh.hasD then .external else .internal

open Minimalism (VoiceHead) in

/-- End-to-end: Voice head determines MI flavor availability.
Given a Voice head and verb volitionality, predict the MI flavors
by composing the full derivation chain. -/
def predictedMIFlavorsOf (vh : VoiceHead) (volitional : Bool) : List ModalFlavor :=
  predictedMIFlavors (argPositionOf vh) volitional

open Coon2019 in

/-- The four Chuj voice heads yield the correct argument positions. -/
theorem voice_to_position :
    argPositionOf vØ = .external ∧
    argPositionOf v_w = .external ∧
    argPositionOf v_ch = .internal ∧
    argPositionOf v_j = .internal := ⟨rfl, rfl, rfl, rfl⟩

open Coon2019 in

/-- End-to-end flavor predictions for each Chuj voice head.
Active/antipassive (external arg): epistemic only.
Passive/agentless (internal arg, volitional): epistemic + RC. -/
theorem voice_to_flavors :
    predictedMIFlavorsOf vØ true = [.epistemic] ∧
    predictedMIFlavorsOf v_w true = [.epistemic] ∧
    predictedMIFlavorsOf v_ch true = [.epistemic, .circumstantial] ∧
    predictedMIFlavorsOf v_j true = [.epistemic, .circumstantial] :=
  ⟨rfl, rfl, rfl, rfl⟩

open Coon2019 in

/-- Non-volitional verbs block RC even in passive: only epistemic. -/
theorem voice_nonvolitional :
    predictedMIFlavorsOf v_ch false = [.epistemic] ∧
    predictedMIFlavorsOf v_j false = [.epistemic] := ⟨rfl, rfl⟩

/-- Connection to EventRelativity's `ModalPosition`: the MI's position
relative to AspP determines which binders are accessible, paralleling
how `ModalPosition` determines which event binder a modal auxiliary is
bound to. External = aboveAsp (speech act only), internal = belowAsp
(VP event accessible). -/
theorem argPosition_parallels_modalPosition :
    ModalPosition.aboveAsp.defaultBinder = .speechAct ∧
    ModalPosition.belowAsp.defaultBinder = .vpEvent ∧
    accessibleBinders .external = [.speechAct] ∧
    accessibleBinders .internal = [.speechAct, .vpEvent] := ⟨rfl, rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- Part III: Empirical Phenomena
-- ════════════════════════════════════════════════════════════════


-- ════════════════════════════════════════════════════
-- § 9. Non-Maximality (§3.2.4)
-- ════════════════════════════════════════════════════

/-- *Yalnhej* is not upper-bounded: compatible with partial-domain
scenarios where not all P are Q. This distinguishes it from maximal
free relatives (*whatever*), which require all domain members to
satisfy the scope. The EventRelativity worked example demonstrates
this concretely with `yalnhej_nonmaximal_ab` (ModalIndefinites.lean). -/
theorem yalnhej_nonmaximal :
    yalnhejEntry.upperBounded = false := rfl


-- ════════════════════════════════════════════════════
-- § 9b. Flavor Selectivity (§6.2)
-- ════════════════════════════════════════════════════

/-- Multi-flavor items: can express BOTH epistemic and RC.
@cite{alonso-ovalle-royer-2024}, §6.2: *yalnhej* and *irgendein*
tolerate more than one modal flavour. -/
theorem multi_flavor_items :
    (allEntries.filter (λ e =>
      e.hasEpistemic && e.hasCircumstantial)).length = 2 := rfl

/-- Epistemic-only items: *algún* conveys only speaker ignorance
(§6.2, example 118). -/
theorem epistemic_only_items :
    (allEntries.filter (λ e =>
      e.hasEpistemic && !e.hasCircumstantial)).length = 1 := rfl

/-- RC-only items: *uno cualquiera*, *n'importe quel*, *un qualsiasi*,
*komon* convey only random choice / indiscriminacy
(§6.2, examples 119–121). -/
theorem rc_only_items :
    (allEntries.filter (λ e =>
      !e.hasEpistemic && e.hasCircumstantial)).length = 4 := rfl


-- ════════════════════════════════════════════════════
-- § 10. Upper-Boundedness (§3.2.4, §6.2)
-- ════════════════════════════════════════════════════

/-- Upper-bounded modal indefinites impose an anti-singleton inference. -/
theorem upper_bounded_group :
    [algúnEntry, unoCualquieraEntry].all (·.upperBounded) = true := rfl

/-- Non-upper-bounded modal indefinites: no anti-singleton. -/
theorem not_upper_bounded_group :
    [yalnhejEntry, irgendeinEntry, nimporteQuelEntry, unQualsiasiEntry].all
      (·.upperBounded == false) = true := rfl


-- ════════════════════════════════════════════════════
-- § 11. Unremarkable Readings and Predicativity (§5)
-- ════════════════════════════════════════════════════

/-- Predicativity correlates with unremarkable readings across all
entries. Items that can appear in predicative position also have
non-modal ("unremarkable") readings. Derived directly from fragment
entry fields — no intermediate data structures needed. -/
theorem predicativity_correlates_unremarkable :
    allEntries.all (λ e =>
      e.canBePredicate == e.hasUnremarkableReading) = true := rfl

/-- Number-neutral items lack upper-boundedness. (Footnote 18 of
@cite{alonso-ovalle-royer-2024}, p.32, attributed to Louise McNally:
wh-phrase origin → number neutrality → incompatible with anti-singleton
inference, since anti-singleton presupposes a singleton alternative.) -/
theorem numberNeutral_implies_not_ub :
    (allEntries.filter (·.numberNeutral)).all (!·.upperBounded) = true := rfl

/-- *Yalnhej* lacks both predicative use and unremarkable readings. -/
theorem yalnhej_no_unremarkable :
    yalnhejEntry.hasUnremarkableReading = false ∧
    yalnhejEntry.canBePredicate = false := ⟨rfl, rfl⟩

/-- *Komon* has both (mass/plural modifier, can be predicative). -/
theorem komon_has_unremarkable :
    komonEntry.hasUnremarkableReading = true ∧
    komonEntry.canBePredicate = true := ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 12. Harmonic Interpretations (§4.3)
-- ════════════════════════════════════════════════════

/-! Under an external modal (imperative, deontic, attitude verb),
the MI's anchor can be co-indexed with the modal's event binder,
giving "any X is fine" readings (harmonic). When the anchor is
independent (bound to the described event), the result is "a random X"
(non-harmonic).

Same surface form, two readings:
- Non-harmonic: "Grab yalnhej card!" = grab a random card
  (MI anchored to described event → circumstantial/RC)
- Harmonic: "Grab yalnhej card!" = any card is fine
  (MI co-indexed with imperative event → permission domain)

The distinction maps directly to `EventBinder`:
- Non-harmonic anchor = vpEvent (aspect-bound)
- Harmonic anchor = speechAct or attitude (co-indexed with embedding modal) -/

/-- Non-harmonic anchoring: MI bound to VP event → circumstantial only.
VP events lack propositional content (content licensing). -/
theorem nonharmonic_is_vpEvent :
    EventBinder.vpEvent.canProjectEpistemic = false ∧
    EventBinder.vpEvent.canProjectCircumstantial = true := ⟨rfl, rfl⟩

/-- Harmonic anchoring: MI co-indexed with speech act → both flavors.
Speech acts are contentful (epistemic available). -/
theorem harmonic_is_speechAct :
    EventBinder.speechAct.canProjectEpistemic = true ∧
    EventBinder.speechAct.canProjectCircumstantial = true := ⟨rfl, rfl⟩

/-- The two readings are formally distinct: non-harmonic and harmonic
anchoring yield different available flavor profiles from the same MI,
explaining the ambiguity of *yalnhej* under imperatives. -/
theorem harmonic_neq_nonharmonic :
    EventBinder.vpEvent.availableFlavors ≠
    EventBinder.speechAct.availableFlavors := by decide


end AlonsoOvalleRoyer2024
