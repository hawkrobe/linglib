import Linglib.Core.Presupposition
import Linglib.Core.ModalLogic
import Linglib.Theories.TruthConditional.Expressives.Basic

/-!
# Outlook Markers: Dual-Layered Secondary Meaning

Formalization of Kubota (2026) "Outlook Management: 'Subjective' Meanings of
Discourse-Sensitive Adverbs and Particles."

## Key Insight

Outlook markers (Japanese *nanka*, *dōse*, *mushiro*, *semete*, *koso*, etc.) are
discourse markers with **two-layered secondary meaning**:

1. **Presuppositional component**: requires a salient *counterstance* in the discourse
2. **Expressive-like component**: encodes the speaker's evaluative stance

This dual nature means outlook markers are *neither* pure CIs nor pure presuppositions,
but share properties of both — specifically:
- Like expressives: descriptive ineffability, immediacy
- Unlike expressives: lack independence and nondisplaceability (allow perspective shift)
- Like presuppositions: require discourse antecedent (counterstance)

## Three-Way Typology of Secondary Meaning (Kubota 2026: (14))

| Class | Examples | Key Property |
|-------|----------|-------------|
| Anaphoric presupposition triggers | pronouns, *mata* 'again' | Discourse-anchored, hard triggers |
| Lexical preconditions | *yameru* 'stop', *seikō-suru* 'succeed' | Soft triggers, overridable defaults |
| Discourse-sensitive modifiers | *nanka*, *mushiro*, *dōse*, *semete* | Outlook markers (this file) |

## References

- Kubota, Y. (2026). Outlook Management. In N. Kizu et al. (eds.), *Handbook of Japanese Semantics and Pragmatics*.
- Kubota, Y. & M. Ido (2026a,b). Outlook markers / contrastive *wa*.
- Coppock, E. (2018). Outlook-based semantics. *L&P* 41.
- Potts, C. (2007). The expressive dimension. *TL* 33(2).
- Farkas, D. & K. Bruce (2010). On reacting to assertions and polar questions. *JoS* 27.
-/

namespace TruthConditional.Expressives.OutlookMarker

open Core.Presupposition (PrProp)
open Core.ModalLogic (ModalFlavor)
open TruthConditional.Expressives (TwoDimProp CIExprProperties)


/-! ## Stance Classification -/

/-- The type of evaluative stance an outlook marker expresses.

Each stance type characterizes how the speaker situates the prejacent
relative to a salient counterstance in the discourse (Kubota 2026: §3). -/
inductive StanceType where
  /-- Negative/pessimistic evaluation: the prejacent is undesirable or implausible.
      E.g., *nanka* 'anything like', *dōse* 'anyway' -/
  | negative
  /-- Minimum standard: the prejacent is the least one could settle for.
      E.g., *semete* 'at least', *kurai* 'at least' -/
  | minimum
  /-- Contrary to expectation: the prejacent reverses the expected evaluation.
      E.g., *mushiro* 'rather', *kaette* 'rather', *yoppodo* 'much more' -/
  | contrary
  /-- Emphatic confirmation: the prejacent is precisely what's expected.
      E.g., *masani* 'precisely', *koso* 'precisely' -/
  | emphasis
  deriving DecidableEq, Repr, BEq, Inhabited


/-! ## Three-Way Typology of Secondary Meaning -/

/-- Classification of secondary (non-at-issue) meanings following Kubota (2026: (14)).

This typology cross-cuts the standard CI vs presupposition divide. Each class
exhibits different projection behavior, discourse sensitivity, and interaction
with attitude predicates. -/
inductive SecondaryMeaningClass where
  /-- Anaphoric presupposition triggers: pronouns, definites, clefts, additives (*too*).
      Presupposition anchored to prior discourse; cannot be overridden. "Hard triggers." -/
  | anaphoricPresup
  /-- Conditions on lexicalized concepts: aspectuals (*stop*), factives (*know*),
      implicatives (*manage*, *succeed*). "Soft triggers" — projectable default assumptions
      that can be overridden by epistemic uncertainty. -/
  | lexicalPrecondition
  /-- Discourse-sensitive modifiers and connectives: outlook markers, scalar adverbs
      (*almost*, *barely*), discourse particles (*doch*, *ja*), evidentials.
      Sensitive to discourse state; dual-layered meaning. -/
  | discourseSensitive
  deriving DecidableEq, Repr, BEq


/-! ## Presupposition Trigger Strength -/

/-- Hard vs soft presupposition triggers (Abusch 2002, 2010; Abrusán 2011).

Hard triggers project robustly in all embedding environments.
Soft triggers allow non-projective readings under epistemic uncertainty.

Kubota (2026: §2.3) shows that Japanese *mata* 'again' (hard) projects more
robustly than *yameru* 'stop' or *seikō-suru* 'succeed' (soft). -/
inductive TriggerStrength where
  /-- Projects robustly under questions, modals, conditionals.
      E.g., *mata* 'again', definites, clefts. -/
  | hard
  /-- Allows non-projective readings when speaker is epistemically uncertain.
      E.g., *yameru* 'stop', *seikō-suru* 'succeed', factives. -/
  | soft
  deriving DecidableEq, Repr, BEq


/-! ## Outlook Marker Semantics -/

/-- An outlook meaning combines a presuppositional and an expressive component.

The key innovation of Kubota & Ido (2026a,b): these two layers are not independently
stipulated but **fall out** from the marker's basic function as a counterstance marker.
The marker presupposes a salient counterstance in discourse, and the expressive-like
evaluation arises from the relationship between the prejacent and this counterstance.

For an outlook marker OM applied to prejacent p:
- `prejacent`: p (at-issue content, unchanged by the marker)
- `counterstance`: there exists a salient issue Q in the discourse to which p responds
- `stance`: the speaker's evaluative orientation toward Q vis-à-vis p -/
structure OutlookMeaning (W : Type*) where
  /-- At-issue content: same as the prejacent without the marker. -/
  prejacent : W → Bool
  /-- Presuppositional component: a salient counterstance exists in the discourse. -/
  counterstance : W → Bool
  /-- The type of evaluative stance expressed. -/
  stance : StanceType
namespace OutlookMeaning

variable {W : Type*}

/-- Extract the presuppositional layer as a `PrProp`.

The presupposition is the counterstance requirement; the assertion is the prejacent.
This connects outlook markers to the standard presupposition projection machinery. -/
def toPrProp (om : OutlookMeaning W) : PrProp W :=
  { presup := om.counterstance
  , assertion := om.prejacent }

/-- Extract the expressive layer as a `TwoDimProp`.

The at-issue content is the prejacent; the CI content is the counterstance
(that it is salient). Unlike pure CIs, this "CI" component is discourse-anchored
rather than being about the utterance situation per se. -/
def toTwoDimProp (om : OutlookMeaning W) : TwoDimProp W :=
  { atIssue := om.prejacent
  , ci := om.counterstance }

/-- Outlook markers do not change the prejacent's truth conditions.

This is Kubota's observation that omitting an outlook marker like *nanka* from (13a)
does not change the truth-conditional content of the sentence. -/
theorem atIssue_eq_prejacent (om : OutlookMeaning W) :
    om.toTwoDimProp.atIssue = om.prejacent := rfl

/-- The presupposition of an outlook marker is the counterstance requirement. -/
theorem presup_eq_counterstance (om : OutlookMeaning W) :
    om.toPrProp.presup = om.counterstance := rfl

end OutlookMeaning


/-! ## Diagnostic Properties

Potts (2007) identifies six properties of expressives. Kubota (2026) shows that
outlook markers share some but not all of these, which is what makes them a
distinct class of secondary meaning. -/

/-- Properties of a secondary meaning expression, extending Potts (2007: (27)).

These diagnostics distinguish outlook markers from both pure expressives
and pure presuppositions. -/
structure SecondaryMeaningProperties where
  /-- CI contributes to a dimension separate from at-issue content. -/
  independent : Bool
  /-- Predicates something of the utterance situation (not the described situation). -/
  nondisplaceable : Bool
  /-- Evaluated from a particular perspective (usually the speaker's). -/
  perspectiveDependent : Bool
  /-- Cannot be fully paraphrased by descriptive, non-expressive terms. -/
  descriptivelyIneffable : Bool
  /-- Achieves its effect simply by being uttered (like a performative). -/
  immediate : Bool
  /-- Repetition strengthens rather than creating redundancy. -/
  repeatable : Bool
  /-- Allows perspective shift to a non-speaker attitude holder under embedding. -/
  allowsPerspectiveShift : Bool
  /-- Requires a salient issue/counterstance in prior discourse. -/
  requiresDiscourseAntecedent : Bool
  deriving Repr

/-- Canonical properties of expressives (Potts 2007).

Expressives like epithets and honorifics satisfy all six Potts properties
and do NOT typically allow perspective shift or require discourse antecedents. -/
def expressiveProfile : SecondaryMeaningProperties :=
  { independent := true
  , nondisplaceable := true
  , perspectiveDependent := true
  , descriptivelyIneffable := true
  , immediate := true
  , repeatable := true
  , allowsPerspectiveShift := false   -- Potts' default; cf. Wang et al. 2005
  , requiresDiscourseAntecedent := false }

/-- Canonical properties of outlook markers (Kubota 2026: §3).

Outlook markers share descriptive ineffability and immediacy with expressives,
but crucially lack independence and nondisplaceability. They allow perspective
shift under attitude predicates (42) and require a discourse antecedent (37–38). -/
def outlookMarkerProfile : SecondaryMeaningProperties :=
  { independent := false              -- Meaning interacts with at-issue content (45–46)
  , nondisplaceable := false           -- Evaluation can pertain to embedded situation (42)
  , perspectiveDependent := true       -- Evaluated from speaker's (or attitude holder's) perspective
  , descriptivelyIneffable := true     -- Cannot be paraphrased descriptively (40–41)
  , immediate := true                  -- Effect arises from the word's use itself
  , repeatable := false                -- Not typically stackable like expressives
  , allowsPerspectiveShift := true     -- Shifts to attitude holder under embedding (42)
  , requiresDiscourseAntecedent := true }  -- Requires salient counterstance (37–38)

/-- Canonical properties of hard presupposition triggers (e.g., *mata* 'again'). -/
def hardPresupProfile : SecondaryMeaningProperties :=
  { independent := false
  , nondisplaceable := false
  , perspectiveDependent := false      -- Not perspective-dependent
  , descriptivelyIneffable := false    -- Can be paraphrased (e.g., "again" ↔ "did before")
  , immediate := false
  , repeatable := false
  , allowsPerspectiveShift := true     -- Anchored to local attitude holder (26)
  , requiresDiscourseAntecedent := true }  -- Anaphoric to prior discourse


/-! ## Key Theorems: What Outlook Markers Share With and How They Differ From Expressives -/

/-- Outlook markers share descriptive ineffability with expressives.

Kubota (2026: (40)–(41)): when B denies A's outlook-marked utterance, the denial
targets the propositional content, not the evaluative component. The negative
evaluation expressed by *nanka* or *dōse* is not what "no" targets. -/
theorem outlook_shares_descriptiveIneffability :
    outlookMarkerProfile.descriptivelyIneffable =
    expressiveProfile.descriptivelyIneffable := rfl

/-- Outlook markers share immediacy with expressives.

Both are meta-level effects tied to specific linguistic expressions that cannot
be paraphrased by descriptive, non-expressive terms. -/
theorem outlook_shares_immediacy :
    outlookMarkerProfile.immediate = expressiveProfile.immediate := rfl

/-- Outlook markers LACK independence (unlike expressives).

Kubota (2026: §3, discussing (42)–(43)): the evaluative meaning of outlook markers
interacts with the propositional content and can be attributed to a non-speaker
attitude holder, violating the independence criterion. -/
theorem outlook_lacks_independence :
    outlookMarkerProfile.independent = false ∧
    expressiveProfile.independent = true :=
  ⟨rfl, rfl⟩

/-- Outlook markers LACK nondisplaceability (unlike expressives).

Kubota (2026: (42)): under attitude embedding, *nanka*/*dōse* evaluate from
the attitude holder's (not the speaker's) perspective. -/
theorem outlook_lacks_nondisplaceability :
    outlookMarkerProfile.nondisplaceable = false ∧
    expressiveProfile.nondisplaceable = true :=
  ⟨rfl, rfl⟩

/-- Outlook markers REQUIRE discourse antecedent (unlike expressives).

Kubota (2026: (37)–(38)): *nanka* is felicitous only when a counterstance is
salient in the discourse; it is infelicitous as a response to a neutral *wh*-question
where no specific stance is at issue. -/
theorem outlook_requires_discourse_antecedent :
    outlookMarkerProfile.requiresDiscourseAntecedent = true ∧
    expressiveProfile.requiresDiscourseAntecedent = false :=
  ⟨rfl, rfl⟩

/-- Outlook markers ALLOW perspective shift (unlike default expressives).

Kubota (2026: (42)): "My advisor seems to have thought I wouldn't possibly get
accepted at SALT" — the negative evaluation is the advisor's, not the speaker's. -/
theorem outlook_allows_perspective_shift :
    outlookMarkerProfile.allowsPerspectiveShift = true ∧
    expressiveProfile.allowsPerspectiveShift = false :=
  ⟨rfl, rfl⟩

/-- Hard presuppositions differ from outlook markers in descriptive ineffability.

*Mata* 'again' presupposes "happened before" — this IS paraphrasable.
*Nanka* conveys negative stance — this is NOT paraphrasable. -/
theorem outlook_vs_hardPresup_ineffability :
    outlookMarkerProfile.descriptivelyIneffable = true ∧
    hardPresupProfile.descriptivelyIneffable = false :=
  ⟨rfl, rfl⟩


/-! ## Modal Selectional Restrictions

Kubota (2026: (45)–(46)) shows that outlook markers interact differently with
different modal flavors. This connects to Kratzer's conversational backgrounds. -/

/-- Modal flavors that an outlook marker is compatible with.

*semete* 'at least' is compatible with deontic *-beki* and desiderative *-tai*
but NOT with epistemic *hazu* or ability *-eru* (Kubota 2026: (46)).

This reflects the fact that minimum-standard outlook markers require that
the ordering source involve subjective preferences (deontic/bouletic), not
objective evidence (epistemic) or factual circumstances (circumstantial). -/
structure ModalCompatibility where
  /-- Compatible with epistemic modals (*hazu* 'supposed', *-eru* 'can/ability') -/
  epistemic : Bool
  /-- Compatible with deontic modals (*-beki* 'should') -/
  deontic : Bool
  /-- Compatible with circumstantial/ability modals -/
  circumstantial : Bool
  deriving Repr, BEq

/-- Check if a modal flavor is compatible with an outlook marker's selectional
    restrictions. -/
def ModalCompatibility.allows (mc : ModalCompatibility) : ModalFlavor → Bool
  | .epistemic => mc.epistemic
  | .deontic => mc.deontic
  | .circumstantial => mc.circumstantial

/-- *nanka* is compatible with all modal flavors, but the evaluative force
    varies: deontic/bouletic → pejorative, epistemic → more neutral (45). -/
def nanka_modalCompat : ModalCompatibility :=
  { epistemic := true, deontic := true, circumstantial := true }

/-- *semete* 'at least' selects for deontic/desiderative ordering sources.
    Incompatible with epistemic *hazu* and ability *-eru* (46a,b). -/
def semete_modalCompat : ModalCompatibility :=
  { epistemic := false, deontic := true, circumstantial := false }

/-- *semete* rejects epistemic modals. -/
theorem semete_rejects_epistemic :
    semete_modalCompat.allows .epistemic = false := rfl

/-- *semete* accepts deontic modals. -/
theorem semete_accepts_deontic :
    semete_modalCompat.allows .deontic = true := rfl

/-- *nanka* accepts all modal flavors (though evaluation force differs). -/
theorem nanka_accepts_all_modals :
    nanka_modalCompat.allows .epistemic = true ∧
    nanka_modalCompat.allows .deontic = true ∧
    nanka_modalCompat.allows .circumstantial = true :=
  ⟨rfl, rfl, rfl⟩


/-! ## Projection Behavior

Outlook markers exhibit both presuppositional and CI-like projection. The
counterstance requirement projects (like a presupposition), while the evaluative
stance projects (like a CI). This dual behavior is what makes them interesting. -/

/-- The counterstance requirement projects through negation.

If an outlook marker appears under negation, the counterstance is still presupposed.
This follows from the presuppositional layer (`PrProp.neg` preserves presupposition). -/
theorem counterstance_projects_through_neg {W : Type*} (om : OutlookMeaning W) :
    (PrProp.neg om.toPrProp).presup = om.counterstance := rfl

/-- The evaluative stance projects through negation (CI-like behavior).

This follows from the CI layer (`TwoDimProp.neg` preserves CI content). -/
theorem stance_projects_through_neg {W : Type*} (om : OutlookMeaning W) :
    (TwoDimProp.neg om.toTwoDimProp).ci = om.counterstance := rfl


end TruthConditional.Expressives.OutlookMarker
