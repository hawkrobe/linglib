import Linglib.Core.Modality.ModalIndefinite
import Linglib.Theories.Semantics.Modality.EventRelativity
import Linglib.Theories.Semantics.Modality.ModalIndefinites
import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Fragments.Chuj.VerbBuilding
import Linglib.Fragments.Chuj.ModalIndefinites
import Linglib.Fragments.Spanish.ModalIndefinites
import Linglib.Fragments.German.ModalIndefinites
import Linglib.Fragments.French.ModalIndefinites
import Linglib.Fragments.Italian.ModalIndefinites

/-!
# Modal Indefinites: Cross-Linguistic Typology & Kratzer Anchoring
@cite{alonso-ovalle-royer-2024} @cite{alonso-ovalle-menendez-benito-2010}
@cite{alonso-ovalle-menendez-benito-2018} @cite{coon-2019} @cite{hacquard-2006}
@cite{kratzer-shimoyama-2002b} @cite{alonso-ovalle-royer-2021}
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

## Three Dimensions of Variation (§6)

1. **Status**: Is the modal component at-issue or not-at-issue?
2. **Content**: Which modal flavors does the component support?
3. **Upper-boundedness**: Does the indefinite impose an anti-singleton
   inference (¬∀x[P(x) → Q(x)])?

## Key Bridge Theorems

1. **Position → Anchor**: The syntactic position of the *yalnhej* DP
   determines which anchoring functions are semantically productive.
2. **Anchor → Flavor**: Speech event → epistemic; described event → RC.
3. **Volitionality**: RC requires a volitional verb (decision subevent).
4. **Voice → Position**: Chuj voice system determines external/internal.
5. **Cross-linguistic predictions**: Three-dimensional typology instantiated.

-/

namespace Phenomena.ModalIndefinites.Studies.AlonsoOvalleRoyer2024

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

theorem allEntries_count : allEntries.length = 7 := by native_decide


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
      (·.status == .atIssue) = true := by native_decide

theorem not_at_issue_items :
    [algúnEntry, irgendeinEntry].all (·.status == .notAtIssue) = true := by native_decide

/-- Upper-bounded items are a proper subset: only *algún* and
*uno cualquiera* impose anti-singleton inferences. -/
theorem upper_bounded_items :
    (allEntries.filter (·.upperBounded)).length = 2 := by native_decide

/-- *Yalnhej* is the only item that is both at-issue AND has both
epistemic and random choice flavors. This is the core empirical
contribution of @cite{alonso-ovalle-royer-2024}. -/
theorem yalnhej_unique_profile :
    (allEntries.filter (λ e =>
      e.status == .atIssue && e.hasEpistemic && e.hasCircumstantial)).length = 1 := by
  native_decide


-- ════════════════════════════════════════════════════
-- § 3. Independence of Dimensions
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
-- § 4. Position-Sensitive Flavor Distribution (Table 5)
-- ════════════════════════════════════════════════════

/-- Syntactic positions for a DP in Chuj, cross-classified with
verb volitionality (§3–4, Table 5).

The paper shows that RC availability depends on TWO factors:
(1) structural position (external vs internal/adjunct), and
(2) whether the verb describes a volitional event (one containing
a decision subevent that can anchor RC modality). -/
inductive ChujDPPosition where
  /-- External argument (subject of transitive) -/
  | externalArg
  /-- Internal argument of a volitional verb (e.g., "buy") -/
  | internalArgVolitional
  /-- Internal argument of a non-volitional verb (e.g., "like") -/
  | internalArgNonVolitional
  /-- Adjunct of a volitional verb (e.g., "Malin ate where") -/
  | adjunctVolitional
  /-- Adjunct of a non-volitional verb (e.g., "it rained where") -/
  | adjunctNonVolitional
  deriving DecidableEq, BEq, Repr

/-- Which modal flavors are available to *yalnhej* in each position
(Table 5, §3.2–4.2). -/
def yalnhejFlavorsAt : ChujDPPosition → List ModalFlavor
  | .externalArg => [.epistemic]
  | .internalArgVolitional => [.epistemic, .circumstantial]
  | .internalArgNonVolitional => [.epistemic]
  | .adjunctVolitional => [.epistemic, .circumstantial]
  | .adjunctNonVolitional => [.epistemic]

theorem ext_arg_epistemic_only :
    yalnhejFlavorsAt .externalArg = [.epistemic] := rfl

theorem int_arg_vol_both_flavors :
    yalnhejFlavorsAt .internalArgVolitional = [.epistemic, .circumstantial] := rfl

theorem int_arg_nonvol_epistemic_only :
    yalnhejFlavorsAt .internalArgNonVolitional = [.epistemic] := rfl

/-- Position sensitivity: external ≠ volitional internal flavor sets. -/
theorem position_matters :
    yalnhejFlavorsAt .externalArg ≠ yalnhejFlavorsAt .internalArgVolitional := by
  decide

/-- Volitionality sensitivity: volitional ≠ non-volitional internal
    flavor sets (§4.1). -/
theorem volitionality_matters :
    yalnhejFlavorsAt .internalArgVolitional ≠ yalnhejFlavorsAt .internalArgNonVolitional := by
  decide


-- ════════════════════════════════════════════════════
-- § 5. Example Sentences
-- ════════════════════════════════════════════════════

/-- A Chuj *yalnhej* example sentence with empirical judgments. -/
structure YalnhejExample where
  chuj : String
  gloss : String
  position : ChujDPPosition
  availableFlavors : List ModalFlavor
  /-- Example number in @cite{alonso-ovalle-royer-2024} -/
  exampleNumber : String
  deriving Repr

def ex22_extArg : YalnhejExample where
  chuj := "[Yalnhej mach] ix-chanhalw-i t'a k'inh."
  gloss := "YALNHEJ who danced at the party"
  position := .externalArg
  availableFlavors := [.epistemic]
  exampleNumber := "(22)"

def ex31_intArgRC : YalnhejExample where
  chuj := "[Yalnhej tas libro'-al] ix-s-man waj Xun."
  gloss := "Xun bought YALNHEJ what book(s)"
  position := .internalArgVolitional
  availableFlavors := [.epistemic, .circumstantial]
  exampleNumber := "(31)"

def ex34_intArgNonVol : YalnhejExample where
  chuj := "[Yalnhej tas tek-al] ix-s-nib'-ej waj Xun."
  gloss := "Xun liked YALNHEJ what dish(es)"
  position := .internalArgNonVolitional
  availableFlavors := [.epistemic]
  exampleNumber := "(34)"

def ex41_adjunctRC : YalnhejExample where
  chuj := "[Yalnhej b'ajt'il] ix-wa' ix Malin."
  gloss := "Malin ate YALNHEJ where"
  position := .adjunctVolitional
  availableFlavors := [.epistemic, .circumstantial]
  exampleNumber := "(41)"

def ex39_adjunctNonVol : YalnhejExample where
  chuj := "[Yalnhej b'ajt'il] y-ak' nhab' ewi."
  gloss := "it rained YALNHEJ where yesterday"
  position := .adjunctNonVolitional
  availableFlavors := [.epistemic]
  exampleNumber := "(39)"

def allExamples : List YalnhejExample :=
  [ex22_extArg, ex31_intArgRC, ex34_intArgNonVol, ex41_adjunctRC, ex39_adjunctNonVol]

/-- Consistency: each example's available flavors match the position-based
    prediction from yalnhejFlavorsAt. -/
theorem examples_match_position_prediction :
    allExamples.all (λ ex => ex.availableFlavors == yalnhejFlavorsAt ex.position)
    = true := by native_decide


-- ════════════════════════════════════════════════════
-- § 6. Non-Maximality Data (§3.2.4)
-- ════════════════════════════════════════════════════

/-! Yalnhej is compatible with partial-domain scenarios, unlike
maximal free relatives (English *whatever*). -/

structure MaximalityDatum where
  context : String
  chuj : String
  gloss : String
  yalnhejFelicitous : Bool
  /-- Example number in @cite{alonso-ovalle-royer-2024} -/
  exampleNumber : String
  deriving Repr

def ex43_partialRC : MaximalityDatum where
  context := "10 tools on a table; speaker grabbed 3 at random"
  chuj := "Ix-w-il-a' [yalnhej tas herramienta]."
  gloss := "I grabbed YALNHEJ what tools"
  yalnhejFelicitous := true
  exampleNumber := "(43)/(44)"

def ex46_partialEpi : MaximalityDatum where
  context := "10 meals available; speaker ate 5 unknown ones"
  chuj := "Ix-w-uch'a' [yalnhej tas tek-al]."
  gloss := "I ate YALNHEJ what dishes"
  yalnhejFelicitous := true
  exampleNumber := "(46)/(47)"

theorem all_partial_domain_felicitous :
    [ex43_partialRC, ex46_partialEpi].all (·.yalnhejFelicitous) = true := by native_decide


-- ════════════════════════════════════════════════════
-- § 7. Unremarkable Readings (§5)
-- ════════════════════════════════════════════════════

/-! Some modal indefinites have "unremarkable" (plain existential)
readings in addition to their modal readings. @cite{alonso-ovalle-royer-2024} (§5)
correlate this with predicativity. -/

structure UnremarkableReadingDatum where
  language : String
  form : String
  hasUnremarkable : Bool
  predicative : Bool
  /-- Example number(s) in @cite{alonso-ovalle-royer-2024} -/
  exampleNumber : String
  deriving Repr

def unoCualquiera_unremarkable : UnremarkableReadingDatum where
  language := "Spanish"
  form := "uno cualquiera"
  hasUnremarkable := true
  predicative := true
  exampleNumber := "(99)–(102)"

def irgendein_unremarkable : UnremarkableReadingDatum where
  language := "German"
  form := "irgendein"
  hasUnremarkable := true
  predicative := true
  exampleNumber := "(94)/(95)"

def komon_unremarkable : UnremarkableReadingDatum where
  language := "Chuj (Mayan)"
  form := "komon"
  hasUnremarkable := true
  predicative := true
  exampleNumber := "§5"

def yalnhej_unremarkable : UnremarkableReadingDatum where
  language := "Chuj (Mayan)"
  form := "yalnhej"
  hasUnremarkable := false
  predicative := false
  exampleNumber := "(104)/(105)"

def allUnremarkableData : List UnremarkableReadingDatum :=
  [unoCualquiera_unremarkable, irgendein_unremarkable,
   komon_unremarkable, yalnhej_unremarkable]

/-- Predicativity correlates with unremarkable readings across all data. -/
theorem predicativity_unremarkable_correlation :
    allUnremarkableData.all (λ d =>
      d.predicative == d.hasUnremarkable) = true := by native_decide

/-- Cross-check: fragment entry fields agree with independent empirical data. -/
theorem yalnhej_entry_unremarkable_agrees :
    yalnhejEntry.hasUnremarkableReading = yalnhej_unremarkable.hasUnremarkable := rfl

theorem komon_entry_unremarkable_agrees :
    komonEntry.hasUnremarkableReading = komon_unremarkable.hasUnremarkable := rfl

theorem unoCualquiera_entry_unremarkable_agrees :
    unoCualquieraEntry.hasUnremarkableReading = unoCualquiera_unremarkable.hasUnremarkable := rfl

/-- Predicativity correlates with unremarkable readings across all entries. -/
theorem predicativity_correlates_unremarkable :
    allEntries.all (λ e =>
      e.canBePredicate == e.hasUnremarkableReading) = true := by native_decide


-- ════════════════════════════════════════════════════
-- § 8. Harmonic Interpretations (§4.3)
-- ════════════════════════════════════════════════════

/-! Under an external modal (imperative, deontic, attitude verb),
the MI's anchor can be co-indexed with the modal's event, giving
"any X is fine" readings. -/

inductive EmbeddingModal where
  | imperative
  | deontic
  | attitudeVerb
  deriving DecidableEq, BEq, Repr

structure HarmonicDatum where
  chuj : String
  gloss : String
  embedding : EmbeddingModal
  isHarmonic : Bool
  reading : String
  /-- Example number in @cite{alonso-ovalle-royer-2024} -/
  exampleNumber : String
  deriving Repr

def ex82_imperativeNonharmonic : HarmonicDatum where
  chuj := "Il-a' [yalnhej tas baraja]!"
  gloss := "Grab YALNHEJ what card!"
  embedding := .imperative
  isHarmonic := false
  reading := "Grab a random card (described event anchor)"
  exampleNumber := "(82)"

def ex85_imperativeHarmonic : HarmonicDatum where
  chuj := "Il-a' [yalnhej tas baraja]!"
  gloss := "Grab YALNHEJ what card!"
  embedding := .imperative
  isHarmonic := true
  reading := "Any card is fine (imperative event anchor)"
  exampleNumber := "(85)"

def ex90_attitudeHarmonic : HarmonicDatum where
  chuj := "S-b'oj-on waj Xun [yalnhej mach] ix-hul-i."
  gloss := "Xun thinks YALNHEJ who came"
  embedding := .attitudeVerb
  isHarmonic := true
  reading := "Xun thinks someone came, doesn't know/care who (doxastic anchor)"
  exampleNumber := "(90)/(91)"

/-- Same surface string, two readings: (82) non-harmonic and (85) harmonic
    share the same Chuj form but differ in anchor co-indexing. -/
theorem imperative_ambiguity :
    ex82_imperativeNonharmonic.chuj = ex85_imperativeHarmonic.chuj ∧
    ex82_imperativeNonharmonic.isHarmonic ≠ ex85_imperativeHarmonic.isHarmonic := by
  constructor
  · rfl
  · decide


-- ════════════════════════════════════════════════════════════════
-- Part II: Kratzer Anchoring Bridge Theorems
-- ════════════════════════════════════════════════════════════════


-- ════════════════════════════════════════════════════
-- § 9. Position → Semantically Productive Anchors
-- ════════════════════════════════════════════════════

/-- Which anchor types are semantically productive given a syntactic
position (cross-classified with verb volitionality).

This is A-O&R's core structural explanation for the
position-sensitivity of *yalnhej*'s modal flavor. -/
def availableAnchors : ChujDPPosition → List AnchorType
  | .externalArg => [.speechEvent]
  | .internalArgVolitional => [.speechEvent, .describedEvent]
  | .internalArgNonVolitional => [.speechEvent]
  | .adjunctVolitional => [.speechEvent, .describedEvent]
  | .adjunctNonVolitional => [.speechEvent]


-- ════════════════════════════════════════════════════
-- § 10. Anchor → Flavor (by construction)
-- ════════════════════════════════════════════════════

/-- The predicted flavors for a position = the flavors of its
available anchor types. -/
def predictedFlavors (pos : ChujDPPosition) : List ModalFlavor :=
  (availableAnchors pos).map AnchorType.toFlavor

theorem speech_anchor_epistemic :
    AnchorType.speechEvent.toFlavor = .epistemic := rfl

theorem described_anchor_circumstantial :
    AnchorType.describedEvent.toFlavor = .circumstantial := rfl


-- ════════════════════════════════════════════════════
-- § 11. Predictions match observed data
-- ════════════════════════════════════════════════════

/-- The anchoring theory predicts exactly the observed flavor
distribution for ALL five position types in Table 5. -/
theorem predictions_match_data :
    ∀ pos : ChujDPPosition,
      predictedFlavors pos = yalnhejFlavorsAt pos := by
  intro pos; cases pos <;> rfl


-- ════════════════════════════════════════════════════
-- § 12. Voice → Position (via Chuj voice system)
-- ════════════════════════════════════════════════════

/-- Active transitive voice (vØ): agent = external → epistemic only. -/
theorem active_agent_is_external :
    Fragments.Chuj.vØ.hasD = true ∧
    predictedFlavors .externalArg = [.epistemic] :=
  ⟨rfl, rfl⟩

/-- Passive voice (-ch): theme promoted, agent implicit → both flavors. -/
theorem passive_theme_is_internal :
    Fragments.Chuj.v_ch.hasD = false ∧
    predictedFlavors .internalArgVolitional = [.epistemic, .circumstantial] :=
  ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 13. Cross-Linguistic Bridge: Upper-Boundedness
-- ════════════════════════════════════════════════════

/-- Upper-bounded modal indefinites impose an anti-singleton inference (§5). -/
theorem upper_bounded_group :
    [algúnEntry, unoCualquieraEntry].all (·.upperBounded) = true := by native_decide

/-- Non-upper-bounded modal indefinites: no anti-singleton. -/
theorem not_upper_bounded_group :
    [yalnhejEntry, irgendeinEntry, nimporteQuelEntry, unQualsiasiEntry].all
      (·.upperBounded == false) = true := by native_decide


-- ════════════════════════════════════════════════════
-- § 14. Non-Maximality Bridge (§3.2.4)
-- ════════════════════════════════════════════════════

/-- *Yalnhej* is not upper-bounded: compatible with partial-domain
    scenarios. The EventRelativity worked example demonstrates this
    concretely with `yalnhej_nonmaximal_ab`. -/
theorem yalnhej_nonmaximal :
    yalnhejEntry.upperBounded = false := rfl


end Phenomena.ModalIndefinites.Studies.AlonsoOvalleRoyer2024
