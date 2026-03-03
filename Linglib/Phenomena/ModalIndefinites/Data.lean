import Linglib.Core.ModalIndefinite

/-!
# Modal Indefinites: Cross-Linguistic Data
@cite{alonso-ovalle-menendez-benito-2010} @cite{alonso-ovalle-royer-2024} @cite{kratzer-shimoyama-2002b} @cite{alonso-ovalle-royer-2021} @cite{chierchia-2013} @cite{jayez-tovena-2006} @cite{kratzer-shimoyama-2002}

Theory-neutral empirical data on modal indefinites, following
@cite{alonso-ovalle-royer-2024} "Modal indefinites: Lessons from Chuj."

## Definition

A **modal indefinite** is an indefinite determiner / DP that conventionally
encodes a modal component: beyond existential quantification, it conveys
that any domain member could have been the witness (modal variation / free
choice), or that the speaker doesn't know which individual satisfies the
predicate (epistemic ignorance), or that any choice is permitted (random
choice).

## Three Dimensions of Variation (§6)

1. **Status**: Is the modal component at-issue (part of assertive content)
   or not-at-issue (presupposed / conventionally implicated)?
2. **Content**: Which modal flavors does the component support?
   (Epistemic, random choice / circumstantial, or both.)
3. **Upper-boundedness**: Does the indefinite impose an anti-singleton
   inference (¬∀x[P(x) → Q(x)])?

-/

namespace Phenomena.ModalIndefinites.Data

open Core.ModalLogic (ModalFlavor)
open Core.ModalIndefinite


-- ════════════════════════════════════════════════════
-- § 1. Chuj *yalnhej*
-- ════════════════════════════════════════════════════

/-- Chuj *yalnhej*: at-issue, epistemic + random choice, not upper-bounded,
    position-sensitive (§6).

    External argument → epistemic only.
    Internal argument / adjunct (volitional) → epistemic or random choice.
    Internal argument / adjunct (non-volitional) → epistemic only. -/
def yalnhej : ModalIndefiniteEntry where
  language := "Chuj (Mayan)"
  form := "yalnhej"
  gloss := "MODAL.INDEF"
  status := .atIssue
  flavors := [.epistemic, .circumstantial]  -- RC ⊂ circumstantial
  upperBounded := false
  positionSensitive := true
  hasUnremarkableReading := false
  canBePredicate := false
  source := "Alonso-Ovalle & Royer 2024"

/-- Chuj *komon*: at-issue random-choice modifier for mass/plural
    (@cite{alonso-ovalle-royer-2021}; cited in @cite{alonso-ovalle-royer-2024}, §5). -/
def komon : ModalIndefiniteEntry where
  language := "Chuj (Mayan)"
  form := "komon"
  gloss := "MODAL.INDEF (mass/plural)"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := false
  hasUnremarkableReading := true
  canBePredicate := true
  source := "Alonso-Ovalle & Royer 2021"


-- ════════════════════════════════════════════════════
-- § 2. Spanish *algún* (@cite{alonso-ovalle-menendez-benito-2010})
-- ════════════════════════════════════════════════════

/-- Spanish *algún*: not-at-issue, epistemic only, upper-bounded
    (§6; @cite{alonso-ovalle-menendez-benito-2010}). -/
def algún : ModalIndefiniteEntry where
  language := "Spanish"
  form := "algún"
  gloss := "MODAL.INDEF (epistemic, anti-singleton)"
  status := .notAtIssue
  flavors := [.epistemic]
  upperBounded := true
  hasUnremarkableReading := false
  canBePredicate := false
  source := "Alonso-Ovalle & Menéndez-Benito 2010"


-- ════════════════════════════════════════════════════
-- § 3. German *irgendein* (@cite{kratzer-shimoyama-2002})
-- ════════════════════════════════════════════════════

/-- German *irgendein*: not-at-issue, epistemic + random choice,
    not upper-bounded (§6).
    Epistemic in episodic assertions; random choice under deontic modals. -/
def irgendein : ModalIndefiniteEntry where
  language := "German"
  form := "irgendein"
  gloss := "MODAL.INDEF (epistemic / free choice)"
  status := .notAtIssue
  flavors := [.epistemic, .circumstantial]
  upperBounded := false
  hasUnremarkableReading := true
  canBePredicate := true
  source := "Kratzer & Shimoyama 2002"


-- ════════════════════════════════════════════════════
-- § 4. Spanish *uno cualquiera* (@cite{alonso-ovalle-menendez-benito-2010})
-- ════════════════════════════════════════════════════

/-- Spanish *uno cualquiera*: at-issue, random choice only,
    upper-bounded (§5–6; @cite{alonso-ovalle-menendez-benito-2010}). -/
def unoCualquiera : ModalIndefiniteEntry where
  language := "Spanish"
  form := "uno cualquiera"
  gloss := "one whichever"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := true
  hasUnremarkableReading := true
  canBePredicate := true
  source := "Alonso-Ovalle & Menéndez-Benito 2018"


-- ════════════════════════════════════════════════════
-- § 5. French *n'importe quel* (@cite{jayez-tovena-2006})
-- ════════════════════════════════════════════════════

/-- French *n'importe quel*: at-issue, random choice only,
    not upper-bounded (§6; @cite{jayez-tovena-2006}).

    Note: at-issue status and non-upper-boundedness are inferred from
    the cited source; @cite{alonso-ovalle-royer-2024} discusses content only. -/
def nimporteQuel : ModalIndefiniteEntry where
  language := "French"
  form := "n'importe quel"
  gloss := "no matter which"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := false
  hasUnremarkableReading := false
  canBePredicate := false
  source := "Jayez & Tovena 2006"


-- ════════════════════════════════════════════════════
-- § 6. Italian *un qualsiasi* (@cite{chierchia-2013})
-- ════════════════════════════════════════════════════

/-- Italian *un qualsiasi*: at-issue, random choice,
    not upper-bounded (§6; @cite{chierchia-2013}, §5.3.2).

    Note: at-issue status and non-upper-boundedness are inferred from
    the cited source; @cite{alonso-ovalle-royer-2024} discusses content only. -/
def unQualsiasi : ModalIndefiniteEntry where
  language := "Italian"
  form := "un qualsiasi"
  gloss := "a whichever"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := false
  hasUnremarkableReading := false
  canBePredicate := false
  source := "Chierchia 2013"


-- ════════════════════════════════════════════════════
-- § 7. All Entries
-- ════════════════════════════════════════════════════

def allEntries : List ModalIndefiniteEntry :=
  [yalnhej, komon, algún, irgendein, unoCualquiera, nimporteQuel, unQualsiasi]

theorem allEntries_count : allEntries.length = 7 := by native_decide


-- ════════════════════════════════════════════════════
-- § 8. Per-Datum Verification Theorems
-- ════════════════════════════════════════════════════

-- Status

theorem yalnhej_at_issue : yalnhej.status = .atIssue := rfl
theorem algún_not_at_issue : algún.status = .notAtIssue := rfl
theorem irgendein_not_at_issue : irgendein.status = .notAtIssue := rfl
theorem unoCualquiera_at_issue : unoCualquiera.status = .atIssue := rfl
theorem nimporteQuel_at_issue : nimporteQuel.status = .atIssue := rfl

-- Upper-boundedness

theorem yalnhej_not_upper_bounded : yalnhej.upperBounded = false := rfl
theorem algún_upper_bounded : algún.upperBounded = true := rfl
theorem irgendein_not_upper_bounded : irgendein.upperBounded = false := rfl
theorem unoCualquiera_upper_bounded : unoCualquiera.upperBounded = true := rfl
theorem nimporteQuel_not_upper_bounded : nimporteQuel.upperBounded = false := rfl

-- Flavor availability

theorem yalnhej_has_epistemic : yalnhej.hasEpistemic = true := by native_decide
theorem yalnhej_has_rc : yalnhej.hasCircumstantial = true := by native_decide
theorem algún_epistemic_only : algún.hasEpistemic = true ∧ algún.hasCircumstantial = false := by
  constructor <;> native_decide
theorem irgendein_both_flavors :
    irgendein.hasEpistemic = true ∧ irgendein.hasCircumstantial = true := by
  constructor <;> native_decide
theorem unoCualquiera_rc_only :
    unoCualquiera.hasEpistemic = false ∧ unoCualquiera.hasCircumstantial = true := by
  constructor <;> native_decide

-- Position sensitivity

theorem yalnhej_position_sensitive : yalnhej.positionSensitive = true := rfl
theorem algún_not_position_sensitive : algún.positionSensitive = false := rfl


-- ════════════════════════════════════════════════════
-- § 9. Typological Generalizations (§6)
-- ════════════════════════════════════════════════════

/-- Chuj *yalnhej* and German *irgendein* share the same flavor
inventory (epistemic + random choice) but differ in status. -/
theorem yalnhej_irgendein_same_flavors :
    yalnhej.flavors = irgendein.flavors := rfl

theorem yalnhej_irgendein_differ_in_status :
    yalnhej.status ≠ irgendein.status := by decide

/-- The at-issue / not-at-issue split (§6.1):
*yalnhej*, *uno cualquiera* are at-issue; *algún*, *irgendein*
are not-at-issue. (n'importe quel and un qualsiasi classified as
at-issue per their respective cited sources.) -/
theorem at_issue_items :
    [yalnhej, unoCualquiera, nimporteQuel, unQualsiasi].all
      (·.status == .atIssue) = true := by native_decide

theorem not_at_issue_items :
    [algún, irgendein].all (·.status == .notAtIssue) = true := by native_decide

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
-- § 10. Position-Sensitive Flavor Distribution (Table 5)
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
(Table 5, §3.2–4.2).

External argument: epistemic only — too high to co-bind with the
  VP event, so the anchor must project from the assertion (speech event).
Internal/adjunct + volitional: both epistemic and RC — the described
  event has a decision subevent that can anchor normative modality.
Internal/adjunct + non-volitional: epistemic only — the described
  event has no decision subevent, so f(e) cannot yield RC (§4.1, ex.34). -/
def yalnhejFlavorsAt : ChujDPPosition → List ModalFlavor
  | .externalArg => [.epistemic]
  | .internalArgVolitional => [.epistemic, .circumstantial]
  | .internalArgNonVolitional => [.epistemic]
  | .adjunctVolitional => [.epistemic, .circumstantial]
  | .adjunctNonVolitional => [.epistemic]

/-- External argument restricts to epistemic only (§3.2.1). -/
theorem ext_arg_epistemic_only :
    yalnhejFlavorsAt .externalArg = [.epistemic] := rfl

/-- Volitional internal argument allows both flavors (§3.2.2). -/
theorem int_arg_vol_both_flavors :
    yalnhejFlavorsAt .internalArgVolitional = [.epistemic, .circumstantial] := rfl

/-- Non-volitional internal argument restricts to epistemic only
    (§3.2.2, ex.28/34). -/
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
-- § 11. Example Sentences
-- ════════════════════════════════════════════════════

/-- A Chuj *yalnhej* example sentence with empirical judgments. -/
structure YalnhejExample where
  /-- Chuj sentence -/
  chuj : String
  /-- English gloss -/
  gloss : String
  /-- Syntactic position of the yalnhej DP -/
  position : ChujDPPosition
  /-- Available modal reading(s) -/
  availableFlavors : List ModalFlavor
  /-- Example number in @cite{alonso-ovalle-royer-2024} -/
  exampleNumber : String
  deriving Repr

/-- (22)/(3): External argument, epistemic only.
    "A person or group of people danced at the party, I don't
    know who (maybe all did)." RC unavailable. -/
def ex22_extArg : YalnhejExample where
  chuj := "[Yalnhej mach] ix-chanhalw-i t'a k'inh."
  gloss := "YALNHEJ who danced at the party"
  position := .externalArg
  availableFlavors := [.epistemic]
  exampleNumber := "(22)"

/-- (31): Internal argument, volitional verb, random choice available.
    "Xun bought a random book / some random books." -/
def ex31_intArgRC : YalnhejExample where
  chuj := "[Yalnhej tas libro'-al] ix-s-man waj Xun."
  gloss := "Xun bought YALNHEJ what book(s)"
  position := .internalArgVolitional
  availableFlavors := [.epistemic, .circumstantial]
  exampleNumber := "(31)"

/-- (34)/(28): Internal argument, non-volitional verb, epistemic only.
    "Xun liked some dish(es) or other, I don't know which
    (maybe all)." RC unavailable with non-volitional 'like'. -/
def ex34_intArgNonVol : YalnhejExample where
  chuj := "[Yalnhej tas tek-al] ix-s-nib'-ej waj Xun."
  gloss := "Xun liked YALNHEJ what dish(es)"
  position := .internalArgNonVolitional
  availableFlavors := [.epistemic]
  exampleNumber := "(34)"

/-- (41): Adjunct, volitional verb, random choice available.
    "Malin ate yalnhej where" = Malin ate at a random place. -/
def ex41_adjunctRC : YalnhejExample where
  chuj := "[Yalnhej b'ajt'il] ix-wa' ix Malin."
  gloss := "Malin ate YALNHEJ where"
  position := .adjunctVolitional
  availableFlavors := [.epistemic, .circumstantial]
  exampleNumber := "(41)"

/-- (39): Adjunct, non-volitional verb, epistemic only.
    "There was rain yalnhej where yesterday" = It rained
    somewhere, I don't know where. RC unavailable. -/
def ex39_adjunctNonVol : YalnhejExample where
  chuj := "[Yalnhej b'ajt'il] y-ak' nhab' ewi."
  gloss := "it rained YALNHEJ where yesterday"
  position := .adjunctNonVolitional
  availableFlavors := [.epistemic]
  exampleNumber := "(39)"

def allExamples : List YalnhejExample :=
  [ex22_extArg, ex31_intArgRC, ex34_intArgNonVol, ex41_adjunctRC, ex39_adjunctNonVol]

/-- Per-example flavor verification. -/
theorem ex22_epistemic_only :
    ex22_extArg.availableFlavors = [.epistemic] := rfl
theorem ex31_allows_rc :
    ex31_intArgRC.availableFlavors = [.epistemic, .circumstantial] := rfl
theorem ex34_nonvol_epistemic_only :
    ex34_intArgNonVol.availableFlavors = [.epistemic] := rfl

/-- Consistency: each example's available flavors match the position-based
    prediction from yalnhejFlavorsAt. -/
theorem examples_match_position_prediction :
    allExamples.all (λ ex => ex.availableFlavors == yalnhejFlavorsAt ex.position)
    = true := by native_decide


-- ════════════════════════════════════════════════════
-- § 12. Non-Maximality Data (§3.2.4)
-- ════════════════════════════════════════════════════

/-! Yalnhej is compatible with partial-domain scenarios, unlike
maximal free relatives (English *whatever*). A *whatever*-FR
requires every domain member to satisfy the scope; yalnhej
does not. This is distinct from upper-boundedness: UB blocks
∀P→Q (anti-singleton), whereas non-maximality merely allows
¬∀P→Q without requiring it. -/

/-- A maximality datum: a context + Chuj sentence + felicity judgment. -/
structure MaximalityDatum where
  /-- Context description -/
  context : String
  /-- Chuj sentence -/
  chuj : String
  /-- English gloss -/
  gloss : String
  /-- Whether yalnhej is felicitous in this context -/
  yalnhejFelicitous : Bool
  /-- Example number in @cite{alonso-ovalle-royer-2024} -/
  exampleNumber : String
  deriving Repr

/-- (43)/(44): Partial-domain, RC context.
    Context: 10 tools on a table; speaker grabbed 3 at random.
    *Yalnhej* is felicitous — no maximality requirement. -/
def ex43_partialRC : MaximalityDatum where
  context := "10 tools on a table; speaker grabbed 3 at random"
  chuj := "Ix-w-il-a' [yalnhej tas herramienta]."
  gloss := "I grabbed YALNHEJ what tools"
  yalnhejFelicitous := true
  exampleNumber := "(43)/(44)"

/-- (46)/(47): Partial-domain, epistemic context.
    Context: 10 meals available; speaker ate 5 but doesn't remember which.
    *Yalnhej* is felicitous — compatible with not knowing, without
    requiring all meals to have been eaten. -/
def ex46_partialEpi : MaximalityDatum where
  context := "10 meals available; speaker ate 5 unknown ones"
  chuj := "Ix-w-uch'a' [yalnhej tas tek-al]."
  gloss := "I ate YALNHEJ what dishes"
  yalnhejFelicitous := true
  exampleNumber := "(46)/(47)"

def allMaximalityData : List MaximalityDatum :=
  [ex43_partialRC, ex46_partialEpi]

/-- Per-datum: both partial-domain examples are felicitous with yalnhej. -/
theorem ex43_felicitous : ex43_partialRC.yalnhejFelicitous = true := rfl
theorem ex46_felicitous : ex46_partialEpi.yalnhejFelicitous = true := rfl

/-- All maximality data show yalnhej is felicitous in partial-domain
    contexts — confirming non-maximality. -/
theorem all_partial_domain_felicitous :
    allMaximalityData.all (·.yalnhejFelicitous) = true := by native_decide


-- ════════════════════════════════════════════════════
-- § 13. Unremarkable Readings (§5)
-- ════════════════════════════════════════════════════

/-! Some modal indefinites have "unremarkable" (plain existential)
readings in addition to their modal readings. *Komon* and *uno
cualquiera* can mean just "some" without modal flavor; *yalnhej*
cannot. @cite{alonso-ovalle-royer-2024} (§5) correlate this with predicativity:
items that can appear in predicative position tend to have
unremarkable readings; *yalnhej* cannot be predicative and
correspondingly lacks unremarkable readings. -/

/-- An unremarkable-reading datum: item + whether it has unremarkable readings. -/
structure UnremarkableReadingDatum where
  /-- Language -/
  language : String
  /-- Surface form -/
  form : String
  /-- Does the item have unremarkable (non-modal) readings? -/
  hasUnremarkable : Bool
  /-- Can the item appear in predicative position? -/
  predicative : Bool
  /-- Example number(s) in @cite{alonso-ovalle-royer-2024} -/
  exampleNumber : String
  deriving Repr

/-- (99)–(102): *uno cualquiera* has unremarkable readings;
    can be predicative. -/
def unoCualquiera_unremarkable : UnremarkableReadingDatum where
  language := "Spanish"
  form := "uno cualquiera"
  hasUnremarkable := true
  predicative := true
  exampleNumber := "(99)–(102)"

/-- (94)/(95): *irgendein* has unremarkable readings;
    can be predicative. -/
def irgendein_unremarkable : UnremarkableReadingDatum where
  language := "German"
  form := "irgendein"
  hasUnremarkable := true
  predicative := true
  exampleNumber := "(94)/(95)"

/-- *komon* has unremarkable readings; can be predicative
    (§5). -/
def komon_unremarkable : UnremarkableReadingDatum where
  language := "Chuj (Mayan)"
  form := "komon"
  hasUnremarkable := true
  predicative := true
  exampleNumber := "§5"

/-- (104)/(105): *yalnhej* LACKS unremarkable readings;
    CANNOT be predicative. -/
def yalnhej_unremarkable : UnremarkableReadingDatum where
  language := "Chuj (Mayan)"
  form := "yalnhej"
  hasUnremarkable := false
  predicative := false
  exampleNumber := "(104)/(105)"

def allUnremarkableData : List UnremarkableReadingDatum :=
  [unoCualquiera_unremarkable, irgendein_unremarkable,
   komon_unremarkable, yalnhej_unremarkable]

-- Per-datum verification

theorem yalnhej_no_unremarkable :
    yalnhej_unremarkable.hasUnremarkable = false := rfl

theorem komon_has_unremarkable :
    komon_unremarkable.hasUnremarkable = true := rfl

theorem unoCualquiera_has_unremarkable :
    unoCualquiera_unremarkable.hasUnremarkable = true := rfl

theorem irgendein_has_unremarkable_datum :
    irgendein_unremarkable.hasUnremarkable = true := rfl

/-- Predicativity correlates with unremarkable readings:
    every datum where canBePredicate = true also has unremarkable
    readings, and vice versa. -/
theorem predicativity_unremarkable_correlation :
    allUnremarkableData.all (λ d =>
      d.predicative == d.hasUnremarkable) = true := by native_decide

/-- Cross-check: the entry-level fields agree with the datum-level fields
    for yalnhej, komon, and uno cualquiera. -/
theorem yalnhej_entry_unremarkable_agrees :
    yalnhej.hasUnremarkableReading = yalnhej_unremarkable.hasUnremarkable := rfl

theorem komon_entry_unremarkable_agrees :
    komon.hasUnremarkableReading = komon_unremarkable.hasUnremarkable := rfl

theorem unoCualquiera_entry_unremarkable_agrees :
    unoCualquiera.hasUnremarkableReading = unoCualquiera_unremarkable.hasUnremarkable := rfl


-- ════════════════════════════════════════════════════
-- § 14. Harmonic Interpretations (§4.3)
-- ════════════════════════════════════════════════════

/-! Under an external modal (imperative, deontic, attitude verb),
the MI's anchor can be co-indexed with the modal's event, giving
"any X is fine" readings. The non-harmonic reading anchors the MI
to the described event independently; the harmonic reading aligns
the MI's domain with the external modal's domain. -/

/-- The type of embedding modal for harmonic interpretation data. -/
inductive EmbeddingModal where
  /-- Imperative: "Grab yalnhej card!" -/
  | imperative
  /-- Deontic: "You should grab yalnhej card." -/
  | deontic
  /-- Attitude verb: "Xun thinks yalnhej person came." -/
  | attitudeVerb
  deriving DecidableEq, BEq, Repr

/-- A harmonic interpretation datum. -/
structure HarmonicDatum where
  /-- Chuj sentence -/
  chuj : String
  /-- English gloss -/
  gloss : String
  /-- Which embedding modal -/
  embedding : EmbeddingModal
  /-- Does the harmonic reading arise? -/
  isHarmonic : Bool
  /-- Description of reading -/
  reading : String
  /-- Example number in @cite{alonso-ovalle-royer-2024} -/
  exampleNumber : String
  deriving Repr

/-- (82): Imperative, non-harmonic reading.
    "Grab a random card!" — MI anchors to the described (grabbing) event. -/
def ex82_imperativeNonharmonic : HarmonicDatum where
  chuj := "Il-a' [yalnhej tas baraja]!"
  gloss := "Grab YALNHEJ what card!"
  embedding := .imperative
  isHarmonic := false
  reading := "Grab a random card (described event anchor)"
  exampleNumber := "(82)"

/-- (85): Imperative, harmonic reading.
    "Grab yalnhej card!" — MI anchor co-indexed with imperative event,
    giving "any card is fine" / "it doesn't matter which." -/
def ex85_imperativeHarmonic : HarmonicDatum where
  chuj := "Il-a' [yalnhej tas baraja]!"
  gloss := "Grab YALNHEJ what card!"
  embedding := .imperative
  isHarmonic := true
  reading := "Any card is fine (imperative event anchor)"
  exampleNumber := "(85)"

/-- (90)/(91): Attitude verb, harmonic reading.
    "Xun thinks yalnhej person came" — MI anchor co-indexed with
    doxastic modal of 'think', giving "whoever it was" reading. -/
def ex90_attitudeHarmonic : HarmonicDatum where
  chuj := "S-b'oj-on waj Xun [yalnhej mach] ix-hul-i."
  gloss := "Xun thinks YALNHEJ who came"
  embedding := .attitudeVerb
  isHarmonic := true
  reading := "Xun thinks someone came, doesn't know/care who (doxastic anchor)"
  exampleNumber := "(90)/(91)"

def allHarmonicData : List HarmonicDatum :=
  [ex82_imperativeNonharmonic, ex85_imperativeHarmonic, ex90_attitudeHarmonic]

-- Per-datum verification

theorem ex82_nonharmonic : ex82_imperativeNonharmonic.isHarmonic = false := rfl
theorem ex85_harmonic : ex85_imperativeHarmonic.isHarmonic = true := rfl
theorem ex90_harmonic : ex90_attitudeHarmonic.isHarmonic = true := rfl

/-- Same surface string, two readings: (82) non-harmonic and (85) harmonic
    share the same Chuj form but differ in anchor co-indexing. -/
theorem imperative_ambiguity :
    ex82_imperativeNonharmonic.chuj = ex85_imperativeHarmonic.chuj ∧
    ex82_imperativeNonharmonic.isHarmonic ≠ ex85_imperativeHarmonic.isHarmonic := by
  constructor
  · rfl
  · decide


end Phenomena.ModalIndefinites.Data
