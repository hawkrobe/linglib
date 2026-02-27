import Linglib.Core.ModalIndefinite

/-!
# Modal Indefinites: Cross-Linguistic Data

Theory-neutral empirical data on modal indefinites, following
Alonso-Ovalle & Royer (2024) "Modal indefinites: Lessons from Chuj."

## Definition

A **modal indefinite** is an indefinite determiner / DP that conventionally
encodes a modal component: beyond existential quantification, it conveys
that any domain member could have been the witness (modal variation / free
choice), or that the speaker doesn't know which individual satisfies the
predicate (epistemic ignorance), or that any choice is permitted (random
choice).

## Three Dimensions of Variation (A-O&R 2024, §6)

1. **Status**: Is the modal component at-issue (part of assertive content)
   or not-at-issue (presupposed / conventionally implicated)?
2. **Content**: Which modal flavors does the component support?
   (Epistemic, random choice / circumstantial, or both.)
3. **Upper-boundedness**: Does the indefinite impose an anti-singleton
   inference (¬∀x[P(x) → Q(x)])?

## References

- Alonso-Ovalle, L. & Royer, J. (2024). Modal indefinites: Lessons from
  Chuj. Linguistics and Philosophy.
- Alonso-Ovalle, L. & Menéndez-Benito, P. (2010). Modal indefinites.
  Natural Language Semantics 18:1–31.
- Kratzer, A. & Shimoyama, J. (2002). Indeterminate pronouns: The view
  from Japanese.
-/

namespace Phenomena.ModalIndefinites.Data

open Core.ModalLogic (ModalFlavor)
open Core.ModalIndefinite


-- ════════════════════════════════════════════════════
-- § 1. Chuj *yalnhej* (A-O&R 2024)
-- ════════════════════════════════════════════════════

/-- Chuj *yalnhej*: at-issue, epistemic + random choice, not upper-bounded,
    position-sensitive (A-O&R 2024, §6).

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
  source := "Alonso-Ovalle & Royer 2024"

/-- Chuj *komon*: at-issue random-choice modifier for mass/plural
    (Alonso-Ovalle & Royer 2021; cited in A-O&R 2024, §5). -/
def komon : ModalIndefiniteEntry where
  language := "Chuj (Mayan)"
  form := "komon"
  gloss := "MODAL.INDEF (mass/plural)"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := false
  source := "Alonso-Ovalle & Royer 2021"


-- ════════════════════════════════════════════════════
-- § 2. Spanish *algún* (Alonso-Ovalle & Menéndez-Benito 2010)
-- ════════════════════════════════════════════════════

/-- Spanish *algún*: not-at-issue, epistemic only, upper-bounded
    (A-O&R 2024, §6; Alonso-Ovalle & Menéndez-Benito 2010). -/
def algún : ModalIndefiniteEntry where
  language := "Spanish"
  form := "algún"
  gloss := "MODAL.INDEF (epistemic, anti-singleton)"
  status := .notAtIssue
  flavors := [.epistemic]
  upperBounded := true
  source := "Alonso-Ovalle & Menéndez-Benito 2010"


-- ════════════════════════════════════════════════════
-- § 3. German *irgendein* (Kratzer & Shimoyama 2002)
-- ════════════════════════════════════════════════════

/-- German *irgendein*: not-at-issue, epistemic + random choice,
    not upper-bounded (A-O&R 2024, §6).
    Epistemic in episodic assertions; random choice under deontic modals. -/
def irgendein : ModalIndefiniteEntry where
  language := "German"
  form := "irgendein"
  gloss := "MODAL.INDEF (epistemic / free choice)"
  status := .notAtIssue
  flavors := [.epistemic, .circumstantial]
  upperBounded := false
  source := "Kratzer & Shimoyama 2002"


-- ════════════════════════════════════════════════════
-- § 4. Spanish *uno cualquiera* (Alonso-Ovalle & Menéndez-Benito 2018)
-- ════════════════════════════════════════════════════

/-- Spanish *uno cualquiera*: at-issue, random choice only,
    upper-bounded (A-O&R 2024, §5–6; A-O & M-B 2018). -/
def unoCualquiera : ModalIndefiniteEntry where
  language := "Spanish"
  form := "uno cualquiera"
  gloss := "one whichever"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := true
  source := "Alonso-Ovalle & Menéndez-Benito 2018"


-- ════════════════════════════════════════════════════
-- § 5. French *n'importe quel* (Jayez & Tovena 2006)
-- ════════════════════════════════════════════════════

/-- French *n'importe quel*: at-issue, random choice only,
    not upper-bounded (A-O&R 2024, §6; Jayez & Tovena 2006).

    Note: at-issue status and non-upper-boundedness are inferred from
    the cited source; A-O&R 2024 discusses content only. -/
def nimporteQuel : ModalIndefiniteEntry where
  language := "French"
  form := "n'importe quel"
  gloss := "no matter which"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := false
  source := "Jayez & Tovena 2006"


-- ════════════════════════════════════════════════════
-- § 6. Italian *un qualsiasi* (Chierchia 2013)
-- ════════════════════════════════════════════════════

/-- Italian *un qualsiasi*: at-issue, random choice,
    not upper-bounded (A-O&R 2024, §6; Chierchia 2013, §5.3.2).

    Note: at-issue status and non-upper-boundedness are inferred from
    the cited source; A-O&R 2024 discusses content only. -/
def unQualsiasi : ModalIndefiniteEntry where
  language := "Italian"
  form := "un qualsiasi"
  gloss := "a whichever"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := false
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
-- § 9. Typological Generalizations (A-O&R 2024, §6)
-- ════════════════════════════════════════════════════

/-- Chuj *yalnhej* and German *irgendein* share the same flavor
inventory (epistemic + random choice) but differ in status. -/
theorem yalnhej_irgendein_same_flavors :
    yalnhej.flavors = irgendein.flavors := rfl

theorem yalnhej_irgendein_differ_in_status :
    yalnhej.status ≠ irgendein.status := by decide

/-- The at-issue / not-at-issue split (A-O&R 2024, §6.1):
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
contribution of A-O&R (2024). -/
theorem yalnhej_unique_profile :
    (allEntries.filter (λ e =>
      e.status == .atIssue && e.hasEpistemic && e.hasCircumstantial)).length = 1 := by
  native_decide


-- ════════════════════════════════════════════════════
-- § 10. Position-Sensitive Flavor Distribution (A-O&R 2024, Table 5)
-- ════════════════════════════════════════════════════

/-- Syntactic positions for a DP in Chuj, cross-classified with
verb volitionality (A-O&R 2024, §3–4, Table 5).

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
(A-O&R 2024, Table 5, §3.2–4.2).

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

/-- External argument restricts to epistemic only (A-O&R 2024, §3.2.1). -/
theorem ext_arg_epistemic_only :
    yalnhejFlavorsAt .externalArg = [.epistemic] := rfl

/-- Volitional internal argument allows both flavors (A-O&R 2024, §3.2.2). -/
theorem int_arg_vol_both_flavors :
    yalnhejFlavorsAt .internalArgVolitional = [.epistemic, .circumstantial] := rfl

/-- Non-volitional internal argument restricts to epistemic only
    (A-O&R 2024, §3.2.2, ex.28/34). -/
theorem int_arg_nonvol_epistemic_only :
    yalnhejFlavorsAt .internalArgNonVolitional = [.epistemic] := rfl

/-- Position sensitivity: external ≠ volitional internal flavor sets. -/
theorem position_matters :
    yalnhejFlavorsAt .externalArg ≠ yalnhejFlavorsAt .internalArgVolitional := by
  decide

/-- Volitionality sensitivity: volitional ≠ non-volitional internal
    flavor sets (A-O&R 2024, §4.1). -/
theorem volitionality_matters :
    yalnhejFlavorsAt .internalArgVolitional ≠ yalnhejFlavorsAt .internalArgNonVolitional := by
  decide


-- ════════════════════════════════════════════════════
-- § 11. Example Sentences (A-O&R 2024)
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
  /-- Example number in A-O&R (2024) -/
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


end Phenomena.ModalIndefinites.Data
