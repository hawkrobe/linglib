import Linglib.Data.Examples.Levin1993
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Studies.Dowty1991

/-!
# Diathesis Alternation Bridge [levin-1993]

Connects the alternation judgment rows in `Data/Examples/Levin1993.json` to
the `LevinClass.participatesIn` prediction function, the Fragment verb
entries, and [dowty-1991]'s proto-role account of the three verb classes.

The verbs *break*, *cut*, *hit*, *touch* form Levin's §0.4 diagnostic
quadruple (pp. 5–10): each participates in a distinct subset of the
causative/inchoative, middle, conative, and body-part possessor ascension
alternations.

| Verb | Class | CI | Mid | Con | BPPA |
|------|-------|----|-----|-----|------|
| break | 45.1 | ✓ | ✓ | ✗ | ✗ |
| cut | 21.1 | ✗ | ✓ | ✓ | ✓ |
| hit | 18.1 | ✗ | ✗ | ✓ | ✓ |
| touch | 20 | ✗ | ✗ | ✗ | ✓ |

## Main declarations

- `classOf`, `alternationOf`, `observed` — project a row's `paperFeatures`
  into the curated `LevinClass` / `DiathesisAlternation` enums and a
  categorical participation value
- `participation_matches_prediction` — every categorical row with a
  representable class and alternation agrees with `participatesIn`
- `quadruple_patterns_distinct` — the four §0.4 verbs show pairwise
  distinct participation patterns
- `dowty_*` — [dowty-1991] §9.3's CoS-symmetry predictions checked against
  the rows (the comparison lives here, in the later paper's file)
-/

namespace Levin1993

open Data.Examples
open ArgumentStructure
open English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 1. Row adapters
-- ════════════════════════════════════════════════════

/-- Map a row's `levin_class` section string to the curated `LevinClass`
    enum. Subclasses collapse to their enum representative (51.3.2 run
    verbs → `mannerOfMotion`; 47.5.1 swarm verbs → the §47 existence
    family's `exist`; 48.1.1 → `appear`; 41.1.1 dress verbs → `dress`;
    36.3 → `socialInteraction`; 54.1 register verbs → `measure`).
    Classes outside the enum's grain (40.2 nonverbal expression, 40.3.2
    wink, 40.4 snooze, 37.5 talk) map to `none`. -/
def classOfString : String → Option LevinClass
  | "45.1" => some .break_
  | "21.1" => some .cut
  | "18.1" => some .hit
  | "20" => some .touch
  | "12" => some .pushPull
  | "9.7" => some .sprayLoad
  | "13.1" => some .give
  | "11.1" => some .send
  | "26.1" => some .build
  | "26.6" => some .turn
  | "43.4" => some .substanceEmission
  | "39.1" => some .eat
  | "39.4" => some .devour
  | "36.3" => some .socialInteraction
  | "48.1.1" => some .appear
  | "47.1" => some .exist
  | "47.5.1" => some .exist
  | "51.3" => some .mannerOfMotion
  | "51.3.2" => some .mannerOfMotion
  | "41.1.1" => some .dress
  | "37.3" => some .mannerOfSpeaking
  | "30.1" => some .see
  | "54.1" => some .measure
  | _ => none

/-- Map a row's `alternation` tag to the curated enum. -/
def alternationOfString : String → Option DiathesisAlternation
  | "causativeInchoative" => some .causativeInchoative
  | "inducedAction" => some .inducedAction
  | "middle" => some .middle
  | "conative" => some .conative
  | "substanceSource" => some .substanceSource
  | "unspecifiedObject" => some .unspecifiedObject
  | "understoodBodyPartObject" => some .understoodBodyPartObject
  | "understoodReflexiveObject" => some .understoodReflexiveObject
  | "understoodReciprocalObject" => some .understoodReciprocalObject
  | "dative" => some .dative
  | "benefactive" => some .benefactive
  | "locative" => some .locative
  | "bodyPartPossessorAscension" => some .bodyPartPossessorAscension
  | "swarm" => some .swarm
  | "materialProduct" => some .materialProduct
  | "totalTransformation" => some .totalTransformation
  | "instrumentSubject" => some .instrumentSubject
  | "verbalPassive" => some .verbalPassive
  | "prepositionalPassive" => some .prepositionalPassive
  | "thereInsertion" => some .thereInsertion
  | "locativeInversion" => some .locativeInversion
  | "cognateObject" => some .cognateObject
  | "wayConstruction" => some .wayConstruction
  | "resultative" => some .resultative
  | "directionalPhrase" => some .directionalPhrase
  | _ => none

/-- Levin class recorded on a row. -/
def classOf (e : LinguisticExample) : Option LevinClass :=
  (e.paperFeatures.lookup "levin_class").bind classOfString

/-- Alternation recorded on a row. -/
def alternationOf (e : LinguisticExample) : Option DiathesisAlternation :=
  (e.paperFeatures.lookup "alternation").bind alternationOfString

/-- Categorical participation recorded on a row; `none` for marginal
    judgments (the `participatesIn` profile is Boolean). -/
def observed (e : LinguisticExample) : Option Bool :=
  match e.paperFeatures.lookup "participates" with
  | some "true" => some true
  | some "false" => some false
  | _ => none

-- ════════════════════════════════════════════════════
-- § 2. Transfer: judgments match the participation profile
-- ════════════════════════════════════════════════════

/-- A row agrees with `LevinClass.participatesIn` (vacuously, if its class
    or alternation is unrepresentable or its judgment is marginal). -/
def agreesWithPrediction (e : LinguisticExample) : Bool :=
  match classOf e, alternationOf e, observed e with
  | some c, some a, some b => c.participatesIn a == b
  | _, _, _ => true

set_option maxRecDepth 4096 in
/-- Every categorical row with a representable class and alternation matches
    the `participatesIn` prediction. In particular the CI rule blocks *cut*
    via instrument specification (Levin pp. 9–10: an inherently specified
    instrument requires an agent, blocking the agentless inchoative). -/
theorem participation_matches_prediction :
    Examples.all.all agreesWithPrediction = true := by decide

/-- Every row's `alternation` tag is one of the curated alternations. -/
theorem alternations_all_representable :
    Examples.all.all (fun e => (alternationOf e).isSome) = true := by decide

set_option maxRecDepth 4096 in
/-- Exactly four rows carry Levin classes outside the curated enum's grain:
    *wave* (40.3.2 wink), *laugh* (40.2 nonverbal expression), *sleep*
    (40.4 snooze), *talk* (37.5). These are excluded from
    `participation_matches_prediction` by `classOf`. -/
theorem unrepresentable_classes :
    (Examples.all.filter (fun e => (classOf e).isNone)).map (·.id) =
      ["levin1993_ubpo_wave", "levin1993_co_laugh", "levin1993_pp_sleep",
       "levin1993_pp_talk"] := by decide

-- ════════════════════════════════════════════════════
-- § 3. The §0.4 diagnostic quadruple
-- ════════════════════════════════════════════════════

/-- Participation pattern of a verb across the four §0.4 alternations
    (CI, middle, conative, BPPA). -/
def quadruplePattern (rows : List LinguisticExample) : List (Option Bool) :=
  rows.map observed

/-- Each verb of the quadruple shows a pairwise distinct pattern across the
    four alternations — Levin's §0.4 table has no repeated rows, so the four
    verbs instantiate four distinct verb classes. -/
theorem quadruple_patterns_distinct :
    [quadruplePattern [Examples.ci_break, Examples.mid_break,
       Examples.con_break, Examples.bppa_break],
     quadruplePattern [Examples.ci_cut, Examples.mid_cut,
       Examples.con_cut, Examples.bppa_cut],
     quadruplePattern [Examples.ci_hit, Examples.mid_hit,
       Examples.con_hit, Examples.bppa_hit],
     quadruplePattern [Examples.ci_touch, Examples.mid_touch,
       Examples.con_touch, Examples.bppa_touch]].Pairwise (· ≠ ·) := by decide

-- ════════════════════════════════════════════════════
-- § 4. Fragment connection
-- ════════════════════════════════════════════════════

/-! Each Fragment verb entry's `levinClass` matches the class recorded on
    its alternation rows. -/

theorem break_class_matches : break_.levinClass = classOf Examples.ci_break := by decide
theorem cut_class_matches : cut.levinClass = classOf Examples.ci_cut := by decide
theorem hit_class_matches : hit.levinClass = classOf Examples.ci_hit := by decide
theorem touch_class_matches : touch.levinClass = classOf Examples.ci_touch := by decide
theorem push_class_matches : push.levinClass = classOf Examples.con_push := by decide
theorem spray_class_matches : spray.levinClass = classOf Examples.loc_spray := by decide
theorem load_class_matches : load.levinClass = classOf Examples.loc_load := by decide
theorem give_class_matches : give.levinClass = classOf Examples.dat_give := by decide
theorem send_class_matches : send.levinClass = classOf Examples.dat_send := by decide

-- ════════════════════════════════════════════════════
-- § 5. Bridge to [dowty-1991] §9.3: three verb classes
-- ════════════════════════════════════════════════════

/-! [dowty-1991] §9.3 derives the alternation behavior of the spray/load,
    *break*, and *hit* classes from the distribution of the change-of-state
    entailment across non-subject arguments: symmetric CoS permits
    alternation, asymmetric CoS fixes the CoS argument as direct object.
    Levin's judgment rows confirm each prediction. -/

/-- Spray/load: CoS is symmetric across theme and location, predicting the
    locative alternation — attested for both *spray* and *load*. -/
theorem dowty_sprayLoad_symmetry_matches_data :
    Dowty1991.cosSymmetric Dowty1991.sprayLoadTheme Dowty1991.sprayLoadLocation = true
    ∧ observed Examples.loc_spray = some true
    ∧ observed Examples.loc_load = some true := by decide

/-- *Break*: CoS is asymmetric (direct object vs. instrument), fixing the
    CoS argument as direct object — *break* lacks the locative alternation. -/
theorem dowty_break_asymmetry_matches_prediction :
    Dowty1991.cosSymmetric Dowty1991.breakDirectObject Dowty1991.breakInstrument = false
    ∧ LevinClass.break_.participatesIn .locative = false := by decide

/-- *Hit*: both arguments symmetrically lack CoS — the conative is attested
    while the CoS-sensitive causative/inchoative and middle are blocked. -/
theorem dowty_hit_class_matches_data :
    Dowty1991.cosSymmetric Dowty1991.hitArg1 Dowty1991.hitArg2 = true
    ∧ observed Examples.con_hit = some true
    ∧ observed Examples.ci_hit = some false
    ∧ observed Examples.mid_hit = some false := by decide

end Levin1993
