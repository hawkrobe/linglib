import Linglib.Phenomena.Comparison.Studies.Wellwood2015.Data
import Linglib.Theories.Semantics.Lexical.Measurement
import Linglib.Theories.Semantics.Events.ThematicRoles

/-!
# Wellwood (2015): Theory–Data Bridge

@cite{wellwood-2015}

Per-datum verification that `Measurement.lean`'s mereological status
classification predicts the empirical felicity patterns in `Data.lean`.

The bridge function `lexCatToStatus` maps each `LexCat` to a
`MereologicalStatus` using the theory's cross-categorial bridges
(`telicityToStatus`, `numberToStatus`, `gradableToStatus`,
`nonGradableToStatus`). The prediction: `.cumulative` categories
are felicitous with `much`, `.quantized` categories are not.

The grammar shift bridges (§4) ground Wellwood's §5 in the existing
`AspectualProfile.telicize` / `.atelicize` operations from
`Lexical.Verb.Aspect`, showing that grammatical shifts that change
telicity also change measurement status.

-/

namespace Phenomena.Comparison.Wellwood2015.Bridge

open Phenomena.Comparison.Wellwood2015
open Semantics.Lexical.Measurement
open Semantics.Lexical.Verb.Aspect (AspectualProfile)

-- ════════════════════════════════════════════════════
-- § 1. Theory Prediction
-- ════════════════════════════════════════════════════

/-- Map `LexCat` to `MereologicalStatus` using the theory's bridges. -/
def lexCatToStatus : LexCat → MereologicalStatus
  | .massNoun       => numberToStatus .mass
  | .countNoun      => numberToStatus .sg
  | .atelicVP       => telicityToStatus .atelic
  | .telicVP        => telicityToStatus .telic
  | .gradableAdj    => gradableToStatus
  | .nonGradableAdj => nonGradableToStatus

/-- The theory predicts: cumulative → felicitous with `much`. -/
def statusPredictsFelicitous : MereologicalStatus → Bool
  | .cumulative => true
  | .quantized  => false

-- ════════════════════════════════════════════════════
-- § 2. Per-Datum Felicity Bridges
-- ════════════════════════════════════════════════════

/-- Mass nouns: theory predicts cumulative → felicitous. ✓ -/
theorem massNoun_felicity :
    statusPredictsFelicitous (lexCatToStatus .massNoun) =
      massNounDatum.felicitousWithMuch := rfl

/-- Count nouns: theory predicts quantized → not felicitous. ✓ -/
theorem countNoun_felicity :
    statusPredictsFelicitous (lexCatToStatus .countNoun) =
      countNounDatum.felicitousWithMuch := rfl

/-- Atelic VPs: theory predicts cumulative → felicitous. ✓ -/
theorem atelicVP_felicity :
    statusPredictsFelicitous (lexCatToStatus .atelicVP) =
      atelicVPDatum.felicitousWithMuch := rfl

/-- Telic VPs: theory predicts quantized → not felicitous. ✓ -/
theorem telicVP_felicity :
    statusPredictsFelicitous (lexCatToStatus .telicVP) =
      telicVPDatum.felicitousWithMuch := rfl

/-- Gradable adjectives: theory predicts cumulative → felicitous. ✓ -/
theorem gradableAdj_felicity :
    statusPredictsFelicitous (lexCatToStatus .gradableAdj) =
      gradableAdjDatum.felicitousWithMuch := rfl

/-- Non-gradable adjectives: theory predicts quantized → not felicitous. ✓ -/
theorem nonGradableAdj_felicity :
    statusPredictsFelicitous (lexCatToStatus .nonGradableAdj) =
      nonGradableAdjDatum.felicitousWithMuch := rfl

-- ════════════════════════════════════════════════════
-- § 3. Cross-Categorial Parallel Bridge
-- ════════════════════════════════════════════════════

/-- Mass nouns and atelic VPs share the same mereological status. -/
theorem massNoun_atelicVP_same_status :
    lexCatToStatus .massNoun = lexCatToStatus .atelicVP := rfl

/-- Count nouns and telic VPs share the same mereological status. -/
theorem countNoun_telicVP_same_status :
    lexCatToStatus .countNoun = lexCatToStatus .telicVP := rfl

/-- Gradable adjectives share status with mass nouns and atelic VPs. -/
theorem gradableAdj_patterns_with_cum :
    lexCatToStatus .gradableAdj = lexCatToStatus .massNoun := rfl

/-- Non-gradable adjectives share status with count nouns and telic VPs. -/
theorem nonGradableAdj_patterns_with_qua :
    lexCatToStatus .nonGradableAdj = lexCatToStatus .countNoun := rfl

-- ════════════════════════════════════════════════════
-- § 4. Grammar Shift Bridges
-- ════════════════════════════════════════════════════

/-- "ran in the park" → "ran to the park" (Wellwood ex. 105):
    telicization via `AspectualProfile.telicize` shifts cumulative → quantized.
    Extensive dimensions (DURATION, DISTANCE) → blocked; only NUMBER available.

    This grounds the grammar shift datum in the existing aspectual shift
    infrastructure rather than asserting it by fiat: `telicize_shifts_status`
    proves that the shift follows from the telicity change. -/
theorem run_shift_via_telicize :
    let p : AspectualProfile := Semantics.Lexical.Verb.Aspect.activityProfile
    telicityToStatus p.telicity = .cumulative ∧
    telicityToStatus p.telicize.telicity = .quantized :=
  telicize_shifts_status _ rfl

/-- "was building the house" → "built the house" (progressive removal):
    atelicization via `AspectualProfile.atelicize` shifts quantized → cumulative.
    Extensive dimensions restored. -/
theorem build_shift_via_atelicize :
    let p : AspectualProfile := Semantics.Lexical.Verb.Aspect.accomplishmentProfile
    telicityToStatus p.telicity = .quantized ∧
    telicityToStatus p.atelicize.telicity = .cumulative :=
  atelicize_shifts_status _ rfl

/-- rock → rocks: mass (cumulative) → count (quantized).
    Number morphology restricts measurement to NUMBER. -/
theorem rock_shift_status :
    lexCatToStatus .massNoun = .cumulative ∧
    lexCatToStatus .countNoun = .quantized := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Boundedness Bridge
-- ════════════════════════════════════════════════════

/-- All cumulative categories map to open scales; all quantized categories
    map to closed scales. This connects the per-datum felicity predictions
    to Kennedy's (2007) scale structure. -/
theorem massNoun_open_scale :
    (lexCatToStatus .massNoun).toBoundedness = .open_ := rfl

theorem countNoun_closed_scale :
    (lexCatToStatus .countNoun).toBoundedness = .closed := rfl

theorem atelicVP_open_scale :
    (lexCatToStatus .atelicVP).toBoundedness = .open_ := rfl

theorem telicVP_closed_scale :
    (lexCatToStatus .telicVP).toBoundedness = .closed := rfl

-- ════════════════════════════════════════════════════
-- § 6. Dimension Reversal Bridges (§3.4)
-- ════════════════════════════════════════════════════

/-- Dimension type tracks measured domain, not lexical category.
    States are dimensionally restricted (single dimension available);
    entities and events are not (multiple dimensions available).

    This is the prediction function for Wellwood's §3.4 argument:
    - `hot`/`hard` (GA) and `heat`/`firmness` (noun) both access
      intensive dimensions because both measure states.
    - `full`/`heavy` (GA) and `coffee`/`plastic` (noun) both access
      extensive dimensions because both measure entities.
    - The syntactic category is irrelevant to dimension type. -/
def measuredDomainRestricted : MeasuredDomain → Bool
  | .state  => true
  | .entity => false
  | .event  => false

/-- (82a) "hotter": GA measuring states → dimensionally restricted. ✓ -/
theorem hotter_restricted :
    measuredDomainRestricted hotterDatum.measuredDomain = hotterDatum.intensive := rfl

/-- (82b) "harder": GA measuring states → dimensionally restricted. ✓ -/
theorem harder_restricted :
    measuredDomainRestricted harderDatum.measuredDomain = harderDatum.intensive := rfl

/-- (83a) "more coffee": mass noun measuring entities → not restricted. ✓ -/
theorem moreCoffee_not_restricted :
    measuredDomainRestricted moreCoffeeDatum.measuredDomain = moreCoffeeDatum.intensive := rfl

/-- (83b) "more plastic": mass noun measuring entities → not restricted. ✓ -/
theorem morePlastic_not_restricted :
    measuredDomainRestricted morePlasticDatum.measuredDomain = morePlasticDatum.intensive := rfl

/-- (84a) "fuller": GA measuring entities → NOT restricted.
    **Reversal**: GA but extensive, because measured domain is entity. ✓ -/
theorem fuller_not_restricted :
    measuredDomainRestricted fullerDatum.measuredDomain = fullerDatum.intensive := rfl

/-- (84b) "heavier": GA measuring entities → NOT restricted.
    **Reversal**: GA but extensive, because measured domain is entity. ✓ -/
theorem heavier_not_restricted :
    measuredDomainRestricted heavierDatum.measuredDomain = heavierDatum.intensive := rfl

/-- (85a) "more heat": mass noun measuring states → restricted.
    **Reversal**: noun but intensive, because measured domain is state. ✓ -/
theorem moreHeat_restricted :
    measuredDomainRestricted moreHeatDatum.measuredDomain = moreHeatDatum.intensive := rfl

/-- (85b) "more firmness": mass noun measuring states → restricted.
    **Reversal**: noun but intensive, because measured domain is state. ✓ -/
theorem moreFirmness_restricted :
    measuredDomainRestricted moreFirmnessDatum.measuredDomain = moreFirmnessDatum.intensive := rfl

/-- (89a) "sped up more": atelic VP measuring states → restricted.
    **Reversal**: verb but intensive, because measured domain is state. ✓ -/
theorem spedUpMore_restricted :
    measuredDomainRestricted spedUpMoreDatum.measuredDomain = spedUpMoreDatum.intensive := rfl

/-- (87a) "drove more": atelic VP measuring events → not restricted. ✓ -/
theorem droveMore_not_restricted :
    measuredDomainRestricted droveMoreDatum.measuredDomain = droveMoreDatum.intensive := rfl

-- ════════════════════════════════════════════════════
-- § 7. State Modification Bridge (§3.5)
-- ════════════════════════════════════════════════════

open Semantics.Events (Ev EvPred)
open Semantics.Events.ThematicRoles (ThematicFrame EventModifier
  modifiedStativeLogicalForm stativeLogicalForm modify modified_stative_is_pm)

/-- State modification data (§3.5) confirms that stative predicates
    support event modification via conjunction (Predicate Modification),
    just as dynamic predicates do.

    The PM equivalence `modified_stative_is_pm` from ThematicRoles grounds
    this observation: "happy in the morning" has logical form
    ∃s. happy(s) ∧ Holder(x,s) ∧ in-the-morning(s), which is equivalently
    `stativeLogicalForm (modify happy in-the-morning) frame x`.

    This is the bridge between the empirical observation (states can be
    modified) and the theoretical prediction (states are eventualities,
    so Davidson's event modification applies to them). -/
theorem state_mod_pm_bridge {Entity Time : Type*} [LE Time]
    (P : EvPred Time) (frame : ThematicFrame Entity Time)
    (x : Entity) (M : EventModifier Time) :
    modifiedStativeLogicalForm P frame x M ↔
      stativeLogicalForm (modify P M) frame x :=
  modified_stative_is_pm P frame x M

end Phenomena.Comparison.Wellwood2015.Bridge
