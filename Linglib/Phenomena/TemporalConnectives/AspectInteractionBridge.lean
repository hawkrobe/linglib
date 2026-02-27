import Linglib.Theories.Semantics.Tense.TemporalConnectives
import Linglib.Theories.Semantics.Events.TemporalDecomposition
import Linglib.Fragments.English.TemporalExpressions
import Linglib.Phenomena.TemporalConnectives.AspectInteractionData

/-!
# Aspect × Temporal Connective Interaction Bridge

Connects three layers:

1. **Fragment field**: `TemporalExprEntry.embeddedTelicityEffect : Bool`
2. **Theory**: `VendlerClass.telicity`, `INCHOAT`, `COMPLET` operators
3. **Data**: `AspectInteraction` judgments from Moens & Steedman (1988)

## What This File Proves

1. `embeddedTelicityEffect = true` holds exactly for connectives whose truth
   conditions change depending on the Vendler class of the embedded clause
   (*before*, *after*). This is because they reference boundary points
   (onset/telos) that depend on aspect.

2. `embeddedTelicityEffect = false` holds for connectives that use overlap
   or containment semantics (*while*, *when*, *until*, *since*), which are
   insensitive to the internal temporal structure of the embedded clause.

3. The `triggeredCoercion` field is grounded in the theory's `INCHOAT` and
   `COMPLET` operators: INCHOAT extracts the onset point (= `CoSType.inception`),
   COMPLET extracts the telos (= `CoSType.cessation`).

4. The `satisfiesDurativeRestriction` predicate (from Data) coincides with
   `VendlerClass.toProfile.isHomogeneous`: exactly states and activities
   satisfy the durative requirement for *until* and *since* main clauses.

## The Explanatory Chain

```
VendlerClass.telicity          TemporalExprEntry.embeddedTelicityEffect
  .telic / .atelic  ──────────► true (before, after: reading depends on telicity)
                                false (while, when, until, since: insensitive)

VendlerClass.duration          *until*/*since* selectional restriction
  .durative  ─────────────────► satisfiesDurativeRestriction = true  (OK)
  .punctual  ─────────────────► satisfiesDurativeRestriction = false (BAD)

INCHOAT / COMPLET              Fragment.triggeredCoercion
  INCHOAT(stative) = onset ───► "INCHOAT" for within_, after_ (coerced)
  COMPLET(telic) = telos ─────► "COMPLET" for at_punct, before_ (coerced)
```

## References

- Moens, M. & Steedman, M. (1988). Temporal ontology and temporal reference.
- Rett, J. (2020). Eliminating EARLIEST.
- Alstott, A. & Aravind, A. (2026). Aspectual coercion in *before*/*after*-clauses.
-/

namespace Phenomena.TemporalConnectives.AspectInteractionBridge

open Semantics.Lexical.Verb.Aspect
open Semantics.Tense.TemporalConnectives
open Fragments.English.TemporalExpressions
open Phenomena.TemporalConnectives.AspectInteractionData
open Core.Time
open Core.Time.Interval

-- ============================================================================
-- § 1: Telicity Sensitivity Pattern
-- ============================================================================

/-- `embeddedTelicityEffect = true` holds exactly for connectives that
    reference boundary points (onset/telos) of the embedded clause.
    These are *before* and *after*: their truth conditions change depending
    on whether the embedded clause is telic or atelic, because:
    - Telic → natural endpoint exists → COMPLET/INCHOAT not needed
    - Atelic → no natural endpoint → coercion needed for endpoint reading -/
theorem telicity_sensitivity_pattern :
    -- Sensitive: truth conditions depend on embedded telicity
    before_.embeddedTelicityEffect = true ∧
    after_.embeddedTelicityEffect = true ∧
    -- Insensitive: overlap/containment semantics, no endpoint reference
    while_conn.embeddedTelicityEffect = false ∧
    until_.embeddedTelicityEffect = false ∧
    when_conn.embeddedTelicityEffect = false ∧
    since_conn.embeddedTelicityEffect = false ∧
    till_conn.embeddedTelicityEffect = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The telicity sensitivity split corresponds to the ordering direction:
    connectives with `order ∈ {before, after}` are telicity-sensitive;
    overlap/persistence connectives are not. -/
theorem telicity_sensitivity_iff_ordering :
    (before_.order == .before) = before_.embeddedTelicityEffect ∧
    (after_.order == .after) = after_.embeddedTelicityEffect ∧
    (while_conn.order == .before || while_conn.order == .after) =
      while_conn.embeddedTelicityEffect ∧
    (until_.order == .before || until_.order == .after) =
      until_.embeddedTelicityEffect ∧
    (when_conn.order == .before || when_conn.order == .after) =
      when_conn.embeddedTelicityEffect :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 2: Fragment ↔ Data Agreement
-- ============================================================================

/-- The Fragment's `embeddedTelicityEffect` for *before* is consistent with
    the data: *before* + stative is acceptable without coercion (default
    before-start reading), but *before* + accomplishment has a coerced
    alternative (before-finish via COMPLET). -/
theorem before_telicity_data_agree :
    before_.embeddedTelicityEffect = true ∧
    before_stative.acceptableWithout = true ∧
    before_accomplishment.coercionType = some "COMPLET" :=
  ⟨rfl, rfl, rfl⟩

/-- The Fragment's `embeddedTelicityEffect` for *after* is consistent with
    the data: *after* + accomplishment is default (after-finish), but
    *after* + stative has a coerced alternative (after-start via INCHOAT). -/
theorem after_telicity_data_agree :
    after_.embeddedTelicityEffect = true ∧
    after_accomplishment.acceptableWithout = true ∧
    after_stative.coercionType = some "INCHOAT" :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 3: Durative Selectional Restriction ↔ VendlerClass
-- ============================================================================

/-- The `satisfiesDurativeRestriction` predicate from the data layer is
    equivalent to the theory's `isHomogeneous` predicate on the canonical
    VendlerClass profile. This grounds the data-level predicate in the
    theory-level aspectual feature system. -/
theorem durative_restriction_is_homogeneity (c : VendlerClass) :
    satisfiesDurativeRestriction c = c.toProfile.isHomogeneous :=
  durative_restriction_iff_homogeneous c

/-- The *until* interaction data matches VendlerClass predictions:
    acceptable iff homogeneous (state or activity). -/
theorem until_selectional_restriction_grounded :
    -- Acceptable: homogeneous classes
    until_state_main.acceptableWithout = VendlerClass.state.toProfile.isHomogeneous ∧
    until_activity_main.acceptableWithout = VendlerClass.activity.toProfile.isHomogeneous ∧
    -- Degraded: non-homogeneous classes
    until_achievement_main.acceptableWithout = VendlerClass.achievement.toProfile.isHomogeneous ∧
    until_accomplishment_main.acceptableWithout =
      VendlerClass.accomplishment.toProfile.isHomogeneous :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 4: Coercion Operators ↔ Aspect Features
-- ============================================================================

/-- INCHOAT extracts the onset of an atelic/stative denotation.
    The theory proves this equals the start point — connecting the
    Fragment's `triggeredCoercion = "INCHOAT"` to concrete behavior. -/
theorem inchoat_extracts_onset (i : Interval ℕ) :
    INCHOAT (stativeDenotation i) = { j | j = Interval.point i.start } :=
  inchoat_bridges_inception i

/-- COMPLET extracts the telos of a telic denotation.
    The theory proves this equals the finish point — connecting the
    Fragment's `triggeredCoercion = "COMPLET"` to concrete behavior. -/
theorem complet_extracts_telos (i : Interval ℕ) :
    COMPLET (accomplishmentDenotation i) = { j | j = Interval.point i.finish } :=
  complet_bridges_cessation i

/-- The Fragment entries that specify `triggeredCoercion` are exactly those
    that need aspectual adjustment for their complement type:
    - `within_` triggers INCHOAT (needs onset of duration)
    - `at_punct` triggers COMPLET (needs telos of telic event)
    - *before*/*after* have `triggeredCoercion = none` because they have
      both default and coerced readings (specified via `coercedReading`). -/
theorem triggered_coercion_entries :
    within_.triggeredCoercion = some "INCHOAT" ∧
    at_punct.triggeredCoercion = some "COMPLET" ∧
    before_.triggeredCoercion = none ∧
    after_.triggeredCoercion = none :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 5: *When* Coercion ↔ VendlerClass Punctuality
-- ============================================================================

/-- *When* accepts states and achievements without coercion: states are
    homogeneous (any subinterval works for overlap), and achievements
    are already punctual. Activities and accomplishments require coercion
    to achievement because *when* selects a single reference point. -/
theorem when_coercion_from_vendler :
    -- No coercion needed: already compatible
    when_state.acceptableWithout = true ∧      -- homogeneous
    when_achievement.acceptableWithout = true ∧ -- already punctual
    -- Coercion needed: not compatible
    when_activity.acceptableWithout = false ∧
    when_accomplishment.acceptableWithout = false ∧
    -- Coercion target is always achievement
    when_activity.resultClass = some .achievement ∧
    when_accomplishment.resultClass = some .achievement :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- *When*'s coercion need correlates with the Vendler class:
    classes that are either stative or punctual need no coercion.
    This is because *when* selects a reference point, and statives
    trivially provide one (any subinterval) while achievements
    ARE a single point. -/
def whenCompatible (c : VendlerClass) : Bool :=
  c == .state || c == .achievement

theorem when_compatible_iff_no_coercion :
    whenCompatible .state = true ∧
    whenCompatible .achievement = true ∧
    whenCompatible .activity = false ∧
    whenCompatible .accomplishment = false :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 6: Coercion Network ↔ Aspectual Shift Operations
-- ============================================================================

/-- Moens & Steedman's "strip-process" coercion (accomplishment → achievement)
    corresponds to the theory's telicize-then-punctualize, but more precisely
    it is the inverse of `duratize`: it removes duration. -/
theorem strip_process_matches :
    stripProcess.source = .accomplishment ∧
    stripProcess.target = .achievement ∧
    VendlerClass.accomplishment.duration = .durative ∧
    VendlerClass.achievement.duration = .punctual :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Moens & Steedman's "add-result" coercion (activity → accomplishment)
    corresponds to the theory's `telicize` operation:
    adding a natural endpoint to an atelic predicate. -/
theorem add_result_matches_telicize :
    addResult.source = .activity ∧
    addResult.target = .accomplishment ∧
    activityProfile.telicize.toVendlerClass = .accomplishment :=
  ⟨rfl, rfl, rfl⟩

/-- Moens & Steedman's "iterate" coercion (achievement → activity)
    corresponds to the theory's `duratize ∘ atelicize`:
    stretching a punctual event over time and removing the endpoint. -/
theorem iterate_matches_duratize :
    iterate_.source = .achievement ∧
    iterate_.target = .activity ∧
    achievementProfile.duratize.toVendlerClass = .accomplishment ∧
    -- After duratize + atelicize: activity
    (achievementProfile.duratize.atelicize).toVendlerClass = .activity :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 7: When-Coercion ↔ M&S Event Types
-- ============================================================================

open Semantics.Events (MoensSteedmanClass WhenTarget)

/-- M&S's unified *when*-semantics agrees with the empirical coercion
    pattern: *when* needs no coercion iff `whenCompatible` is true.
    The M&S analysis *explains* the pattern: states are compatible
    because they're homogeneous; achievements because they already ARE
    culmination points. Processes and accomplishments require coercion
    because *when* must access a culmination they don't directly provide. -/
theorem ms_when_agrees_with_data (c : MoensSteedmanClass) :
    (c.whenTarget = .directCulmination ∨ c.whenTarget = .homogeneousOverlap) ↔
    (whenCompatible c.toProfile.toVendlerClass = true) := by
  cases c <;> simp [MoensSteedmanClass.whenTarget, MoensSteedmanClass.toProfile,
    stateProfile, activityProfile, achievementProfile, accomplishmentProfile,
    AspectualProfile.toVendlerClass, whenCompatible] <;> decide

/-- M&S's coercion type matches the data layer: inception coercion
    targets processes (= Vendler activities), completion coercion targets
    culminated processes (= Vendler accomplishments). -/
theorem ms_coercion_type_matches :
    -- Inception (INCHOAT): process onset
    (MoensSteedmanClass.process.whenTarget = .inceptionCoercion ∧
     when_activity.coercionType = some "inception") ∧
    -- Completion (strip-process): culminated process telos
    (MoensSteedmanClass.culminatedProcess.whenTarget = .completionCoercion ∧
     when_accomplishment.coercionType = some "culmination") :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end Phenomena.TemporalConnectives.AspectInteractionBridge
