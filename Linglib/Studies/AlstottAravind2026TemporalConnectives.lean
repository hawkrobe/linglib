import Linglib.Studies.Rett2020
import Linglib.Semantics.Aspect.SubeventStructure
import Linglib.Fragments.English.TemporalExpressions
import Linglib.Data.Examples.MoensSteedman1988
import Linglib.Data.Examples.Karttunen1974
import Linglib.Data.Examples.AlstottAravind2026

/-!
# Aspect × Temporal Connective Interaction Bridge
[alstott-aravind-2026] [moens-steedman-1988] [karttunen-1974] [rett-2020]

Connects three layers:

1. **Fragment**: `TemporalExprEntry` fields (`embeddedTelicityEffect`,
   `defaultReading`, `coercedReading`, `triggeredCoercion`)
2. **Theory**: `VendlerClass` features, `INCHOAT`/`COMPLET`, and
   `MoensSteedmanClass.whenTarget`
3. **Data**: per-paper rows in `Data.Examples.{MoensSteedman1988,
   Karttunen1974, AlstottAravind2026}`

## Main declarations

- `vendlerOf`: adapter reading a row's `paperFeatures`
- `coercion_tracks_embedded_telicity`: a *before*/*after* row records a
  coercion operator exactly when the connective × embedded-telicity pair
  demands one (COMPLET for *before* + telic, INCHOAT for *after* + atelic)
- `satisfiesDurativeRestriction`, `until_acceptable_iff_durative`: Karttunen's
  durative selectional restriction, derived from Vendler features, predicts
  each *until* row's acceptability
- `when_coercion_matches_ms`: each *when* row's coercion annotation is the
  one `MoensSteedmanClass.whenTarget` predicts for its Vendler class
- `inchoat_extracts_onset`, `complet_extracts_telos`: the Fragment's coercion
  labels grounded in the operators' interval-set behavior
-/

namespace AlstottAravind2026TemporalConnectives

open Features
open Tense.TemporalConnectives
open English.TemporalExpressions
open Data.Examples
open Core.Order
open NonemptyInterval
open Semantics.Aspect.SubeventStructure (MoensSteedmanClass WhenTarget)

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
-- § 2: Row Adapters
-- ============================================================================

/-- Vendler-class adapter: the row's `vendler_class` feature. -/
def vendlerOf (row : LinguisticExample) : Option VendlerClass :=
  match row.feature? "vendler_class" with
  | some "state"          => some .state
  | some "activity"       => some .activity
  | some "achievement"    => some .achievement
  | some "accomplishment" => some .accomplishment
  | some "semelfactive"   => some .semelfactive
  | _ => none

-- ============================================================================
-- § 3: *Before*/*After* — Coercion Tracks Embedded Telicity
-- ============================================================================

/-- The coercion operator a *before*/*after* clause needs for its non-default
    reading: COMPLET (telos extraction) for *before* + telic embedded clauses,
    INCHOAT (onset extraction) for *after* + atelic embedded clauses; the
    remaining combinations have only the default reading. -/
def expectedCoercion (conn : String) (c : VendlerClass) : Option String :=
  match conn, c.telicity with
  | "before", .telic  => some "COMPLET"
  | "after",  .atelic => some "INCHOAT"
  | _, _ => none

/-- **Transfer equation** over the *before*/*after* rows: a row records a
    coercion operator exactly when its connective × embedded-telicity pair
    demands one. The two coerced cells are the conditions tested in
    [alstott-aravind-2026]'s Exps 2 (COMPLET) and 4 (INCHOAT). -/
theorem coercion_tracks_embedded_telicity :
    ∀ row ∈ AlstottAravind2026.Examples.all,
      row.feature? "coercion" =
        (row.feature? "connective").bind fun conn =>
          (vendlerOf row).bind fun c => expectedCoercion conn c := by
  decide

/-- The rows' recorded default readings are the Fragment's defaults:
    before-start for *before*, after-finish for *after* ([rett-2020]'s
    strong defaults). -/
theorem default_reading_matches_fragment :
    before_.defaultReading = .beforeStart ∧
    after_.defaultReading = .afterFinish ∧
    ∀ row ∈ AlstottAravind2026.Examples.all,
      row.feature? "default_reading" =
        (row.feature? "connective").bind fun conn =>
          if conn = "before" then some "before-start"
          else if conn = "after" then some "after-finish"
          else none :=
  ⟨rfl, rfl, by decide⟩

/-- A row records a coerced reading exactly when it records a coercion
    operator, and the reading is the Fragment's `coercedReading`:
    before-finish under COMPLET, after-start under INCHOAT. -/
theorem coerced_reading_matches_fragment :
    before_.coercedReading = some .beforeFinish ∧
    after_.coercedReading = some .afterStart ∧
    ∀ row ∈ AlstottAravind2026.Examples.all,
      row.feature? "coerced_reading" =
        (row.feature? "coercion").bind fun op =>
          if op = "COMPLET" then some "before-finish"
          else if op = "INCHOAT" then some "after-start"
          else none :=
  ⟨rfl, rfl, by decide⟩

-- ============================================================================
-- § 4: *Until* — Durative Selectional Restriction
-- ============================================================================

/-- [karttunen-1974]'s durative selectional restriction on *until*/*since*
    main clauses, derived from the Vendler feature decomposition: atelic and
    durative — exactly the subinterval-property (homogeneous) classes. -/
def satisfiesDurativeRestriction (c : VendlerClass) : Bool :=
  c.telicity == .atelic && c.duration == .durative

/-- The durative restriction picks out exactly states and activities. -/
theorem durative_restriction_iff_state_or_activity (c : VendlerClass) :
    satisfiesDurativeRestriction c = true ↔ c = .state ∨ c = .activity := by
  cases c <;> decide

/-- **Transfer equation** over the *until* main-clause rows: a row is
    acceptable iff its main clause's Vendler class satisfies the durative
    restriction. -/
theorem until_acceptable_iff_durative :
    ∀ row ∈ Karttunen1974.Examples.all,
      (row.judgment = .acceptable ↔
        (vendlerOf row).map satisfiesDurativeRestriction = some true) := by
  decide

-- ============================================================================
-- § 5: Coercion Operators ↔ Aspect Features
-- ============================================================================

/-- INCHOAT extracts the onset of an atelic/stative denotation.
    The theory proves this equals the start point — connecting the
    Fragment's `triggeredCoercion = "INCHOAT"` to concrete behavior. -/
theorem inchoat_extracts_onset (i : NonemptyInterval ℕ) :
    INCHOAT (stativeDenotation i) = { j | j = NonemptyInterval.pure i.fst } :=
  inchoat_bridges_inception i

/-- COMPLET extracts the telos of a telic denotation.
    The theory proves this equals the finish point — connecting the
    Fragment's `triggeredCoercion = "COMPLET"` to concrete behavior. -/
theorem complet_extracts_telos (i : NonemptyInterval ℕ) :
    COMPLET (accomplishmentDenotation i) = { j | j = NonemptyInterval.pure i.snd } :=
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
-- § 6: *When* — Coercion Predicted by M&S Event Types
-- ============================================================================

/-- Embed Vendler classes into [moens-steedman-1988] event types
    (achievements as culminations, semelfactives as points; the two M&S
    atomic types collapse to `achievement` at Vendler granularity). -/
def msOf : VendlerClass → MoensSteedmanClass
  | .state          => .state
  | .activity       => .process
  | .accomplishment => .culminatedProcess
  | .achievement    => .culmination
  | .semelfactive   => .point

/-- The coercion a *when*-clause triggers for each `WhenTarget`: inception
    coercion for processes, completion coercion for culminated processes,
    and none where the event directly supplies a reference point. -/
def whenCoercionLabel : WhenTarget → Option String
  | .inceptionCoercion  => some "inception"
  | .completionCoercion => some "culmination"
  | .directCulmination | .homogeneousOverlap => none

/-- **Transfer equation** over the *when* rows: each row's coercion
    annotation is exactly the one `MoensSteedmanClass.whenTarget` predicts
    for its Vendler class. States need no coercion (homogeneous overlap),
    achievements ARE culmination points, activities coerce to their onset,
    accomplishments to their telos. -/
theorem when_coercion_matches_ms :
    ∀ row ∈ MoensSteedman1988.Examples.all,
      row.feature? "coercion" =
        (vendlerOf row).bind fun c => whenCoercionLabel (msOf c).whenTarget := by
  decide

/-- When *when* coerces, the result is punctual: every coerced *when* row
    records achievement as its result class. -/
theorem when_coercion_targets_achievement :
    ∀ row ∈ MoensSteedman1988.Examples.all,
      (row.feature? "coercion").isSome →
        row.feature? "result_class" = some "achievement" := by
  decide

-- ============================================================================
-- § 7: M&S Coercion Network ↔ Aspectual Shift Operations
-- ============================================================================

/-- [moens-steedman-1988] Fig. 2's "add-result" transition
    (process → culminated process) is the theory's `telicize`: adding a
    natural endpoint to an activity yields an accomplishment. -/
theorem add_result_is_telicize :
    activityProfile.telicize.toVendlerClass = .accomplishment := rfl

/-- Fig. 2's iteration transition (point → process) at Vendler granularity
    is `duratize` followed by `atelicize`: stretching a punctual event over
    time and removing the endpoint yields an activity. -/
theorem iterate_is_duratize_atelicize :
    (achievementProfile.duratize.atelicize).toVendlerClass = .activity := rfl

end AlstottAravind2026TemporalConnectives
