import Linglib.Theories.Semantics.Lexical.Verb.Aspect

/-!
# Aspect × Temporal Connective Interaction Data
@cite{moens-steedman-1988} @cite{vendler-1957}Theory-neutral empirical data on how temporal connectives interact with the
aspectual class (Vendler class) of their complement and main clauses.

## Key Empirical Generalizations (Moens & Steedman 1988)

1. **Selectional restrictions**: *until* and *since* require durative
   (stative/activity) main clauses. *When* triggers coercion to punctual.

2. **Coercion effects**: When a connective's selectional requirements
   conflict with the clause's Vendler class, aspectual coercion occurs:
   - *when* + accomplishment → culmination (achievement) reading
   - *when* + activity → inception reading ("just when he was running")
   - *before*/*after* + stative → inchoative (onset) extraction
   - *until* + achievement → degraded / requires coercion to iterative

3. **Telicity sensitivity**: *before* and *after* have different default
   readings depending on embedded clause telicity:
   - Telic embedded clause → endpoint reading is default
   - Atelic embedded clause → onset reading requires coercion (INCHOAT)

-/

namespace Phenomena.TemporalConnectives.AspectInteractionData

open Semantics.Lexical.Verb.Aspect

-- ============================================================================
-- § 1: Connective × Aspect Interaction Judgments
-- ============================================================================

/-- Acceptability of a temporal connective with a given Vendler class,
    and what coercion (if any) the combination triggers. -/
structure AspectInteraction where
  /-- The temporal connective -/
  connective : String
  /-- Vendler class of the relevant clause -/
  vendlerClass : VendlerClass
  /-- Whether this is about the main clause or the embedded clause -/
  clause : String  -- "main" or "embedded"
  /-- Is the combination acceptable without coercion? -/
  acceptableWithout : Bool
  /-- If coercion is needed, what kind? -/
  coercionType : Option String
  /-- Resulting Vendler class after coercion (if any) -/
  resultClass : Option VendlerClass
  /-- Example sentence -/
  example_ : String
  deriving Repr

-- ============================================================================
-- § 2: *When* + Embedded Clause (M&S 1988, §3)
-- ============================================================================

/-- *when* + state → no coercion (state persists).
    "When John knew the answer, he raised his hand." -/
def when_state : AspectInteraction where
  connective := "when"
  vendlerClass := .state
  clause := "embedded"
  acceptableWithout := true
  coercionType := none
  resultClass := none
  example_ := "When John knew the answer, he raised his hand"

/-- *when* + activity → inception coercion.
    "When John ran, the crowd cheered" → "just when John started running."
    The activity is coerced to its onset point (achievement). -/
def when_activity : AspectInteraction where
  connective := "when"
  vendlerClass := .activity
  clause := "embedded"
  acceptableWithout := false
  coercionType := some "inception"
  resultClass := some .achievement
  example_ := "When John ran, the crowd cheered"

/-- *when* + accomplishment → culmination coercion.
    "When John built the house, he sold it" → "when John finished building."
    The accomplishment is coerced to its culmination point (achievement). -/
def when_accomplishment : AspectInteraction where
  connective := "when"
  vendlerClass := .accomplishment
  clause := "embedded"
  acceptableWithout := false
  coercionType := some "culmination"
  resultClass := some .achievement
  example_ := "When John built the house, he sold it"

/-- *when* + achievement → no coercion needed (already punctual).
    "When John arrived, Mary left." -/
def when_achievement : AspectInteraction where
  connective := "when"
  vendlerClass := .achievement
  clause := "embedded"
  acceptableWithout := true
  coercionType := none
  resultClass := none
  example_ := "When John arrived, Mary left"

-- ============================================================================
-- § 3: *Until* Main Clause Restrictions (M&S 1988, §4; Karttunen 1974)
-- ============================================================================

/-- *until* + stative main clause → acceptable (canonical use).
    "John slept until 3pm." -/
def until_state_main : AspectInteraction where
  connective := "until"
  vendlerClass := .state
  clause := "main"
  acceptableWithout := true
  coercionType := none
  resultClass := none
  example_ := "John slept until 3pm"

/-- *until* + activity main clause → acceptable.
    "John ran until 3pm." -/
def until_activity_main : AspectInteraction where
  connective := "until"
  vendlerClass := .activity
  clause := "main"
  acceptableWithout := true
  coercionType := none
  resultClass := none
  example_ := "John ran until 3pm"

/-- *until* + achievement main clause → degraded.
    "*John arrived until 3pm." Achievement is punctual; *until* requires
    duration. Coercion to iterative is possible but marked. -/
def until_achievement_main : AspectInteraction where
  connective := "until"
  vendlerClass := .achievement
  clause := "main"
  acceptableWithout := false
  coercionType := some "iterative"
  resultClass := some .activity
  example_ := "*John arrived until 3pm"

/-- *until* + accomplishment main clause → degraded.
    "*John built the house until 3pm." Accomplishment has an endpoint;
    *until* provides an external boundary, creating a conflict. -/
def until_accomplishment_main : AspectInteraction where
  connective := "until"
  vendlerClass := .accomplishment
  clause := "main"
  acceptableWithout := false
  coercionType := some "atelicize"
  resultClass := some .activity
  example_ := "*John built the house until 3pm"

-- ============================================================================
-- § 4: *Before*/*After* + Embedded Clause Telicity (Rett 2020)
-- ============================================================================

/-- *before* + stative embedded → default before-start reading.
    "John left before she was president." ME precedes onset of EE. -/
def before_stative : AspectInteraction where
  connective := "before"
  vendlerClass := .state
  clause := "embedded"
  acceptableWithout := true
  coercionType := none
  resultClass := none
  example_ := "John left before she was president"

/-- *before* + accomplishment embedded → before-start is default;
    before-finish (COMPLET) reading is available with coercion cost.
    "John left before she climbed the mountain." Default: before onset.
    Coerced: before completion. (Alstott & Aravind 2026, Exp. 2) -/
def before_accomplishment : AspectInteraction where
  connective := "before"
  vendlerClass := .accomplishment
  clause := "embedded"
  acceptableWithout := true
  coercionType := some "COMPLET"
  resultClass := some .achievement
  example_ := "John left before she climbed the mountain"

/-- *after* + stative embedded → default after-finish; after-start (INCHOAT)
    requires coercion. "John left after she was surprised."
    Default: after end of surprise. Coerced: after onset.
    (Alstott & Aravind 2026, Exp. 4) -/
def after_stative : AspectInteraction where
  connective := "after"
  vendlerClass := .state
  clause := "embedded"
  acceptableWithout := true
  coercionType := some "INCHOAT"
  resultClass := some .achievement
  example_ := "John left after she was surprised"

/-- *after* + accomplishment embedded → default after-finish.
    "John left after she climbed the mountain." ME follows telos. -/
def after_accomplishment : AspectInteraction where
  connective := "after"
  vendlerClass := .accomplishment
  clause := "embedded"
  acceptableWithout := true
  coercionType := none
  resultClass := none
  example_ := "John left after she climbed the mountain"

-- ============================================================================
-- § 5: *Since* Main Clause Restrictions (Heinämäki 1974)
-- ============================================================================

/-- *since* + stative main clause → acceptable.
    "John has been happy since she arrived." -/
def since_state_main : AspectInteraction where
  connective := "since"
  vendlerClass := .state
  clause := "main"
  acceptableWithout := true
  coercionType := none
  resultClass := none
  example_ := "John has been happy since she arrived"

/-- *since* + achievement main clause → degraded.
    "*John found it since she arrived." Achievement is punctual;
    *since* requires an ongoing state from the reference point. -/
def since_achievement_main : AspectInteraction where
  connective := "since"
  vendlerClass := .achievement
  clause := "main"
  acceptableWithout := false
  coercionType := some "resultative"
  resultClass := some .state
  example_ := "*John found it since she arrived"

-- ============================================================================
-- § 6: Selectional Restriction Generalization
-- ============================================================================

/-- Whether a VendlerClass satisfies the durative selectional restriction
    required by *until* and *since* for their main clauses. -/
def satisfiesDurativeRestriction (c : VendlerClass) : Bool :=
  c.duration == .durative && c.toProfile.isHomogeneous

/-- States satisfy the durative restriction. -/
theorem state_satisfies : satisfiesDurativeRestriction .state = true := rfl

/-- Activities satisfy the durative restriction. -/
theorem activity_satisfies : satisfiesDurativeRestriction .activity = true := rfl

/-- Achievements do NOT satisfy the durative restriction. -/
theorem achievement_fails : satisfiesDurativeRestriction .achievement = false := rfl

/-- Accomplishments do NOT satisfy the durative restriction. -/
theorem accomplishment_fails : satisfiesDurativeRestriction .accomplishment = false := rfl

/-- The durative selectional restriction coincides with homogeneity
    (the subinterval property): exactly states and activities pass. -/
theorem durative_restriction_iff_homogeneous (c : VendlerClass) :
    satisfiesDurativeRestriction c = c.toProfile.isHomogeneous := by
  cases c <;> rfl

-- ============================================================================
-- § 7: Coercion Network Transitions (M&S 1988, Fig. 2)
-- ============================================================================

/-- A directed edge in Moens & Steedman's aspectual coercion network.
    Each edge represents a possible contextual coercion from one Vendler
    class to another, triggered by linguistic context. -/
structure CoercionEdge where
  /-- Source Vendler class -/
  source : VendlerClass
  /-- Target Vendler class -/
  target : VendlerClass
  /-- Name of the coercion operation -/
  operation : String
  /-- Example of the coercion in context -/
  example_ : String
  deriving Repr

/-- Add-result: activity → accomplishment.
    "John walked" → "John walked to school." -/
def addResult : CoercionEdge where
  source := .activity
  target := .accomplishment
  operation := "add-result"
  example_ := "John walked → John walked to school"

/-- Strip-process: accomplishment → achievement.
    "John built the house" → culmination point (when he finished). -/
def stripProcess : CoercionEdge where
  source := .accomplishment
  target := .achievement
  operation := "strip-process"
  example_ := "When John built the house... (= finished building)"

/-- Add-process: achievement → accomplishment.
    "John noticed the painting" → "John noticed the painting for hours." -/
def addProcess : CoercionEdge where
  source := .achievement
  target := .accomplishment
  operation := "add-process"
  example_ := "John noticed the painting (for hours → iterative)"

/-- Iterate: achievement → activity.
    "John coughed" → "John coughed for hours" (iterated). -/
def iterate_ : CoercionEdge where
  source := .achievement
  target := .activity
  operation := "iterate"
  example_ := "John coughed → John coughed for hours"

/-- Inchoative: state → achievement.
    "John knew the answer" → "John came to know the answer." -/
def inchoative : CoercionEdge where
  source := .state
  target := .achievement
  operation := "inchoative"
  example_ := "John knew the answer → came to know (onset)"

/-- The full coercion network. -/
def coercionNetwork : List CoercionEdge :=
  [addResult, stripProcess, addProcess, iterate_, inchoative]

/-- All coercion edges change the Vendler class. -/
theorem coercion_changes_class :
    ∀ e ∈ coercionNetwork, e.source ≠ e.target := by
  intro e he
  simp only [coercionNetwork, List.mem_cons, List.mem_nil_iff,
             or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> decide

-- ============================================================================
-- § 8: Interaction Matrix Summary
-- ============================================================================

/-- All *until*-acceptable main clauses have the durative restriction. -/
theorem until_data_consistent :
    until_state_main.acceptableWithout = satisfiesDurativeRestriction .state ∧
    until_activity_main.acceptableWithout = satisfiesDurativeRestriction .activity ∧
    until_achievement_main.acceptableWithout = satisfiesDurativeRestriction .achievement ∧
    until_accomplishment_main.acceptableWithout = satisfiesDurativeRestriction .accomplishment :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- *When* requires coercion for non-punctual, non-stative classes. -/
theorem when_coercion_pattern :
    when_state.acceptableWithout = true ∧
    when_achievement.acceptableWithout = true ∧
    when_activity.acceptableWithout = false ∧
    when_accomplishment.acceptableWithout = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- *When* coercion always targets achievement (punctual). -/
theorem when_coercion_target :
    when_activity.resultClass = some .achievement ∧
    when_accomplishment.resultClass = some .achievement :=
  ⟨rfl, rfl⟩

end Phenomena.TemporalConnectives.AspectInteractionData
