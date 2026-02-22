import Linglib.Theories.Semantics.Lexical.Verb.Aspect
import Linglib.Fragments.English.FunctionWords

/-!
# English Temporal Expressions Fragment

Lexical entries for temporal subordinating connectives (*before*, *after*,
*while*) and temporal adverbial modifiers (*within*, *at*) as separate types.

The connective/modifier distinction matters:
- **Connectives** (*before*, *after*, *while*) take clausal complements
  and introduce temporal ordering between two eventualities.
- **Temporal modifiers** (*within*, *at*) take NP complements and
  constrain the temporal profile of a single eventuality.

Alstott & Aravind (2026) test aspectual coercion across both categories,
but the coercion operators (INCHOAT, COMPLET) compose differently in each.

## References

- Rett, J. (2020). Eliminating EARLIEST. *Sinn und Bedeutung* 24.
- Alstott, A. & Aravind, A. (2026). Aspectual coercion in *before*/*after*-clauses.
- Heinamäki, O. (1974). *Semantics of English temporal connectives*.
-/

namespace Fragments.English.TemporalExpressions

open Semantics.Lexical.Verb.Aspect

-- ============================================================================
-- § 1: Shared Types
-- ============================================================================

/-- Temporal ordering relation encoded by a connective or modifier. -/
inductive TemporalOrder where
  | before
  | after
  | while_
  | when_
  | until_
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Available readings for a temporal clause or modified VP.
    "Start" = initial point of embedded eventuality; "finish" = final point. -/
inductive Reading where
  | beforeStart   -- ME precedes onset of EE
  | beforeFinish  -- ME precedes telos of EE
  | afterStart    -- ME follows onset of EE
  | afterFinish   -- ME follows telos of EE
  | durative      -- ME overlaps with EE runtime
  deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================================
-- § 2: Temporal Subordinating Connectives
-- ============================================================================

/-- Lexical entry for a temporal subordinating connective (takes clausal complement).
    Bundles syntactic, semantic, and cross-linguistic properties. -/
structure TemporalConnectiveEntry where
  /-- Surface form -/
  form : String
  /-- Temporal ordering direction -/
  order : TemporalOrder
  /-- Does this connective license NPIs in its complement? (Heinamäki 1974) -/
  licensesNPI : Bool
  /-- Reading obtained without coercion (Rett's strong default) -/
  defaultReading : Reading
  /-- Reading requiring aspectual coercion (INCHOAT or COMPLET) -/
  coercedReading : Option Reading
  /-- Does telicity of the embedded clause affect interpretation? -/
  embeddedTelicityEffect : Bool
  /-- Attested in all 17 languages of Rett's (2020) typological survey -/
  crossLinguisticBasic : Bool
  /-- Does the connective entail the truth of its complement clause?
      *after* is veridical: "He left after she arrived" entails she arrived.
      *before* is non-veridical: "He left before she arrived" is compatible
      with her not arriving. (Ogihara & Steinert-Threlkeld 2024) -/
  complementVeridical : Bool
  deriving Repr, BEq

/-- *before*: licenses NPIs; default = before-start; coerced = before-finish
    (requires COMPLET to extract telos of telic EE). -/
def before_ : TemporalConnectiveEntry :=
  { form := "before"
  , order := .before
  , licensesNPI := true
  , defaultReading := .beforeStart
  , coercedReading := some .beforeFinish
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := false }

/-- *after*: no NPIs; default = after-finish; coerced = after-start
    (requires INCHOAT to extract onset of atelic EE). -/
def after_ : TemporalConnectiveEntry :=
  { form := "after"
  , order := .after
  , licensesNPI := false
  , defaultReading := .afterFinish
  , coercedReading := some .afterStart
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := true }

/-- *while*: durative overlap, no coercion, no telicity sensitivity. -/
def while_conn : TemporalConnectiveEntry :=
  { form := "while"
  , order := .while_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true }

/-- *until*: durative persistence up to complement time.
    Has two uses (Karttunen 1974):
    - **Durative**: "John slept until 3pm" — main clause is stative, *until*
      marks minimum extent. Truth-conditionally = temporal overlap.
    - **Punctual** (with negation): "He didn't wake up until 3pm" — logical
      form = NOT(A BEFORE T). Licenses NPIs in this use.

    We encode the durative reading as default, with the punctual reading
    arising compositionally via negation + the `before` semantics. -/
def until_ : TemporalConnectiveEntry :=
  { form := "until"
  , order := .until_
  , licensesNPI := true
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true }

/-- *when*: temporal coincidence, no coercion. Veridical complement.
    "John arrived when Mary left" — the two events overlap in time.
    Symmetric: "A when B" ↔ "B when A" (Karttunen 1974). -/
def when_conn : TemporalConnectiveEntry :=
  { form := "when"
  , order := .when_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true }

def allConnectives : List TemporalConnectiveEntry :=
  [before_, after_, while_conn, until_, when_conn]

-- ============================================================================
-- § 3: Temporal Adverbial Modifiers
-- ============================================================================

/-- Lexical entry for a temporal adverbial modifier (takes NP complement).
    These are syntactically and semantically distinct from subordinating
    connectives: they modify a single eventuality's temporal profile rather
    than ordering two eventualities. Included because Alstott & Aravind (2026)
    test INCHOAT/COMPLET with these constructions. -/
structure TemporalModifierEntry where
  /-- Surface form -/
  form : String
  /-- Does this modifier force a punctual (point-like) reading? -/
  forcesPunctual : Bool
  /-- Which coercion operator is triggered (if any) -/
  triggeredCoercion : Option String
  deriving Repr, BEq

/-- *within* + duration: relevant to INCHOAT debate.
    Alstott & Aravind Exps 1a, 3: "within an hour" + activity verb.
    Brennan & Pylkkänen (2010) claimed INCHOAT cost; not replicated. -/
def within_ : TemporalModifierEntry :=
  { form := "within"
  , forcesPunctual := false
  , triggeredCoercion := some "INCHOAT" }

/-- *at* + time point: relevant to COMPLET debate.
    Alstott & Aravind Exp 1b: "at 7 o'clock" + accomplishment.
    Forces punctual reading → COMPLET required for telic events. -/
def at_punct : TemporalModifierEntry :=
  { form := "at"
  , forcesPunctual := true
  , triggeredCoercion := some "COMPLET" }

def allModifiers : List TemporalModifierEntry :=
  [within_, at_punct]

-- ============================================================================
-- § 4: Form Agreement with FunctionWords
-- ============================================================================

open Fragments.English.FunctionWords in
theorem before_form_agrees : before_.form = FunctionWords.before.form := rfl

open Fragments.English.FunctionWords in
theorem after_form_agrees : after_.form = FunctionWords.after.form := rfl

-- ============================================================================
-- § 5: Coverage — Every TemporalOrder Has an Entry
-- ============================================================================

/-- All five temporal orders in the enum have corresponding connective entries. -/
theorem all_orders_covered :
    before_.order = .before ∧
    after_.order = .after ∧
    while_conn.order = .while_ ∧
    until_.order = .until_ ∧
    when_conn.order = .when_ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Veridicality pattern: *before* is the only non-veridical connective. -/
theorem only_before_nonveridical :
    before_.complementVeridical = false ∧
    after_.complementVeridical = true ∧
    while_conn.complementVeridical = true ∧
    until_.complementVeridical = true ∧
    when_conn.complementVeridical = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- NPI licensing pattern: only *before* and *until* license NPIs.
    For *before*, this follows from downward entailment of the complement.
    For *until*, this arises in the punctual (*not...until*) construction,
    which is truth-conditionally ¬*before* (Karttunen 1974). -/
theorem npi_pattern :
    before_.licensesNPI = true ∧
    until_.licensesNPI = true ∧
    after_.licensesNPI = false ∧
    while_conn.licensesNPI = false ∧
    when_conn.licensesNPI = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Fragments.English.TemporalExpressions
