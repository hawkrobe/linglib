import Linglib.Theories.Semantics.Lexical.Verb.Aspect
import Linglib.Fragments.English.FunctionWords

/-!
# English Temporal Expressions Fragment

Lexical entries for temporal expressions: subordinating connectives (*before*,
*after*, *while*, *until*, *when*, *since*, *till*) and adverbial modifiers
(*within*, *at*, *by*), unified under a single `TemporalExprEntry` type.

The connective/modifier distinction is captured by the `ComplementType` field
(clausal vs nominal), but the semantic fields — `order`, `licensesNPI`,
`complementVeridical` — are shared, enabling uniform pattern theorems across
both categories. This matters because *by* has the same temporal-ordering
semantics as *before* (weakened to ≤) and should participate in the
veridicality and NPI-licensing generalizations (Heinämäki 1974).

## References

- Rett, J. (2020). Eliminating EARLIEST. *Sinn und Bedeutung* 24.
- Alstott, A. & Aravind, A. (2026). Aspectual coercion in *before*/*after*-clauses.
- Heinämäki, O. (1974). *Semantics of English temporal connectives*.
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
  | since_
  | by_
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

/-- Syntactic complement type: clausal (*before she arrived*) vs
    nominal (*by 3pm*, *within an hour*). -/
inductive ComplementType where
  | clausal
  | nominal
  deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================================
-- § 2: Unified Temporal Expression Entry
-- ============================================================================

/-- Lexical entry for any temporal expression — subordinating connective
    or adverbial modifier. Unifies the semantic fields (ordering direction,
    NPI licensing, veridicality) that Heinämäki (1974) shows are shared
    across both syntactic categories.

    The `complementType` field records the syntactic distinction (clausal
    vs nominal complement) without splitting the semantic properties into
    separate types. -/
structure TemporalExprEntry where
  /-- Surface form -/
  form : String
  /-- Syntactic complement type -/
  complementType : ComplementType
  /-- Temporal ordering direction -/
  order : TemporalOrder
  /-- Does this expression license NPIs in its complement? (Heinämäki 1974) -/
  licensesNPI : Bool
  /-- Reading obtained without coercion (Rett's strong default) -/
  defaultReading : Reading
  /-- Reading requiring aspectual coercion (INCHOAT or COMPLET) -/
  coercedReading : Option Reading
  /-- Does telicity of the embedded clause affect interpretation? -/
  embeddedTelicityEffect : Bool
  /-- Attested in all 17 languages of Rett's (2020) typological survey -/
  crossLinguisticBasic : Bool
  /-- Does the expression entail the truth of its complement?
      *after* is veridical: "He left after she arrived" entails she arrived.
      *before* is non-veridical: "He left before she arrived" is compatible
      with her not arriving. (Ogihara & Steinert-Threlkeld 2024) -/
  complementVeridical : Bool
  /-- Does this expression force a punctual (point-like) reading? -/
  forcesPunctual : Bool
  /-- Which coercion operator is *mandatorily* triggered (if any).
      `some "INCHOAT"` or `some "COMPLET"` for modifiers that force coercion
      (e.g. *within*, *at*). `none` for connectives like *before*/*after* where
      coercion is optional — those use `coercedReading` to record the
      alternative reading available through voluntary coercion. -/
  triggeredCoercion : Option String
  deriving Repr, BEq

-- ============================================================================
-- § 3: Connective Entries (clausal complement)
-- ============================================================================

/-- *before*: licenses NPIs; default = before-start; coerced = before-finish
    (requires COMPLET to extract telos of telic EE). -/
def before_ : TemporalExprEntry :=
  { form := "before"
  , complementType := .clausal
  , order := .before
  , licensesNPI := true
  , defaultReading := .beforeStart
  , coercedReading := some .beforeFinish
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := false
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *after*: no NPIs; default = after-finish; coerced = after-start
    (requires INCHOAT to extract onset of atelic EE). -/
def after_ : TemporalExprEntry :=
  { form := "after"
  , complementType := .clausal
  , order := .after
  , licensesNPI := false
  , defaultReading := .afterFinish
  , coercedReading := some .afterStart
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *while*: durative overlap, no coercion, no telicity sensitivity. -/
def while_conn : TemporalExprEntry :=
  { form := "while"
  , complementType := .clausal
  , order := .while_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *until*: durative persistence up to complement time.
    Has two uses (Karttunen 1974):
    - **Durative**: "John slept until 3pm" — main clause is stative, *until*
      marks minimum extent. Truth-conditionally = temporal overlap.
    - **Punctual** (with negation): "He didn't wake up until 3pm" — logical
      form = NOT(A BEFORE T). Licenses NPIs in this use.

    We encode the durative reading as default, with the punctual reading
    arising compositionally via negation + the `before` semantics. -/
def until_ : TemporalExprEntry :=
  { form := "until"
  , complementType := .clausal
  , order := .until_
  , licensesNPI := true
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *when*: temporal coincidence, no coercion. Veridical complement.
    "John arrived when Mary left" — the two events overlap in time.
    Symmetric: "A when B" ↔ "B when A" (Karttunen 1974). -/
def when_conn : TemporalExprEntry :=
  { form := "when"
  , complementType := .clausal
  , order := .when_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *since*: starting-point connective. Veridical complement.
    "He's been happy since she arrived" entails she arrived.
    Requires durative (stative/activity) main clause, like *until*.
    Does not license NPIs. (Heinämäki 1974, Ch. 6) -/
def since_conn : TemporalExprEntry :=
  { form := "since"
  , complementType := .clausal
  , order := .since_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- *till*: dialectal variant of *until* (Heinämäki 1974, Ch. 9).
    Identical semantic properties to *until*. Dialectally restricted:
    not universal across English varieties. -/
def till_conn : TemporalExprEntry :=
  { form := "till"
  , complementType := .clausal
  , order := .until_
  , licensesNPI := true
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := false
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

-- ============================================================================
-- § 4: Modifier Entries (nominal complement)
-- ============================================================================

/-- *within* + duration: relevant to INCHOAT debate.
    Alstott & Aravind Exps 1a, 3: "within an hour" + activity verb.
    Brennan & Pylkkänen (2010) claimed INCHOAT cost; not replicated. -/
def within_ : TemporalExprEntry :=
  { form := "within"
  , complementType := .nominal
  , order := .while_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := false
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := some "INCHOAT" }

/-- *at* + time point: relevant to COMPLET debate.
    Alstott & Aravind Exp 1b: "at 7 o'clock" + accomplishment.
    Forces punctual reading → COMPLET required for telic events. -/
def at_punct : TemporalExprEntry :=
  { form := "at"
  , complementType := .nominal
  , order := .when_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := false
  , complementVeridical := true
  , forcesPunctual := true
  , triggeredCoercion := some "COMPLET" }

/-- *by* + time point: deadline semantics.
    "He arrived by 3pm" = at or before 3pm.
    Weaker than *before* (allows coincidence). Does not force punctual
    reading: "He had finished the book by Tuesday" is fine with an
    accomplishment. (Heinämäki 1974, Ch. 8) -/
def by_deadline : TemporalExprEntry :=
  { form := "by"
  , complementType := .nominal
  , order := .by_
  , licensesNPI := false
  , defaultReading := .beforeStart
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := false
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

-- ============================================================================
-- § 5: Entry Lists
-- ============================================================================

def allEntries : List TemporalExprEntry :=
  [before_, after_, while_conn, until_, when_conn, since_conn, till_conn,
   within_, at_punct, by_deadline]

/-- Connective entries only (clausal complement). -/
def allConnectives : List TemporalExprEntry :=
  allEntries.filter (·.complementType == .clausal)

/-- Modifier entries only (nominal complement). -/
def allModifiers : List TemporalExprEntry :=
  allEntries.filter (·.complementType == .nominal)

-- ============================================================================
-- § 6: Form Agreement with FunctionWords
-- ============================================================================

open Fragments.English.FunctionWords in
theorem before_form_agrees : before_.form = FunctionWords.before.form := rfl

open Fragments.English.FunctionWords in
theorem after_form_agrees : after_.form = FunctionWords.after.form := rfl

-- ============================================================================
-- § 7: Coverage — Every TemporalOrder Has an Entry
-- ============================================================================

/-- All seven temporal orders in the enum have corresponding entries. -/
theorem all_orders_covered :
    before_.order = .before ∧
    after_.order = .after ∧
    while_conn.order = .while_ ∧
    until_.order = .until_ ∧
    when_conn.order = .when_ ∧
    since_conn.order = .since_ ∧
    by_deadline.order = .by_ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Veridicality pattern: *before* is the only non-veridical expression.
    This holds across both connectives and modifiers. -/
theorem only_before_nonveridical :
    before_.complementVeridical = false ∧
    after_.complementVeridical = true ∧
    while_conn.complementVeridical = true ∧
    until_.complementVeridical = true ∧
    when_conn.complementVeridical = true ∧
    since_conn.complementVeridical = true ∧
    till_conn.complementVeridical = true ∧
    by_deadline.complementVeridical = true ∧
    within_.complementVeridical = true ∧
    at_punct.complementVeridical = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- NPI licensing pattern: only *before*, *until*, and *till* license NPIs.
    For *before*, this follows from downward entailment of the complement.
    For *until*/*till*, this arises in the punctual (*not...until*) construction,
    which is truth-conditionally ¬*before* (Karttunen 1974).
    No modifiers license NPIs. -/
theorem npi_pattern :
    before_.licensesNPI = true ∧
    until_.licensesNPI = true ∧
    till_conn.licensesNPI = true ∧
    after_.licensesNPI = false ∧
    while_conn.licensesNPI = false ∧
    when_conn.licensesNPI = false ∧
    since_conn.licensesNPI = false ∧
    by_deadline.licensesNPI = false ∧
    within_.licensesNPI = false ∧
    at_punct.licensesNPI = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- *Till* and *until* agree on all semantic properties. -/
theorem till_matches_until :
    till_conn.order = until_.order ∧
    till_conn.licensesNPI = until_.licensesNPI ∧
    till_conn.defaultReading = until_.defaultReading ∧
    till_conn.complementVeridical = until_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The complement-type field correctly classifies all entries. -/
theorem complement_type_classification :
    before_.complementType = .clausal ∧
    after_.complementType = .clausal ∧
    while_conn.complementType = .clausal ∧
    until_.complementType = .clausal ∧
    when_conn.complementType = .clausal ∧
    since_conn.complementType = .clausal ∧
    till_conn.complementType = .clausal ∧
    by_deadline.complementType = .nominal ∧
    within_.complementType = .nominal ∧
    at_punct.complementType = .nominal :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Fragments.English.TemporalExpressions
