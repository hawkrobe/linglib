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

open TruthConditional.Verb.Aspect

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
  , crossLinguisticBasic := true }

/-- *after*: no NPIs; default = after-finish; coerced = after-start
    (requires INCHOAT to extract onset of atelic EE). -/
def after_ : TemporalConnectiveEntry :=
  { form := "after"
  , order := .after
  , licensesNPI := false
  , defaultReading := .afterFinish
  , coercedReading := some .afterStart
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true }

/-- *while*: durative overlap, no coercion, no telicity sensitivity. -/
def while_conn : TemporalConnectiveEntry :=
  { form := "while"
  , order := .while_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true }

def allConnectives : List TemporalConnectiveEntry :=
  [before_, after_, while_conn]

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

end Fragments.English.TemporalExpressions
