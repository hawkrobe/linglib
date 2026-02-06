import Linglib.Phenomena.Constructions.Studies.FillmoreKayOConnor1988

/-!
# Kay & Fillmore (1999): *What's X Doing Y?* — Empirical Data

Theory-neutral judgment data from "Grammatical Constructions and Linguistic
Generalizations: The *What's X doing Y?* Construction" (Language 75(1):1–33).

## Phenomena covered

1. **Incredulity reading**: "What's this fly doing in my soup?" (speaker knows the answer)
2. **Literal question reading**: "What's John doing in the kitchen?" (genuine information-seeking)
3. **Progressive requirement**: WXDY requires progressive *doing*; bare infinitive is out
4. **Subject referentiality**: referential subjects OK; non-referential degraded
5. **Complement types**: locative PP, participial VP, instrumental PP
6. **Ambiguity**: sentences admitting both readings
7. **Embedding / CI projection**: WXDY meaning under embedding predicates
8. **FKO1988 comparison**: relation to Incredulity Response construction

## Reference

Kay, P. & Fillmore, C. J. (1999). Grammatical Constructions and Linguistic
Generalizations: The *What's X doing Y?* Construction. Language, 75(1), 1–33.
-/

namespace Phenomena.Constructions.Studies.KayFillmore1999

open Phenomena.Constructions.Studies.FillmoreKayOConnor1988

/-- Check if a string contains a substring. -/
def containsSubstr (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-! ## Reading type -/

/-- The available readings of a WXDY sentence. -/
inductive WXDYReading where
  | literal       -- genuine information-seeking question
  | incredulity   -- speaker expresses surprise/disapproval at the situation
  | ambiguous     -- both readings available
  deriving Repr, DecidableEq, BEq

/-! ## Datum structure -/

/-- A single WXDY example with judgment and reading information. -/
structure WXDYDatum where
  /-- Example identifier -/
  exId : String
  /-- The sentence -/
  sentence : String
  /-- Acceptability judgment -/
  judgment : Judgment
  /-- Available reading(s) -/
  reading : WXDYReading
  /-- What phenomenon this illustrates -/
  phenomenon : String
  deriving Repr, BEq

/-! ## 1. Basic incredulity (§1, pp.1–3) -/

def fly_in_soup : WXDYDatum :=
  { exId := "1"
  , sentence := "What's this fly doing in my soup?"
  , judgment := .grammatical
  , reading := .incredulity
  , phenomenon := "canonical incredulity: speaker sees the fly" }

def cat_on_table : WXDYDatum :=
  { exId := "2"
  , sentence := "What's the cat doing on the dinner table?"
  , judgment := .grammatical
  , reading := .incredulity
  , phenomenon := "incredulity: speaker disapproves of cat's location" }

def car_in_driveway : WXDYDatum :=
  { exId := "3"
  , sentence := "What's that car doing in my driveway?"
  , judgment := .grammatical
  , reading := .incredulity
  , phenomenon := "incredulity: referential subject + locative PP" }

/-! ## 2. Literal question (genuine information-seeking) -/

def john_in_kitchen_literal : WXDYDatum :=
  { exId := "4"
  , sentence := "What's John doing in the kitchen?"
  , judgment := .grammatical
  , reading := .literal
  , phenomenon := "literal question: speaker genuinely asks about activity" }

def mary_with_scissors : WXDYDatum :=
  { exId := "5"
  , sentence := "What's Mary doing with those scissors?"
  , judgment := .grammatical
  , reading := .literal
  , phenomenon := "literal question: instrumental PP complement" }

/-! ## 3. Progressive requirement (§2.2)

WXDY requires the progressive auxiliary + *doing*. Without it, only a
standard wh-question remains; the incredulity reading disappears. -/

def no_progressive : WXDYDatum :=
  { exId := "6"
  , sentence := "*What does this fly do in my soup?"
  , judgment := .ungrammatical
  , reading := .incredulity
  , phenomenon := "incredulity lost without progressive" }

def habitual_do : WXDYDatum :=
  { exId := "7"
  , sentence := "What does John do in the kitchen?"
  , judgment := .grammatical
  , reading := .literal
  , phenomenon := "habitual reading OK, but no incredulity" }

def bare_infinitive : WXDYDatum :=
  { exId := "8"
  , sentence := "*What's this fly do in my soup?"
  , judgment := .ungrammatical
  , reading := .incredulity
  , phenomenon := "bare infinitive blocks WXDY construction" }

/-! ## 4. Subject referentiality (§2.3)

Referential subjects are fine; non-referential or quantified subjects
are degraded on the incredulity reading. -/

def referential_subject : WXDYDatum :=
  { exId := "9"
  , sentence := "What's this book doing on the floor?"
  , judgment := .grammatical
  , reading := .incredulity
  , phenomenon := "demonstrative subject: fully referential" }

def nonreferential_subject : WXDYDatum :=
  { exId := "10"
  , sentence := "?What's something doing on the floor?"
  , judgment := .marginal
  , reading := .incredulity
  , phenomenon := "indefinite subject: degraded incredulity reading" }

/-! ## 5. Complement types (§2.4)

WXDY accepts various complement types: locative PPs, participial VPs,
and instrumental PPs. -/

def locative_pp : WXDYDatum :=
  { exId := "11"
  , sentence := "What's my coat doing on the floor?"
  , judgment := .grammatical
  , reading := .incredulity
  , phenomenon := "locative PP complement" }

def participial_vp : WXDYDatum :=
  { exId := "12"
  , sentence := "What's John doing reading my diary?"
  , judgment := .grammatical
  , reading := .incredulity
  , phenomenon := "participial VP complement" }

def instrumental_pp : WXDYDatum :=
  { exId := "13"
  , sentence := "What are you doing with my car keys?"
  , judgment := .grammatical
  , reading := .incredulity
  , phenomenon := "instrumental PP complement" }

/-! ## 6. Ambiguous (both readings available) -/

def john_in_kitchen_ambig : WXDYDatum :=
  { exId := "14"
  , sentence := "What's John doing in the garden?"
  , judgment := .grammatical
  , reading := .ambiguous
  , phenomenon := "ambiguous: genuine Q or incredulity depending on context" }

def dog_on_couch : WXDYDatum :=
  { exId := "15"
  , sentence := "What's the dog doing on the couch?"
  , judgment := .grammatical
  , reading := .ambiguous
  , phenomenon := "ambiguous: activity Q or disapproval" }

/-! ## 7. Embedding / CI projection (§3)

Under embedding, the incredulity component projects like a CI. -/

def embedded_wonder : WXDYDatum :=
  { exId := "16"
  , sentence := "I wonder what this fly is doing in my soup"
  , judgment := .grammatical
  , reading := .incredulity
  , phenomenon := "embedded: incredulity projects through wonder" }

def embedded_tell : WXDYDatum :=
  { exId := "17"
  , sentence := "Tell me what your shoes are doing on the table"
  , judgment := .grammatical
  , reading := .incredulity
  , phenomenon := "embedded: incredulity projects through imperative" }

/-! ## 8. FKO1988 comparison

WXDY relates to the Incredulity Response construction from FKO1988
("Him be a doctor?"). Both express speaker incredulity via non-standard
question form. -/

def fko_comparison : WXDYDatum :=
  { exId := "18"
  , sentence := "What's HIM doing being a doctor?"
  , judgment := .grammatical
  , reading := .incredulity
  , phenomenon := "WXDY with accusative subject: cf. FKO1988 Incredulity Response" }

/-! ## All data -/

def allExamples : List WXDYDatum :=
  [ fly_in_soup, cat_on_table, car_in_driveway
  , john_in_kitchen_literal, mary_with_scissors
  , no_progressive, habitual_do, bare_infinitive
  , referential_subject, nonreferential_subject
  , locative_pp, participial_vp, instrumental_pp
  , john_in_kitchen_ambig, dog_on_couch
  , embedded_wonder, embedded_tell
  , fko_comparison ]

/-! ## Verification theorems -/

/-- Both readings are attested in the data. -/
theorem has_both_readings :
    (allExamples.any (·.reading == .literal)) = true ∧
    (allExamples.any (·.reading == .incredulity)) = true ∧
    (allExamples.any (·.reading == .ambiguous)) = true := by
  constructor; native_decide
  constructor; native_decide
  native_decide

/-- All judgment types are represented. -/
theorem has_all_judgment_types :
    (allExamples.any (·.judgment == .grammatical)) = true ∧
    (allExamples.any (·.judgment == .ungrammatical)) = true ∧
    (allExamples.any (·.judgment == .marginal)) = true := by
  constructor; native_decide
  constructor; native_decide
  native_decide

/-- All grammatical WXDY examples with incredulity reading have progressive. -/
theorem progressive_is_required :
    (allExamples.filter (λ d =>
      d.judgment == .grammatical && d.reading != .literal
    )).all (λ d => containsSubstr d.sentence "doing" || containsSubstr d.sentence "is doing") = true := by
  native_decide

end Phenomena.Constructions.Studies.KayFillmore1999
