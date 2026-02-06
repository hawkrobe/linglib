import Linglib.Core.Basic

/-!
# Fillmore, Kay & O'Connor (1988): *Let Alone* — Empirical Data

Theory-neutral grammaticality judgments and contrasts from "Regularity and
Idiomaticity in Grammatical Constructions: The Case of *Let Alone*"
(Language 64(3):501–538).

## Phenomena covered

1. **NPI licensing**: which environments license *let alone* (§2.2.4)
2. **Topicalization asymmetry**: *let alone* B cannot topicalize (§2.2.1)
3. **VP ellipsis impossibility**: unlike *and*, *let alone* blocks VP ellipsis (§2.2.1)
4. **Scalar anomaly**: swapping foci on the scale yields anomaly (§2.3.2)
5. **NPI trigger contrasts**: *barely* licenses, *almost*/*only* do not (§2.2.4)
6. **Wh-extraction asymmetry**: easier from *let alone* than from *and* (§2.2.1)

## Reference

Fillmore, C. J., Kay, P., & O'Connor, M. C. (1988). Regularity and
Idiomaticity in Grammatical Constructions: The Case of *Let Alone*.
Language, 64(3), 501–538.
-/

namespace Phenomena.Constructions.Studies.FillmoreKayOConnor1988

/-! ## Judgment data structure -/

/-- Acceptability judgment for a single example. -/
inductive Judgment where
  | grammatical      -- fully acceptable
  | marginal         -- "?" — degraded but not out
  | ungrammatical    -- "*" — clearly unacceptable
  | anomalous        -- "#" — semantically/pragmatically odd
  deriving Repr, DecidableEq, BEq

/-- A single attested or judged example. -/
structure ExampleDatum where
  /-- Example number in the paper -/
  exNumber : String
  /-- The sentence -/
  sentence : String
  /-- Acceptability judgment -/
  judgment : Judgment
  /-- What phenomenon this illustrates -/
  phenomenon : String
  deriving Repr, BEq

/-! ## 1. Basic *let alone* examples (§2.1, exx.15–19) -/

def ex15b : ExampleDatum :=
  { exNumber := "15b"
  , sentence := "I barely got up in time to eat lunch, let alone cook breakfast"
  , judgment := .grammatical
  , phenomenon := "basic let alone with barely" }

def ex16b : ExampleDatum :=
  { exNumber := "16b"
  , sentence := "I doubt you could get Fred to eat shrimp, let alone Louise squid"
  , judgment := .grammatical
  , phenomenon := "let alone with multiple paired foci" }

/-! ## 2. NPI trigger contrasts (§2.2.4, exx.62–70, 113–115)

*barely* licenses *let alone*; *almost* and non-subject *only* do not. -/

def ex62 : ExampleDatum :=
  { exNumber := "62"
  , sentence := "He didn't reach Denver, let alone Chicago"
  , judgment := .grammatical
  , phenomenon := "let alone licensed by simple negation" }

def ex63 : ExampleDatum :=
  { exNumber := "63"
  , sentence := "I'm too tired to get up, let alone go running with you"
  , judgment := .grammatical
  , phenomenon := "let alone licensed by too-complementation" }

def ex66 : ExampleDatum :=
  { exNumber := "66"
  , sentence := "I barely got up in time for lunch, let alone breakfast"
  , judgment := .grammatical
  , phenomenon := "let alone licensed by barely" }

def ex113 : ExampleDatum :=
  { exNumber := "113"
  , sentence := "*He almost reached Denver let alone Chicago"
  , judgment := .ungrammatical
  , phenomenon := "let alone NOT licensed by almost" }

def ex114 : ExampleDatum :=
  { exNumber := "114"
  , sentence := "*He only reached Denver let alone Chicago"
  , judgment := .ungrammatical
  , phenomenon := "let alone NOT licensed by non-subject only" }

def ex115 : ExampleDatum :=
  { exNumber := "115"
  , sentence := "He barely reached Denver let alone Chicago"
  , judgment := .grammatical
  , phenomenon := "let alone licensed by barely (contrast with almost/only)" }

/-- NPI licensing contrasts: barely licenses, almost and only do not. -/
def npiContrasts : List ExampleDatum :=
  [ex113, ex114, ex115]

/-! ## 3. Topicalization asymmetry (§2.2.1, exx.31a–d)

*let alone* B cannot be topicalized, unlike coordinate *and* phrases.
This shows *let alone* is not a standard coordinating conjunction. -/

def ex31a : ExampleDatum :=
  { exNumber := "31a"
  , sentence := "Shrimp and squid Moishe won't eat"
  , judgment := .grammatical
  , phenomenon := "and-coordination permits topicalization" }

def ex31b : ExampleDatum :=
  { exNumber := "31b"
  , sentence := "*Shrimp let alone squid Moishe won't eat"
  , judgment := .ungrammatical
  , phenomenon := "let alone blocks topicalization" }

def ex31c : ExampleDatum :=
  { exNumber := "31c"
  , sentence := "*Shrimp Moishe won't eat and squid"
  , judgment := .ungrammatical
  , phenomenon := "and-coordination: can't split" }

def ex31d : ExampleDatum :=
  { exNumber := "31d"
  , sentence := "Shrimp Moishe won't eat, let alone squid"
  , judgment := .grammatical
  , phenomenon := "let alone permits parenthetical-like extraposition" }

/-- Topicalization asymmetry: *and* allows full topicalization,
*let alone* only allows extraposed second conjunct. -/
def topicalizationContrasts : List ExampleDatum :=
  [ex31a, ex31b, ex31d]

/-! ## 4. VP ellipsis impossibility (§2.2.1, exx.39–41)

*let alone* does not permit VP ellipsis, unlike *and* and comparatives. -/

def ex39 : ExampleDatum :=
  { exNumber := "39"
  , sentence := "Max will eat shrimp more willingly than Minnie will"
  , judgment := .grammatical
  , phenomenon := "comparative permits VP ellipsis" }

def ex40 : ExampleDatum :=
  { exNumber := "40"
  , sentence := "Max won't eat shrimp but Minnie will"
  , judgment := .grammatical
  , phenomenon := "but-coordination permits VP ellipsis" }

def ex41 : ExampleDatum :=
  { exNumber := "41"
  , sentence := "*Max won't eat shrimp let alone Minnie will"
  , judgment := .ungrammatical
  , phenomenon := "let alone blocks VP ellipsis" }

/-- VP ellipsis contrast: *and*/*but* allow it, *let alone* does not. -/
def vpEllipsisContrasts : List ExampleDatum :=
  [ex39, ex40, ex41]

/-! ## 5. Wh-extraction asymmetry (§2.2.1, exx.32a–b)

Wh-extraction from a *let alone* phrase is sometimes easier
than from a corresponding *and*-coordination. -/

def ex32a : ExampleDatum :=
  { exNumber := "32a"
  , sentence := "*a man who Mary hasn't met or ridden in his car"
  , judgment := .ungrammatical
  , phenomenon := "wh-extraction from and-coordination blocked" }

def ex32b : ExampleDatum :=
  { exNumber := "32b"
  , sentence := "?a man who Mary hasn't met, let alone ridden in his car"
  , judgment := .marginal
  , phenomenon := "wh-extraction from let alone is better" }

/-! ## 6. Scalar anomaly (§2.3.2, exx.104, 121–122)

Swapping the scalar order of foci yields pragmatic anomaly.
The A focus (stronger clause) must be scalar-stronger than B. -/

def ex104 : ExampleDatum :=
  { exNumber := "104"
  , sentence := "#Fred doesn't have an odd number of books, let alone seventy-five"
  , judgment := .anomalous
  , phenomenon := "scalar anomaly: odd-number doesn't form a scale with 75" }

def ex121 : ExampleDatum :=
  { exNumber := "121"
  , sentence := "You couldn't get a poor man to wash your car for $2, let alone a rich man to wax your truck for $1"
  , judgment := .grammatical
  , phenomenon := "multi-dimensional scalar model (5 dimensions)" }

def ex122a : ExampleDatum :=
  { exNumber := "122a"
  , sentence := "#You couldn't get a rich man to wash your car for $2 let alone a poor man to wax your truck for $1"
  , judgment := .anomalous
  , phenomenon := "scalar anomaly: swapped foci on poor/rich dimension" }

def ex122b : ExampleDatum :=
  { exNumber := "122b"
  , sentence := "#You couldn't get a poor man to wax your car for $2 let alone a rich man to wash your truck for $1"
  , judgment := .anomalous
  , phenomenon := "scalar anomaly: swapped foci on wash/wax dimension" }

/-- Scalar anomaly contrasts: well-formed scalar ordering vs. swapped foci. -/
def scalarAnomalyContrasts : List ExampleDatum :=
  [ex121, ex122a, ex122b]

/-! ## 7. IT-cleft asymmetry (§2.2.1, exx.33–34)

IT-clefting is possible with a full *and*-coordination
but not with *let alone*. -/

def ex33 : ExampleDatum :=
  { exNumber := "33"
  , sentence := "*It's shrimp let alone squid that Max won't eat"
  , judgment := .ungrammatical
  , phenomenon := "IT-clefting blocked with let alone" }

def ex34 : ExampleDatum :=
  { exNumber := "34"
  , sentence := "It's shrimp and squid that Max won't eat"
  , judgment := .grammatical
  , phenomenon := "IT-clefting fine with and-coordination" }

/-! ## 8. Positive polarity examples (§2.2.4, exx.71–72)

Rare but attested: *let alone* in non-negative contexts.
These challenge a purely syntactic NPI account. -/

def ex71 : ExampleDatum :=
  { exNumber := "71"
  , sentence := "You've got enough material there for a whole semester, let alone a week"
  , judgment := .grammatical
  , phenomenon := "let alone in positive polarity context (attested)" }

def ex72 : ExampleDatum :=
  { exNumber := "72"
  , sentence := "Penutian has been broken up, let alone Macro-Penutian"
  , judgment := .grammatical
  , phenomenon := "let alone in positive polarity context (attested)" }

/-- Positive polarity *let alone* examples challenge pure NPI analysis. -/
def positivePolarityExamples : List ExampleDatum :=
  [ex71, ex72]

/-! ## All data -/

/-- All judgment data from the paper. -/
def allExamples : List ExampleDatum :=
  [ ex15b, ex16b
  , ex62, ex63, ex66, ex113, ex114, ex115
  , ex31a, ex31b, ex31c, ex31d
  , ex39, ex40, ex41
  , ex32a, ex32b
  , ex104, ex121, ex122a, ex122b
  , ex33, ex34
  , ex71, ex72 ]

/-- All grammatical examples. -/
def grammaticalExamples : List ExampleDatum :=
  allExamples.filter (·.judgment == .grammatical)

/-- All ungrammatical examples. -/
def ungrammaticalExamples : List ExampleDatum :=
  allExamples.filter (·.judgment == .ungrammatical)

/-- Verification: we have examples of all judgment types. -/
theorem has_all_judgment_types :
    (allExamples.any (·.judgment == .grammatical)) = true ∧
    (allExamples.any (·.judgment == .ungrammatical)) = true ∧
    (allExamples.any (·.judgment == .marginal)) = true ∧
    (allExamples.any (·.judgment == .anomalous)) = true := by
  constructor; native_decide
  constructor; native_decide
  constructor; native_decide
  native_decide

end Phenomena.Constructions.Studies.FillmoreKayOConnor1988
