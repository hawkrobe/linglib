/-
# Negative Polarity Items: Empirical Patterns

Theory-neutral data about NPI licensing and distribution.

## Key Phenomena

1. **Licensing contexts**: Where NPIs are grammatical
2. **Anti-licensing contexts**: Where NPIs are ungrammatical
3. **Strong vs weak NPIs**: Different licensing requirements
4. **Scalar properties**: NPIs often involve scalar endpoints
5. **Cross-linguistic patterns**: Universal tendencies

## Main Generalizations

- **Ladusaw (1979)**: NPIs licensed in downward-entailing (DE) contexts
- **Fauconnier (1975)**: NPIs appear where scalar reversal occurs
- **Giannakidou (1998)**: NPIs licensed in nonveridical contexts
- **Chierchia (2013)**: NPIs involve covert EVEN + domain widening

## References

- Ladusaw, W. (1979). Polarity Sensitivity as Inherent Scope Relations.
- Fauconnier, G. (1975). Polarity and the scale principle.
- Giannakidou, A. (1998). Polarity Sensitivity as (Non)Veridical Dependency.
- Chierchia, G. (2013). Logic in Grammar.
- Lahiri, U. (1998). Focus and negative polarity in Hindi.
- Kadmon, N. & Landman, F. (1993). Any. Linguistics & Philosophy.
- Krifka, M. (1995). The semantics and pragmatics of polarity items.
- van Rooy, R. (2003). Negative Polarity Items in Questions: Strength as Relevance.
- Borkin, A. (1971). Polarity items in questions.
- Israel, M. (2001). Minimizers, maximizers and the rhetoric of scalar reasoning.
-/

import Linglib.Fragments.English.PolarityItems

namespace Phenomena.Polarity.NPIs

open Fragments.English.PolarityItems (ScalarDirection)

-- Licensing Context Classification

/-- Types of licensing contexts -/
inductive LicensingContext where
  | sententialNegation   -- "not", "never"
  | constituentNegation  -- "no one", "nothing"
  | withoutClause        -- "without seeing anyone"
  | beforeClause         -- "before anyone arrived"
  | onlyFocus            -- "only John saw anyone"
  | superlative          -- "the best book anyone wrote"
  | conditional          -- "if anyone calls"
  | universalRestrictor  -- "everyone who saw anyone"
  | fewNP                -- "few people saw anyone"
  | question             -- "did anyone call?"
  | comparativeThan      -- "taller than anyone expected"
  | tooAdjective         -- "too tired to see anyone"
  | doubtVerb            -- "I doubt anyone came"
  | denyVerb             -- "She denied seeing anyone"
  deriving DecidableEq, Repr, BEq

-- Basic Data Structure

/-- An NPI licensing datum -/
structure NPIDatum where
  /-- The sentence -/
  sentence : String
  /-- The NPI item -/
  npiItem : String
  /-- Grammaticality judgment (true = OK, false = bad) -/
  grammatical : Bool
  /-- Type of licensing context (if grammatical) -/
  context : Option LicensingContext
  /-- Notes -/
  notes : String

-- Classic "Any" Examples

/-!
## The "Any" Paradigm

"Any" is the classic English weak NPI. Licensed in DE contexts.
-/

-- Negation licenses "any"
def anyNegation : NPIDatum :=
  { sentence := "John didn't see anyone"
  , npiItem := "anyone"
  , grammatical := true
  , context := some .sententialNegation
  , notes := "Classic case: sentential negation is DE"
  }

-- Positive context blocks "any"
def anyPositive : NPIDatum :=
  { sentence := "*John saw anyone"
  , npiItem := "anyone"
  , grammatical := false
  , context := none
  , notes := "Positive (UE) context blocks NPI"
  }

-- Questions license "any"
def anyQuestion : NPIDatum :=
  { sentence := "Did anyone call?"
  , npiItem := "anyone"
  , grammatical := true
  , context := some .question
  , notes := "Questions are nonveridical, license weak NPIs"
  }

-- Conditionals license "any"
def anyConditional : NPIDatum :=
  { sentence := "If anyone calls, tell them I'm out"
  , npiItem := "anyone"
  , grammatical := true
  , context := some .conditional
  , notes := "If-clause is DE"
  }

-- Universal restrictor licenses "any"
def anyUniversal : NPIDatum :=
  { sentence := "Everyone who saw anyone was questioned"
  , npiItem := "anyone"
  , grammatical := true
  , context := some .universalRestrictor
  , notes := "Restrictor of universal is DE"
  }

-- "Only" licenses "any"
def anyOnly : NPIDatum :=
  { sentence := "Only John saw anyone"
  , npiItem := "anyone"
  , grammatical := true
  , context := some .onlyFocus
  , notes := "\"Only\" creates DE context for non-focused material"
  }

-- Superlative licenses "any"
def anySuperlative : NPIDatum :=
  { sentence := "This is the best book anyone ever wrote"
  , npiItem := "anyone"
  , grammatical := true
  , context := some .superlative
  , notes := "Superlatives create DE contexts"
  }

-- Comparative "than" licenses "any"
def anyComparative : NPIDatum :=
  { sentence := "John is taller than anyone expected"
  , npiItem := "anyone"
  , grammatical := true
  , context := some .comparativeThan
  , notes := "\"than\"-clause is DE"
  }

-- "Few" licenses "any"
def anyFew : NPIDatum :=
  { sentence := "Few students saw anyone"
  , npiItem := "anyone"
  , grammatical := true
  , context := some .fewNP
  , notes := "\"Few NP\" is DE (but not anti-additive)"
  }

-- "Without" licenses "any"
def anyWithout : NPIDatum :=
  { sentence := "John left without seeing anyone"
  , npiItem := "anyone"
  , grammatical := true
  , context := some .withoutClause
  , notes := "\"Without\" is anti-additive"
  }

-- "Before" licenses "any"
def anyBefore : NPIDatum :=
  { sentence := "John left before anyone arrived"
  , npiItem := "anyone"
  , grammatical := true
  , context := some .beforeClause
  , notes := "\"Before\" is DE"
  }

-- "Too...to" licenses "any"
def anyToo : NPIDatum :=
  { sentence := "John was too tired to see anyone"
  , npiItem := "anyone"
  , grammatical := true
  , context := some .tooAdjective
  , notes := "\"Too...to\" creates DE context"
  }

-- Doubt licenses "any"
def anyDoubt : NPIDatum :=
  { sentence := "I doubt that anyone came"
  , npiItem := "anyone"
  , grammatical := true
  , context := some .doubtVerb
  , notes := "\"Doubt\" is a negative verb, creates DE context"
  }

-- "Ever" Examples

/-!
## "Ever" - Temporal NPI
-/

def everNegation : NPIDatum :=
  { sentence := "John has never seen Paris"
  , npiItem := "ever"
  , grammatical := true
  , context := some .sententialNegation
  , notes := "\"Never\" = not + ever"
  }

def everPositive : NPIDatum :=
  { sentence := "*John has ever seen Paris"
  , npiItem := "ever"
  , grammatical := false
  , context := none
  , notes := "Positive context blocks \"ever\""
  }

def everQuestion : NPIDatum :=
  { sentence := "Has John ever been to Paris?"
  , npiItem := "ever"
  , grammatical := true
  , context := some .question
  , notes := "Questions license \"ever\""
  }

def everConditional : NPIDatum :=
  { sentence := "If you ever need help, call me"
  , npiItem := "ever"
  , grammatical := true
  , context := some .conditional
  , notes := "Conditionals license \"ever\""
  }

-- Strong NPIs: "Lift a Finger" / "In Years"

/-!
## Strong NPIs

Strong NPIs require ANTI-ADDITIVE contexts (not merely DE).
"Few" and "at most 3" don't license them.
-/

def liftFingerNegation : NPIDatum :=
  { sentence := "John didn't lift a finger to help"
  , npiItem := "lift a finger"
  , grammatical := true
  , context := some .sententialNegation
  , notes := "Strong NPI: \"not\" is antimorphic, licenses strong NPIs"
  }

def liftFingerFew : NPIDatum :=
  { sentence := "*Few people lifted a finger to help"
  , npiItem := "lift a finger"
  , grammatical := false
  , context := none
  , notes := "Strong NPI: \"few\" is DE but not anti-additive"
  }

def liftFingerWithout : NPIDatum :=
  { sentence := "John left without lifting a finger"
  , npiItem := "lift a finger"
  , grammatical := true
  , context := some .withoutClause
  , notes := "\"Without\" is anti-additive, licenses strong NPIs"
  }

def inYearsNegation : NPIDatum :=
  { sentence := "I haven't seen him in years"
  , npiItem := "in years"
  , grammatical := true
  , context := some .sententialNegation
  , notes := "Strong NPI licensed by negation"
  }

def inYearsFew : NPIDatum :=
  { sentence := "*Few people have seen him in years"
  , npiItem := "in years"
  , grammatical := false
  , context := none
  , notes := "Strong NPI: \"few\" insufficient"
  }

def inYearsQuestion : NPIDatum :=
  { sentence := "?Have you seen him in years?"
  , npiItem := "in years"
  , grammatical := false  -- marginal
  , context := none
  , notes := "Strong NPI: questions insufficient (marginal)"
  }

-- "Yet" Examples

/-!
## "Yet" - Aspectual/Temporal Strong NPI
-/

def yetNegation : NPIDatum :=
  { sentence := "John hasn't arrived yet"
  , npiItem := "yet"
  , grammatical := true
  , context := some .sententialNegation
  , notes := "\"Yet\" licensed by negation"
  }

def yetQuestion : NPIDatum :=
  { sentence := "Has John arrived yet?"
  , npiItem := "yet"
  , grammatical := true
  , context := some .question
  , notes := "\"Yet\" also licensed in questions"
  }

def yetPositive : NPIDatum :=
  { sentence := "*John has arrived yet"
  , npiItem := "yet"
  , grammatical := false
  , context := none
  , notes := "Positive context blocks \"yet\""
  }

-- "At All" Examples

/-!
## "At All" - Scalar Endpoint NPI
-/

def atAllNegation : NPIDatum :=
  { sentence := "John didn't help at all"
  , npiItem := "at all"
  , grammatical := true
  , context := some .sententialNegation
  , notes := "Scalar endpoint: \"not...at all\" = not even minimally"
  }

def atAllQuestion : NPIDatum :=
  { sentence := "Did John help at all?"
  , npiItem := "at all"
  , grammatical := true
  , context := some .question
  , notes := "Licensed in questions"
  }

def atAllPositive : NPIDatum :=
  { sentence := "*John helped at all"
  , npiItem := "at all"
  , grammatical := false
  , context := none
  , notes := "Positive context blocks \"at all\""
  }

def atAllConditional : NPIDatum :=
  { sentence := "If you help at all, I'll be grateful"
  , npiItem := "at all"
  , grammatical := true
  , context := some .conditional
  , notes := "Licensed in conditionals"
  }

-- Intervention Effects

/-!
## Intervention Effects

Some elements block NPI licensing even in DE contexts.
-/

def interventionQuantifier : NPIDatum :=
  { sentence := "*John didn't show everyone anything"
  , npiItem := "anything"
  , grammatical := false  -- on NPI reading
  , context := none
  , notes := "Intervention: \"everyone\" between licensor and NPI blocks licensing"
  }

def noIntervention : NPIDatum :=
  { sentence := "John didn't show anything to everyone"
  , npiItem := "anything"
  , grammatical := true
  , context := some .sententialNegation
  , notes := "No intervention when NPI precedes quantifier"
  }

-- Free Choice "Any"

/-!
## Free Choice "Any"

Not the same as NPI "any"! Free choice any appears in modal/generic contexts.
-/

def fcAnyModal : NPIDatum :=
  { sentence := "You may take any book"
  , npiItem := "any (FC)"
  , grammatical := true
  , context := none
  , notes := "Free choice any: universal-like under modals"
  }

def fcAnyGeneric : NPIDatum :=
  { sentence := "Any dog will bark at strangers"
  , npiItem := "any (FC)"
  , grammatical := true
  , context := none
  , notes := "Free choice any in generic sentences"
  }

def fcAnyImperative : NPIDatum :=
  { sentence := "Take any card"
  , npiItem := "any (FC)"
  , grammatical := true
  , context := none
  , notes := "Free choice any in imperatives"
  }

-- Cross-Linguistic Data

/-!
## Cross-Linguistic Patterns

NPIs exist in many languages with similar distribution.
-/

/-- Cross-linguistic NPI datum -/
structure CrossLingNPI where
  language : String
  npiItem : String
  gloss : String
  licensingContexts : List String
  /-- Scalar direction (Israel 2011; Schwab 2022) -/
  scalarDirection : ScalarDirection := .nonScalar
  notes : String

def hindiKoii : CrossLingNPI :=
  { language := "Hindi"
  , npiItem := "koii bhii"
  , gloss := "anyone at all"
  , licensingContexts := ["negation", "questions", "conditionals"]
  , notes := "Lahiri (1998): licensed by covert EVEN"
  }

def greekKanenas : CrossLingNPI :=
  { language := "Greek"
  , npiItem := "kanenas"
  , gloss := "anyone"
  , licensingContexts := ["negation", "questions", "conditionals", "before"]
  , notes := "Giannakidou (1998): nonveridicality approach"
  }

def japaneseNanimo : CrossLingNPI :=
  { language := "Japanese"
  , npiItem := "nani-mo"
  , gloss := "anything (with mo)"
  , licensingContexts := ["negation"]
  , notes := "Requires clause-final negation"
  }

def germanJemals : CrossLingNPI :=
  { language := "German"
  , npiItem := "jemals"
  , gloss := "ever"
  , licensingContexts := ["negation", "questions", "conditionals", "without"]
  , scalarDirection := .strengthening  -- Schwab (2022): shows NPI illusion
  , notes := "Similar distribution to English \"ever\""
  }

/-- German "so recht" — attenuating NPI. Schwab (2022): does NOT show NPI illusion. -/
def germanSoRecht : CrossLingNPI :=
  { language := "German"
  , npiItem := "so recht"
  , gloss := "all that / particularly"
  , licensingContexts := ["negation"]
  , scalarDirection := .attenuating  -- Schwab (2022): no NPI illusion
  , notes := "Attenuating NPI; weakens assertion. 'nicht so recht' ≈ 'not all that'"
  }

-- NPIs in Questions (van Rooy, Borkin 1971, Krifka)

/-!
## NPIs in Questions

Key insight from van Rooy: NPIs in questions increase ENTROPY (average informativity).
This makes questions more "general" and less biased.

- Questions expecting negative answers → license NPIs
- Questions expecting positive answers → license PPIs
- Rhetorical questions → strong NPIs (lift a finger, etc.)
-/

/-- NPI in question datum -/
structure NPIQuestionDatum where
  sentence : String
  npiItem : String
  questionType : String  -- "polar", "wh", "rhetorical"
  grammatical : Bool
  expectedBias : String  -- "negative", "positive", "neutral"
  notes : String

-- Information-seeking questions with weak NPIs
def everInQuestion : NPIQuestionDatum :=
  { sentence := "Have you ever been to China?"
  , npiItem := "ever"
  , questionType := "polar"
  , grammatical := true
  , expectedBias := "negative"
  , notes := "van Rooy: NPI increases entropy, reducing bias. Krifka 1995"
  }

def anyInPolarQuestion : NPIQuestionDatum :=
  { sentence := "Does Sue have any potatoes?"
  , npiItem := "any"
  , questionType := "polar"
  , grammatical := true
  , expectedBias := "negative"
  , notes := "Domain widening makes question more general. K&L 1990"
  }

def anyInWhQuestion : NPIQuestionDatum :=
  { sentence := "Who has ever been to China?"
  , npiItem := "ever"
  , questionType := "wh"
  , grammatical := true
  , expectedBias := "neutral"
  , notes := "Wh-questions DE in subject position"
  }

def anyInRestrictor : NPIQuestionDatum :=
  { sentence := "Who, of those who has ever been to China, climbed the Wall?"
  , npiItem := "ever"
  , questionType := "wh"
  , grammatical := true
  , expectedBias := "neutral"
  , notes := "NPI in restrictor of wh-question"
  }

-- Rhetorical questions with strong NPIs
def liftFingerQuestion : NPIQuestionDatum :=
  { sentence := "Did John lift a finger to help Mary?"
  , npiItem := "lift a finger"
  , questionType := "rhetorical"
  , grammatical := true
  , expectedBias := "negative"
  , notes := "Strong NPI → rhetorical reading (implies John didn't help)"
  }

def batAnEyeQuestion : NPIQuestionDatum :=
  { sentence := "Who bats an eye when the boss comes around?"
  , npiItem := "bat an eye"
  , questionType := "rhetorical"
  , grammatical := true
  , expectedBias := "negative"
  , notes := "Strong NPI in wh-question → rhetorical (nobody does)"
  }

def aDropQuestion : NPIQuestionDatum :=
  { sentence := "Doesn't Lois drink a drop of liquor?"
  , npiItem := "a drop"
  , questionType := "rhetorical"
  , grammatical := true
  , expectedBias := "negative"
  , notes := "Borkin 1971: presupposes Lois doesn't drink liquor"
  }

def millionYearsQuestion : NPIQuestionDatum :=
  { sentence := "Would you, in a million years, do that?"
  , npiItem := "in a million years"
  , questionType := "rhetorical"
  , grammatical := true
  , expectedBias := "negative"
  , notes := "Maximizer NPI → rhetorical (implies never)"
  }

-- PPIs in questions (opposite bias)
def ppiRatherQuestion : NPIQuestionDatum :=
  { sentence := "Wouldn't you rather stay here?"
  , npiItem := "rather (PPI)"
  , questionType := "polar"
  , grammatical := true
  , expectedBias := "positive"
  , notes := "PPI in negative question → expects positive answer"
  }

def ppiPrettyQuestion : NPIQuestionDatum :=
  { sentence := "Aren't you pretty tired?"
  , npiItem := "pretty (PPI)"
  , questionType := "polar"
  , grammatical := true
  , expectedBias := "positive"
  , notes := "PPI licensed when positive answer expected"
  }

/-- All question data -/
def questionData : List NPIQuestionDatum :=
  [everInQuestion, anyInPolarQuestion, anyInWhQuestion, anyInRestrictor,
   liftFingerQuestion, batAnEyeQuestion, aDropQuestion, millionYearsQuestion,
   ppiRatherQuestion, ppiPrettyQuestion]

-- Minimizers vs Non-Minimizers (Israel 2001)

/-!
## Minimizers vs Non-Minimizers

Israel (2001) notes NPIs like "all that" and "long" that don't denote minimal quantities.
Their use under negation makes the sentence LESS informative, not more.

This challenges pure informativity-based accounts but supports relevance-based ones.
-/

def allThatNPI : NPIDatum :=
  { sentence := "He is not all that clever"
  , npiItem := "all that"
  , grammatical := true
  , context := some .sententialNegation
  , notes := "Non-minimizer: weakens rather than strengthens. Israel 2001"
  }

def longNPI : NPIDatum :=
  { sentence := "This won't take long"
  , npiItem := "long"
  , grammatical := true
  , context := some .sententialNegation
  , notes := "Non-minimizer NPI. Israel 2001"
  }

-- Aggregate Data

/-- All "any" examples -/
def anyData : List NPIDatum :=
  [anyNegation, anyPositive, anyQuestion, anyConditional,
   anyUniversal, anyOnly, anySuperlative, anyComparative,
   anyFew, anyWithout, anyBefore, anyToo, anyDoubt]

/-- All "ever" examples -/
def everData : List NPIDatum :=
  [everNegation, everPositive, everQuestion, everConditional]

/-- All strong NPI examples -/
def strongNPIData : List NPIDatum :=
  [liftFingerNegation, liftFingerFew, liftFingerWithout,
   inYearsNegation, inYearsFew, inYearsQuestion]

/-- All "yet" examples -/
def yetData : List NPIDatum :=
  [yetNegation, yetQuestion, yetPositive]

/-- All "at all" examples -/
def atAllData : List NPIDatum :=
  [atAllNegation, atAllQuestion, atAllPositive, atAllConditional]

-- Empirical Generalizations

/-!
## Core Empirical Generalizations

### 1. The DE Generalization (Ladusaw 1979)
Weak NPIs are licensed in downward-entailing contexts.

Test: If "All As are Bs" entails "All As are Cs", then:
- In UE contexts: "All As are Bs" entails "All As are Cs"
- In DE contexts: "All As are Cs" entails "All As are Bs"

### 2. Anti-Additivity for Strong NPIs (Zwarts 1998)
Strong NPIs require anti-additive contexts:
- f(A∨B) = f(A) ∧ f(B)

"No one" is anti-additive: "No one saw A or B" = "No one saw A and no one saw B"
"Few people" is merely DE: "Few saw A or B" ≠ "Few saw A and few saw B"

### 3. The Scalar Approach (Fauconnier, Krifka)
NPIs involve scalar reversal:
- In positive contexts: "some" > "any" (some is more informative)
- In negative contexts: "any" > "some" (any is more informative)

### 4. Domain Widening (Kadmon & Landman 1993)
"Any" widens the domain beyond contextual restriction:
- "I don't have an opinion" (contextually restricted)
- "I don't have any opinion" (widened to all opinions)

### 5. EVEN Theory (Lahiri 1998, Chierchia 2013)
NPIs involve covert EVEN:
- [EVEN anyone] = "even the most unlikely person"
- In DE contexts: wide domain = least likely = EVEN presupposition satisfied

### 6. Entropy/Utility (van Rooy 2003)
NPIs maximize RELEVANCE (utility):
- In assertions: strength = informativity (entailment)
- In questions: strength = entropy (average informativity)
- NPIs in questions increase entropy → more useful questions
- Unifies assertion licensing (DE) with question licensing (bias reduction)

### 7. Local RSA Approach
Local RSA derives NPI effects from polarity-sensitive informativity:
- In UE: smaller domain = more informative = preferred (→ EXH effects)
- In DE: wider domain = more informative = preferred (→ NPI licensing)
- No covert EVEN needed - it's pragmatic inference
-/

-- Tests for Generalizations

-- Weak NPIs licensed in all DE contexts
#guard anyData.filter (λ d => d.grammatical)
      |>.all (λ d => d.context.isSome)

-- Strong NPIs not licensed by merely-DE "few"
#guard strongNPIData.filter (λ d => d.npiItem == "lift a finger" || d.npiItem == "in years")
      |>.filter (λ d => d.context == some .fewNP)
      |>.all (λ d => !d.grammatical)

-- Strong NPIs licensed by anti-additive "without"
#guard strongNPIData.filter (λ d => d.context == some .withoutClause)
      |>.all (λ d => d.grammatical)


/-!
## N-words and Scale-Minimality

Chierchia (2013) "Logic in Grammar" observes that N-WORDS (negative indefinites
that participate in Negative Concord) are constrained to SCALE-MINIMAL elements.

### What are N-words?

N-words are negative indefinites in Romance/Slavic languages that:
1. Can appear in Negative Concord (NC) constructions
2. Have negative force when appearing alone
3. Lose negative force under c-commanding negation (NC)

Examples: Italian "nessuno" (no-one), "niente" (nothing), "neanche" (not even)

### The Scale-Minimality Constraint

N-words are formed ONLY from scale-minimal quantifiers:

| Base | Scale Position | N-word? | Example |
|------|---------------|---------|---------|
| uno (one) | minimal | ✓ | nessuno |
| due (two) | non-minimal | ✗ | *nessdue |
| most | non-minimal | ✗ | *nessmost |
| every | maximal | ✗ | *nessevery |

### Why This Constraint?

Chierchia's explanation via scalar implicature:

N-words require PURELY downward-entailing environments. But NON-MINIMAL
scale positions generate POSITIVE implicatures:

- "No more than ten" implicates "at least some" (positive component!)
- This positive implicature DISRUPTS the DE environment
- Only scale-MINIMAL elements avoid this problem

### The "neanche" Test (Chierchia p.6-7)

Italian "neanche" (roughly "not even N") shows this pattern clearly:

✓ "Non ho visto neanche un professore"
   (I didn't see even one professor)

✗ "*Non ho visto neanche due professori"
   (I didn't see even two professors)

BUT: "neanche due" becomes acceptable when "two" is contextually
construed as MINIMAL on a relevant scale:

✓ "Quel problema non lo risolverebbero neanche due professori"
   (That problem wouldn't be solved by even two professors)
   [Context: two is the minimum expected number to solve it]

### References

- Chierchia (2013). Logic in Grammar. Cambridge. Ch.1, p.5-8.
- Zanuttini (1991). Syntactic Properties of Sentential Negation.
- Ladusaw (1992). Expressing Negation.
-/

/--
Scale position of a quantifier/numeral.
-/
inductive ScalePosition where
  | minimal       -- Bottom of scale: one, a, some
  | intermediate  -- Middle: two, three, most, many
  | maximal       -- Top: every, all
  deriving DecidableEq, BEq, Repr

/--
An N-word (negative indefinite in NC language).
-/
structure NWord where
  /-- Surface form -/
  form : String
  /-- Language -/
  language : String
  /-- Decomposition: NEG + base -/
  decomposition : String
  /-- Scale position of the base -/
  baseScalePosition : ScalePosition
  /-- Is it a real N-word? -/
  isRealNWord : Bool
  /-- Notes -/
  notes : String
  deriving Repr

/-- Italian N-words -/
def nessuno : NWord :=
  { form := "nessuno"
  , language := "Italian"
  , decomposition := "NEG + uno (one)"
  , baseScalePosition := .minimal
  , isRealNWord := true
  , notes := "Standard N-word: no-one" }

def niente : NWord :=
  { form := "niente"
  , language := "Italian"
  , decomposition := "NEG + ente (thing)"
  , baseScalePosition := .minimal
  , isRealNWord := true
  , notes := "Standard N-word: nothing" }

def nessdue_hypothetical : NWord :=
  { form := "*nessdue"
  , language := "Italian (hypothetical)"
  , decomposition := "NEG + due (two)"
  , baseScalePosition := .intermediate
  , isRealNWord := false
  , notes := "Predicted non-existent: non-minimal base" }

def nessmost_hypothetical : NWord :=
  { form := "*nessmost"
  , language := "Italian (hypothetical)"
  , decomposition := "NEG + most"
  , baseScalePosition := .intermediate
  , isRealNWord := false
  , notes := "Predicted non-existent: non-minimal base" }

/-- Spanish N-words -/
def nadie : NWord :=
  { form := "nadie"
  , language := "Spanish"
  , decomposition := "NEG + base"
  , baseScalePosition := .minimal
  , isRealNWord := true
  , notes := "Standard N-word: no-one" }

def nada : NWord :=
  { form := "nada"
  , language := "Spanish"
  , decomposition := "NEG + base"
  , baseScalePosition := .minimal
  , isRealNWord := true
  , notes := "Standard N-word: nothing" }

/--
All N-word examples.
-/
def nwordExamples : List NWord :=
  [nessuno, niente, nessdue_hypothetical, nessmost_hypothetical, nadie, nada]

-- Scale-minimality predicts N-word existence
#guard nwordExamples.all (λ nw =>
  (nw.baseScalePosition == .minimal) == nw.isRealNWord)

-- ----------------------------------------------------------------------------
-- 9.1: "neanche" Examples (Chierchia p.6-7)
-- ----------------------------------------------------------------------------

/--
"neanche" (not even) example with scale interaction.
-/
structure NeancheExample where
  /-- Italian sentence -/
  italian : String
  /-- English translation -/
  english : String
  /-- Numeral used -/
  numeral : Nat
  /-- Is it grammatical? -/
  grammatical : Bool
  /-- Context makes numeral scale-minimal? -/
  contextuallyMinimal : Bool
  /-- Explanation -/
  explanation : String
  deriving Repr

def neanche_uno : NeancheExample :=
  { italian := "Non ho visto neanche un professore"
  , english := "I didn't see even one professor"
  , numeral := 1
  , grammatical := true
  , contextuallyMinimal := true
  , explanation := "One is inherently scale-minimal: always OK" }

def neanche_due_bad : NeancheExample :=
  { italian := "*Non ho visto neanche due professori"
  , english := "I didn't see even two professors"
  , numeral := 2
  , grammatical := false
  , contextuallyMinimal := false
  , explanation := "Two is non-minimal on default numeral scale: blocked" }

def neanche_due_ok : NeancheExample :=
  { italian := "Quel problema non lo risolverebbero neanche due professori"
  , english := "That problem wouldn't be solved by even two professors"
  , numeral := 2
  , grammatical := true
  , contextuallyMinimal := true
  , explanation := "Context: two is minimal expected number to solve it" }

def neanche_dieci_bad : NeancheExample :=
  { italian := "*Non ho visto neanche dieci professori"
  , english := "I didn't see even ten professors"
  , numeral := 10
  , grammatical := false
  , contextuallyMinimal := false
  , explanation := "Ten is highly non-minimal on default scale" }

def neanche_dieci_ok : NeancheExample :=
  { italian := "Per risolvere quel problema, neanche dieci professori basterebbero"
  , english := "To solve that problem, even ten professors wouldn't suffice"
  , numeral := 10
  , grammatical := true
  , contextuallyMinimal := true
  , explanation := "Context: ten is minimal expected number for the task" }

/--
All neanche examples.
-/
def neancheExamples : List NeancheExample :=
  [neanche_uno, neanche_due_bad, neanche_due_ok, neanche_dieci_bad, neanche_dieci_ok]

-- Grammaticality tracks contextual minimality
#guard neancheExamples.all (λ ex =>
  ex.grammatical == ex.contextuallyMinimal)

-- ----------------------------------------------------------------------------
-- 9.2: Theoretical Explanation
-- ----------------------------------------------------------------------------

/-!
### Why Scale-Minimality Matters

The key insight: intermediate scale positions generate POSITIVE scalar implicatures.

Consider "no more than ten students came":
- Literal: ≤10 students came
- Scalar implicature: at least some came (not zero!)

This positive implicature component DISRUPTS the purely DE environment
that N-words require.

Only scale-MINIMAL elements avoid generating positive implicatures:
- "No one came" → no positive component
- "Nothing happened" → no positive component

### Connection to NPI Licensing

This explains why N-words behave like STRONG NPIs:
- Strong NPIs require ANTI-ADDITIVE contexts (not just DE)
- The positive implicature from non-minimal bases disrupts anti-additivity
- Scale-minimal bases preserve the pure negativity needed

### Predictions

1. Cross-linguistically, N-words should be based on minimal scale elements
2. N-words should fail in contexts where their base triggers positive implicatures
3. Contextual manipulation of scale-minimality should affect N-word acceptability
-/

/--
Summary of scale-minimality constraint.
-/
structure ScaleMinimalityPrediction where
  /-- The constraint -/
  constraint : String
  /-- Explanation -/
  explanation : String
  /-- Empirical support -/
  evidence : String
  deriving Repr

def scaleMinimalityConstraint : ScaleMinimalityPrediction :=
  { constraint := "N-words are formed only from scale-minimal elements"
  , explanation := "Non-minimal elements generate positive implicatures that disrupt DE"
  , evidence := "Cross-linguistic: nessuno, nadie, etc. based on 'one'; *nessdue impossible" }

-- German NPI scalar direction: jemals is strengthening, soRecht is attenuating
#guard germanJemals.scalarDirection == .strengthening
#guard germanSoRecht.scalarDirection == .attenuating

end Phenomena.Polarity.NPIs
