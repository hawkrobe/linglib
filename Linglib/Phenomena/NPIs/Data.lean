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

namespace Phenomena.NPIs

-- ============================================================================
-- NPI Classification
-- ============================================================================

/-- Types of NPI items -/
inductive NPIType where
  | weak       -- Licensed in DE contexts (any, ever)
  | strong     -- Require anti-additive contexts (in years, lift a finger)
  | superStrong -- Require antimorphic contexts (yet in some dialects)
  deriving DecidableEq, Repr, BEq

/-- Semantic property of NPI (what makes it polarity-sensitive) -/
inductive NPIProperty where
  | domainWidening   -- Widens quantifier domain (any vs some)
  | scalarEndpoint   -- References scalar endpoint (at all, a bit)
  | emphatic         -- Strong/emphatic meaning (lift a finger)
  | temporal         -- Temporal reference (ever, yet)
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- Licensing Context Classification
-- ============================================================================

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

/-- Monotonicity classification -/
inductive Monotonicity where
  | upwardEntailing   -- UE: preserves entailment direction
  | downwardEntailing -- DE: reverses entailment direction
  | nonMonotone       -- Neither UE nor DE
  deriving DecidableEq, Repr, BEq

/-- Anti-additivity classification (stronger than DE) -/
inductive AntiAdditivity where
  | antiAdditive  -- f(A∨B) = f(A)∧f(B) : "no", "without"
  | antiMorphic   -- antiAdditive + f(A∧B) = f(A)∨f(B) : "not"
  | merelyDE      -- DE but not anti-additive: "few", "at most 3"
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- Basic Data Structure
-- ============================================================================

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

-- ============================================================================
-- Classic "Any" Examples
-- ============================================================================

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

-- ============================================================================
-- "Ever" Examples
-- ============================================================================

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

-- ============================================================================
-- Strong NPIs: "Lift a Finger" / "In Years"
-- ============================================================================

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

-- ============================================================================
-- "Yet" Examples
-- ============================================================================

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

-- ============================================================================
-- "At All" Examples
-- ============================================================================

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

-- ============================================================================
-- Intervention Effects
-- ============================================================================

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

-- ============================================================================
-- Free Choice "Any"
-- ============================================================================

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

-- ============================================================================
-- Cross-Linguistic Data
-- ============================================================================

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
  , notes := "Similar distribution to English \"ever\""
  }

-- ============================================================================
-- NPIs in Questions (van Rooy, Borkin 1971, Krifka)
-- ============================================================================

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

-- ============================================================================
-- Minimizers vs Non-Minimizers (Israel 2001)
-- ============================================================================

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

-- ============================================================================
-- Aggregate Data
-- ============================================================================

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

-- ============================================================================
-- Empirical Generalizations
-- ============================================================================

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

-- ============================================================================
-- Tests for Generalizations
-- ============================================================================

-- Weak NPIs licensed in all DE contexts
#guard anyData.filter (fun d => d.grammatical)
      |>.all (fun d => d.context.isSome)

-- Strong NPIs not licensed by merely-DE "few"
#guard strongNPIData.filter (fun d => d.npiItem == "lift a finger" || d.npiItem == "in years")
      |>.filter (fun d => d.context == some .fewNP)
      |>.all (fun d => !d.grammatical)

-- Strong NPIs licensed by anti-additive "without"
#guard strongNPIData.filter (fun d => d.context == some .withoutClause)
      |>.all (fun d => d.grammatical)

end Phenomena.NPIs
