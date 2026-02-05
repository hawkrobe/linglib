/-
# Lo Guercio (2025) - Empirical Data on Anti-Conventional Implicatures

Phenomena from "Maximize Conventional Implicatures!" Semantics & Pragmatics 18(9).

This file contains empirical facts from the paper:
- Judgment data on when ACIs arise
- No theoretical commitments (those belong in Theories/NeoGricean/)

## Paper Citation

Lo Guercio, N. (2025). Maximize Conventional Implicatures!
Semantics & Pragmatics, 18(9). https://doi.org/10.3765/sp.18.9
-/

namespace Phenomena.LoGuercio2025


/--
Judgment status for whether an ACI arises.
-/
inductive ACIJudgment where
  | arises          -- The ACI inference is drawn
  | doesNotArise    -- The ACI inference is not drawn
  | marginal        -- Speakers vary / uncertain
  deriving DecidableEq, BEq, Repr

/--
A single empirical item from the paper.
-/
structure EmpiricalItem where
  /-- Example number(s) from the paper -/
  exampleNum : String
  /-- The sentence tested -/
  sentence : String
  /-- The potential ACI content -/
  potentialACI : String
  /-- Whether the ACI arises empirically -/
  judgment : ACIJudgment
  /-- Prior context (if any) -/
  priorContext : Option String
  deriving Repr


/--
Example (18): Out of the blue, NO epithet ACI.

"John arrived late."
⇝̸ ¬(John is a bastard)

Out of the blue, there's no inference that the speaker doesn't dislike John.
The epithet alternative is not contextually relevant.
-/
def ex18_outOfBlue_noACI : EmpiricalItem :=
  { exampleNum := "18"
  , sentence := "John arrived late."
  , potentialACI := "Speaker doesn't think John is a bastard"
  , judgment := .doesNotArise
  , priorContext := none }

/--
Example (19): Spanish honorific parallel, out of the blue.

"Diego entró."
⇝̸ ¬(speaker respects Diego)

Same pattern: no ACI without prior mention of honorific.
-/
def ex19_spanish_outOfBlue : EmpiricalItem :=
  { exampleNum := "19"
  , sentence := "Diego entró."
  , potentialACI := "Speaker doesn't respect Diego"
  , judgment := .doesNotArise
  , priorContext := none }

/--
Example (20): With prior epithet mention, ACI arises.

Context: "John arrived first, then that bastard Pedro arrived."
"John arrived" ⇝ ¬(John is a bastard)

When "bastard" is mentioned for Pedro, using bare "John" triggers the ACI.
-/
def ex20_priorMention_ACI : EmpiricalItem :=
  { exampleNum := "20"
  , sentence := "John arrived first"
  , potentialACI := "Speaker doesn't think John is a bastard"
  , judgment := .arises
  , priorContext := some "...then that bastard Pedro arrived" }

/--
Example (21): Contrastive epithet ACI.

"Juan arrived first, then that bastard Pedro arrived."
⇝ ¬(Juan is a bastard)

The asymmetry in CI content (bastard for Pedro, not Juan) triggers the ACI.
-/
def ex21_contrastive_ACI : EmpiricalItem :=
  { exampleNum := "21"
  , sentence := "Juan arrived first, then that bastard Pedro arrived."
  , potentialACI := "Speaker doesn't think Juan is a bastard"
  , judgment := .arises
  , priorContext := none }


/--
Example (22)-(23): Spanish honorific ACI.

"Primero entró Donato. Después entró Don Pedro."
⇝ ¬(speaker respects Donato)

When "Don" is used for Pedro but not Donato, ACI arises.
-/
def ex22_23_honorific_ACI : EmpiricalItem :=
  { exampleNum := "22-23"
  , sentence := "Primero entró Donato. Después entró Don Pedro."
  , potentialACI := "Speaker doesn't respect Donato (as much as Don Pedro)"
  , judgment := .arises
  , priorContext := none }


/--
Example (31)-(32): Nominal appositive ACI.

"Diego recommended an aspirin. Laura, a doctor, recommended an antibiotic."
⇝ ¬(Diego is a doctor)

The appositive "a doctor" for Laura triggers ACI about Diego.
-/
def ex31_32_appositive_ACI : EmpiricalItem :=
  { exampleNum := "31-32"
  , sentence := "Diego recommended an aspirin. Laura, a doctor, recommended an antibiotic."
  , potentialACI := "Diego is not a doctor"
  , judgment := .arises
  , priorContext := none }


/--
Property test data structure.
-/
structure PropertyTest where
  /-- Property being tested -/
  property : String
  /-- Example number -/
  exampleNum : String
  /-- Test sentence -/
  sentence : String
  /-- Result: does the property hold? -/
  propertyHolds : Bool
  /-- Comparison: how does this differ from SIs/antipresuppositions? -/
  comparison : Option String
  deriving Repr

/--
Example (50): ACIs do not require same assertive content.

"Juan called María or that bastard Pedro"
ACI: ¬(María is a bastard)

Even though the stronger alternative "Juan called María and that bastard Pedro"
has different assertive content (and vs or), the ACI still arises.

This distinguishes ACIs from antipresuppositions (which do require same assertion).
-/
def ex50_different_assertion : PropertyTest :=
  { property := "ACIs independent of assertive content"
  , exampleNum := "50"
  , sentence := "Juan called María or that bastard Pedro"
  , propertyHolds := true
  , comparison := some "Unlike antipresuppositions, ACIs arise even with different at-issue content" }

/--
Example (52): ACIs are cancellable.

"Juan arrived first, then that bastard Pedro arrived (by the way, Juan is also a bastard)"

The parenthetical cancels the ACI.
-/
def ex52_cancellable : PropertyTest :=
  { property := "ACIs are cancellable"
  , exampleNum := "52"
  , sentence := "Juan arrived first, then that bastard Pedro arrived (by the way, Juan is also a bastard)"
  , propertyHolds := true
  , comparison := some "Like SIs and antipresuppositions, ACIs can be explicitly cancelled" }

/--
Example (61): ACIs not affected by downward-entailing contexts.

"I doubt that Juan or that bastard Pedro passed"
SI blocked: ⇝̸ ¬(I doubt Juan and Pedro passed)
ACI not blocked: ⇝ ¬(Juan is a bastard)

DE context blocks the scalar implicature but not the ACI.
-/
def ex61_de_insensitive : PropertyTest :=
  { property := "ACIs not affected by DE contexts"
  , exampleNum := "61"
  , sentence := "I doubt that Juan or that bastard Pedro passed"
  , propertyHolds := true
  , comparison := some "Unlike SIs (blocked in DE), ACIs arise regardless of polarity context" }

/--
Example (63): ACIs are reinforceable.

"Juan arrived first, that bastard Pedro arrived second (by the way, Juan is not a bastard)"

The reinforcement is informative, not redundant (unlike presupposition reinforcement).
-/
def ex63_reinforceable : PropertyTest :=
  { property := "ACIs are reinforceable"
  , exampleNum := "63"
  , sentence := "Juan arrived first, that bastard Pedro arrived second (by the way, Juan is not a bastard)"
  , propertyHolds := true
  , comparison := some "Unlike presupposition reinforcement (redundant), ACI reinforcement is informative" }


/--
Comparison of scalar inference types from Lo Guercio Table 1.
-/
structure InferenceTypeComparison where
  /-- Inference type name -/
  name : String
  /-- Does it require same assertive content? -/
  requiresSameAssertion : Bool
  /-- Is it affected by DE contexts? -/
  affectedByDE : Bool
  /-- Is it cancellable? -/
  cancellable : Bool
  /-- Is it reinforceable (without redundancy)? -/
  reinforceable : Bool
  deriving Repr

/-- Scalar Implicature properties from Lo Guercio -/
def siComparison : InferenceTypeComparison :=
  { name := "Scalar Implicature"
  , requiresSameAssertion := false
  , affectedByDE := true       -- Blocked in DE contexts
  , cancellable := true
  , reinforceable := true }

/-- Antipresupposition properties from Lo Guercio -/
def antipresupComparison : InferenceTypeComparison :=
  { name := "Antipresupposition"
  , requiresSameAssertion := true  -- MP requires same assertion
  , affectedByDE := false          -- Varies by analysis
  , cancellable := true
  , reinforceable := false }       -- Redundant

/-- ACI properties from Lo Guercio -/
def aciComparison : InferenceTypeComparison :=
  { name := "Anti-Conventional Implicature"
  , requiresSameAssertion := false  -- CI independent of assertion
  , affectedByDE := false           -- CI doesn't interact with entailment
  , cancellable := true
  , reinforceable := true }


/--
CI expression types tested in the paper.
-/
inductive CIExpressionType where
  | epithet              -- "that bastard John"
  | honorific            -- "Don Pedro", "-san" (Japanese)
  | nominalAppositive    -- "Laura, a doctor"
  | supplementaryAdverb  -- "Luckily, p"
  | emotiveMarker        -- "Alas, p"
  deriving DecidableEq, BEq, Repr

/--
Evidence for ACI arising with each expression type.
-/
def expressionTypeCoverage : List (CIExpressionType × String × Bool) :=
  [ (.epithet, "§3.2.1 Examples 18-21", true)              -- Extensively tested
  , (.honorific, "§3.2.1 Examples 22-23", true)            -- Spanish "Don", Japanese ADTs
  , (.nominalAppositive, "§3.2.3 Examples 31-32", true)    -- "Laura, a doctor"
  , (.supplementaryAdverb, "§3.2.3", true)                 -- "Luckily"
  , (.emotiveMarker, "§3.2.3", true) ]                     -- "Alas"

end Phenomena.LoGuercio2025
