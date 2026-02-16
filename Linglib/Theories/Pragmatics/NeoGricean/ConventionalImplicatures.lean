/-
# Anti-Conventional Implicatures (ACIs)

Formalization of Lo Guercio (2025) "Maximize Conventional Implicatures!"
Semantics & Pragmatics 18(9).

## Thesis

Scalar inferences can arise from comparing CI content, not just at-issue
or presuppositional content. These are Anti-Conventional Implicatures (ACIs).

The mechanism parallels:
- Scalar Implicatures: Compare at-issue content (Quantity maxim)
- Antipresuppositions: Compare presuppositional content (Maximize Presupposition)
- ACIs: Compare CI content (Maximize Conventional Implicatures)

## The MCIs! Principle (Lo Guercio Definition 15)

Do not use φ if there's a formal alternative φ' ∈ F(φ) such that:
a. ⟦φ'⟧ᵘ ⊂ ⟦φ⟧ᵘ  (CI-stronger)
b. φ' ∈ C  (contextually relevant)
c. ¬⟦φ'⟧ᵘ doesn't contradict C given φ  (innocently excludable)

## Key Expressions

- Epithets: "that bastard John" vs "John"
- Honorifics: "Don Pedro" vs "Pedro" (Spanish), ADTs (Japanese)
- Appositives: "Laura, a doctor" vs "Laura"
- Supplementary adverbs: "Luckily, p" vs "p"
- Emotive markers: "Alas, p" vs "p"

## Properties of ACIs (vs SIs and Antipresuppositions)

1. Don't require same assertive content (unlike antipresuppositions)
2. Not affected by DE contexts (unlike SIs)
3. Cancellable
4. Reinforceable
5. Pattern with CI expressions on embeddability

## References

- Lo Guercio, N. (2025). Maximize Conventional Implicatures! S&P 18(9).
- Potts, C. (2005). The Logic of Conventional Implicatures. OUP.
- Fox, D. & Katzir, R. (2011). On the characterization of alternatives. NLS 19.
- Gutzmann, D. (2015). Use-Conditional Meaning. OUP.
- McCready, E. (2019). The Semantics and Pragmatics of Honorification. OUP.
-/

import Linglib.Theories.Semantics.Lexical.Expressives.Basic
import Linglib.Theories.Pragmatics.NeoGricean.Core.Basic
import Linglib.Theories.Pragmatics.NeoGricean.Core.Alternatives
import Linglib.Theories.Semantics.Entailment.Polarity

namespace NeoGricean.ConventionalImplicatures

open Semantics.Lexical.Expressives
open Semantics.Entailment.Polarity (ContextPolarity)
open NeoGricean (BeliefState)


/--
Types of CI-bearing expressions that can form alternative sets.

Following Lo Guercio's examples from §3.2:
- Epithets and honorifics (§3.2.1)
- Nominal appositives (§3.2.3)
- Supplementary adverbs (§3.2.3)
- Emotive markers (§3.2.3)
-/
inductive CIAlternativeType where
  | epithet           -- "John" vs "that bastard John"
  | honorific         -- "Pedro" vs "Don Pedro"
  | nominalAppositive -- "Laura" vs "Laura, a doctor"
  | suppAdverb        -- "p" vs "Luckily, p"
  | emotiveMarker     -- "p" vs "Alas, p"
  deriving Repr, DecidableEq, BEq

/--
A CI alternative pair: weaker and stronger CI expressions.

Following Fox & Katzir (2011), alternatives must be:
1. Formal alternatives (constructible by substitution)
2. At most as complex as the original
3. Contextually relevant
-/
structure CIAlternativePair where
  /-- Type of CI expression -/
  altType : CIAlternativeType
  /-- The weaker CI expression (used) -/
  weaker : String
  /-- The stronger CI expression (alternative) -/
  stronger : String
  /-- Is the stronger alternative contextually relevant? -/
  strongerIsRelevant : Bool
  deriving Repr

/--
Standard CI alternative pairs from Lo Guercio.

The stronger alternative is only a formal alternative if it is
contextually relevant (mentioned, subconstituent, or lexical).
-/
def epithetPair (name : String) (relevant : Bool) : CIAlternativePair :=
  { altType := .epithet
  , weaker := name
  , stronger := s!"that bastard {name}"
  , strongerIsRelevant := relevant }

def honorificPair (name : String) (relevant : Bool) : CIAlternativePair :=
  { altType := .honorific
  , weaker := name
  , stronger := s!"Don {name}"
  , strongerIsRelevant := relevant }

def appositivePair (name property : String) (relevant : Bool) : CIAlternativePair :=
  { altType := .nominalAppositive
  , weaker := name
  , stronger := s!"{name}, {property}"
  , strongerIsRelevant := relevant }


/--
Result of applying MCIs! (Maximize Conventional Implicatures).

Parallel to StandardRecipeResult from NeoGricean.Core.Basic.
-/
structure MCIsResult where
  /-- The utterance analyzed -/
  utterance : String
  /-- The CI alternative considered -/
  ciAlternative : String
  /-- Is the alternative CI-stronger? -/
  alternativeIsCIStronger : Bool
  /-- Is the alternative a formal alternative (contextually relevant)? -/
  alternativeIsFormal : Bool
  /-- Does an ACI arise? -/
  aciArises : Bool
  /-- The inferred ACI content (if any) -/
  aciContent : Option String
  deriving Repr

/--
Apply MCIs! to derive an ACI.

Following Lo Guercio (2025) Definition 15:
- If speaker used φ with weaker CI
- And there's a formal alternative φ' with stronger CI
- Then infer speaker couldn't felicitously use φ'
- With competence: speaker believes ¬(CI content of φ')
-/
def applyMCIs (pair : CIAlternativePair) : MCIsResult :=
  let aciArises := pair.strongerIsRelevant  -- ACI only if alternative is formal
  { utterance := pair.weaker
  , ciAlternative := pair.stronger
  , alternativeIsCIStronger := true  -- By construction of pairs
  , alternativeIsFormal := pair.strongerIsRelevant
  , aciArises := aciArises
  , aciContent := if aciArises then some s!"¬(CI of {pair.stronger})" else none }


/--
Example (18)-(19): Out of the blue, NO ACI arises.

"John arrived late" ⇝̸ ¬(John is a bastard)
"Diego entró" ⇝̸ ¬(speaker respects Diego)

Because "that bastard John" is not a formal alternative; it is more complex.
-/
def example_outOfBlue_noACI : MCIsResult :=
  applyMCIs (epithetPair "John" false)  -- Not relevant out of the blue

#check example_outOfBlue_noACI  -- aciArises = false

/--
Example (20)-(21): With prior mention, an ACI arises.

"John arrived first, then that bastard Pedro arrived."
Implicates: not(John is a bastard)

Because "that bastard" is now contextually relevant (mentioned),
"that bastard John" is a formal alternative.
-/
def example_priorMention_ACI : MCIsResult :=
  applyMCIs (epithetPair "John" true)  -- Relevant due to prior mention

#check example_priorMention_ACI  -- aciArises = true

/--
Example (22)-(23): Honorific parallel.

"Primero entró Donato. Después entró Don Pedro."
⇝ ¬(speaker respects Donato)
-/
def example_honorific_ACI : MCIsResult :=
  applyMCIs (honorificPair "Donato" true)

/--
Example (31)-(32): Appositive parallel.

"Diego recommended an aspirin. Laura, a doctor, recommended an antibiotic."
⇝ ¬(Diego is a doctor)
-/
def example_appositive_ACI : MCIsResult :=
  applyMCIs (appositivePair "Diego" "a doctor" true)


/--
ACIs do not require the same assertive content.

Unlike antipresuppositions, ACIs can arise even when the utterance
and alternative have different truth conditions.

Example (50): "Juan called Maria or that bastard Pedro"
- ACI: not(Maria is a bastard)
- Stronger alternative has different assertive content (and vs or)

CI content is independent of at-issue content (Potts 2005).
-/
theorem aci_independent_of_assertion :
    -- Constructive witness: ACI arises despite different assertions
    ∃ (pair : CIAlternativePair),
      pair.strongerIsRelevant = true ∧  -- Formal alternative
      -- (assertive content differs - not formalized here)
      (applyMCIs pair).aciArises = true := by
  exact ⟨epithetPair "John" true, rfl, rfl⟩

/--
ACIs are not affected by DE contexts.

Unlike scalar implicatures, ACIs arise in both UE and DE contexts.

Example (61): "I doubt that Juan or that bastard Pedro passed"
- SI blocked: does not implicate not(I doubt Juan and that bastard Pedro passed)
- ACI not blocked: implicates not(Juan is a bastard)

CI content does not interact with truth-conditional entailment.
-/
def aciInDEContext (pair : CIAlternativePair) (_ctx : ContextPolarity) : MCIsResult :=
  -- ACI derivation is the same regardless of polarity
  applyMCIs pair

theorem aci_polarity_insensitive (pair : CIAlternativePair) :
    aciInDEContext pair .upward = aciInDEContext pair .downward := rfl

/--
ACIs are cancellable.

Example (52): "Juan arrived first, then that bastard Pedro arrived
              (by the way, Juan is also a bastard)"

The parenthetical cancels the ACI.
-/
structure ACIWithCancellation where
  base : MCIsResult
  cancelled : Bool
  cancellationPhrase : Option String
  deriving Repr

def cancelACI (result : MCIsResult) (phrase : String) : ACIWithCancellation :=
  { base := result
  , cancelled := true
  , cancellationPhrase := some phrase }

/--
ACIs are reinforceable.

Example (63): Repeating the ACI content is not redundant.

"Juan arrived first, that bastard Pedro arrived second
 (by the way, Juan is not a bastard)"

The reinforcement is informative, not redundant (unlike presuppositions).
-/
def reinforceACI (result : MCIsResult) : MCIsResult :=
  -- Reinforcement doesn't change the ACI - it's still valid
  result


/--
Summary of how ACIs differ from their "scalar cousins".

| Property                    | SI  | Antipresup | ACI |
|-----------------------------|-----|------------|-----|
| Same assertive content req  | No  | Yes        | No  |
| Affected by DE context      | Yes | Varies     | No  |
| Cancellable                 | Yes | Yes        | Yes |
| Reinforceable               | Yes | No*        | Yes |
| Embeddable                  | Yes | Yes        | Yes |

* Reinforcing a presupposition is redundant
-/
structure ScalarInferenceComparison where
  inferenceType : String
  requiresSameAssertion : Bool
  affectedByDE : Bool
  cancellable : Bool
  reinforceable : Bool
  deriving Repr

def siProperties : ScalarInferenceComparison :=
  { inferenceType := "Scalar Implicature"
  , requiresSameAssertion := false
  , affectedByDE := true    -- DE blocks SIs
  , cancellable := true
  , reinforceable := true }

def antipresupProperties : ScalarInferenceComparison :=
  { inferenceType := "Antipresupposition"
  , requiresSameAssertion := true   -- MP! requires same assertion
  , affectedByDE := false           -- Varies by analysis
  , cancellable := true
  , reinforceable := false }        -- Redundant

def aciProperties : ScalarInferenceComparison :=
  { inferenceType := "Anti-Conventional Implicature"
  , requiresSameAssertion := false  -- CI independent of assertion
  , affectedByDE := false           -- CI doesn't interact with entailment
  , cancellable := true
  , reinforceable := true }


/--
The ACI mechanism is grounded in:
1. Potts (2005): CI content is independent of at-issue content
2. Fox & Katzir (2011): Formal alternatives are structurally constrained
3. Gricean reasoning: Cooperative speakers maximize informativeness

Given these, MCIs! derives ACIs compositionally: if the speaker used φ
when a CI-stronger formal alternative ψ was available and relevant, the
hearer infers the speaker believes the CI of ψ does not hold.
[sorry: need world-level formalization of speaker belief inference]
-/
theorem aci_grounded_in_mcis {W : Type*}
    (φ ψ : TwoDimProp W)
    (h_ci_stronger : ciStrongerThan ψ φ)  -- ψ has stronger CI
    (_h_relevant : ∃ w : W, ψ.ci w = true)  -- ψ's CI is non-trivial (contextually relevant)
    : -- Then ACI arises: there exists a world where φ's CI holds but ψ's does not.
      -- The speaker used φ (weaker) when ψ (stronger) was available, so the hearer
      -- infers ψ's additional CI content does not hold in some world.
      ∃ w : W, φ.ci w = true ∧ ψ.ci w = false :=
  h_ci_stronger.2

end NeoGricean.ConventionalImplicatures
