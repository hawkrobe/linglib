import Linglib.Theories.Semantics.Lexical.Expressives.Basic
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Theories.Semantics.Alternatives.Structural

/-!
# Anti-Conventional Implicatures (ACIs)

@cite{lo-guercio-2025}

Formalization of "Maximize Conventional Implicatures!" (S&P 18(9), 2025).

## Thesis

Scalar inferences can arise from comparing CI content, not just at-issue
or presuppositional content. These are Anti-Conventional Implicatures (ACIs).

The mechanism parallels:
- Scalar Implicatures: Compare at-issue content (Conversational Principle)
- Antipresuppositions: Compare presuppositional content (Maximize Presupposition)
- ACIs: Compare CI content (Maximize Conventional Implicatures)

All three are instances of `violatesMaximize` from `Structural.lean`,
applied to different content dimensions.

## The MCIs! Principle (Lo Guercio Definition 15)

Do not use φ if there's a formal alternative φ' ∈ F(φ) such that:
a. ⟦φ'⟧ᵘ ⊂ ⟦φ⟧ᵘ (CI-stronger)
b. φ' ∈ C (contextually relevant)
c. ¬⟦φ'⟧ᵘ doesn't contradict C given φ (innocently excludable)

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

## Architecture

MCIs! is `violatesMCIs` from `Structural.lean` — `violatesMaximize`
applied to CI content. This file provides:
- The CI content dimension types (`TwoDimProp`, `ciStrongerThan`)
- Property comparison structures
- Worked examples connecting structural alternatives to CI inference
-/

namespace Implicature.ConventionalImplicatures

open Semantics.Lexical.Expressives
open Semantics.Entailment.Polarity (ContextPolarity)
open StructuralAlternatives
open Core.Tree


-- ============================================================================
-- §1  MCIs! as an instance of violatesMaximize
-- ============================================================================

/--
MCIs! is the instantiation of the generic `violatesMaximize` principle
to CI content. This directly connects Lo Guercio's principle to the
Fox & Katzir structural alternatives framework.

Given:
- `lex`: the lexicon (substitution source)
- `ciContentFn`: maps each tree to its CI content
- `φ`: the sentence uttered

MCIs! says: φ violates the principle if there exists a structural
alternative φ' that is CI-stronger and weakly assertable.

See `violatesMCIs` in `Structural.lean` for the formal definition.
-/
example : @violatesMCIs = @violatesMaximize := rfl


-- ============================================================================
-- §2  Property comparison across scalar inference types
-- ============================================================================

/--
Summary of how ACIs differ from their "scalar cousins".

| Property                    | SI  | Antipresup | ACI |
|-----------------------------|-----|------------|-----|
| Same assertive content req  | No  | Yes        | No  |
| Affected by DE context      | Yes | Varies     | No  |
| Cancellable                 | Yes | Yes        | Yes |
| Reinforceable               | Yes | No*        | Yes |

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


-- ============================================================================
-- §3  ACIs are polarity-insensitive (derived)
-- ============================================================================

/--
ACIs are polarity-insensitive: the definition of `violatesMCIs` is
structurally independent of context polarity.

Unlike scalar implicatures (which compare at-issue entailment, reversed
in DE contexts), MCIs! compares CI content via `ciContentFn`, which
is a function of trees and worlds — not of truth-conditional entailment.
Therefore the same `violatesMCIs` applies regardless of whether the
embedding context is UE or DE.

"I doubt that Juan or that bastard Pedro passed"
- SI blocked (DE reverses entailment)
- ACI survives: ⇝ ¬(Juan is a bastard)

This is not a separate definition — it is a structural observation
about `violatesMCIs`: there is no polarity parameter in its type
signature, so polarity cannot affect it.
-/
theorem aci_polarity_insensitive {C W World : Type}
    (lex : List (Tree C W)) (ciContentFn : Tree C W → World → Bool)
    (φ : Tree C W) (weaklyAssertable : Tree C W → Bool)
    (_ctx1 _ctx2 : ContextPolarity) :
    -- The same violation holds regardless of polarity
    violatesMCIs lex ciContentFn φ weaklyAssertable =
    violatesMCIs lex ciContentFn φ weaklyAssertable := rfl


-- ============================================================================
-- §4  Worked example: epithet as structural alternative
-- ============================================================================

section EpithetExample

/-- Vocabulary for epithet examples. -/
inductive EWord where
  | john | pedro | arrived | first | then
  | that_ | bastard
  deriving DecidableEq, Repr

open Cat EWord

/-- Lexicon including "bastard" as a lexical item. -/
def epithetLex : List (Tree Cat EWord) :=
  [.terminal .N .john, .terminal .N .pedro,
   .terminal .V .arrived, .terminal .Adv .first,
   .terminal .Conj .then,
   .terminal .Det .that_, .terminal .N .bastard]

/-- φ = "[DP John] arrived first" — bare DP subject. -/
def johnArrived : Tree Cat EWord :=
  .node .S [.terminal .N .john,
            .node .VP [.terminal .V .arrived, .terminal .Adv .first]]

/-- φ' = "[DP that bastard John] arrived first" — epithet DP subject.

This tree is MORE complex than `johnArrived` because it replaces the
terminal N(john) with a node DP[Det(that), N(bastard), N(john)].

Out of the blue, this is NOT reachable from `johnArrived` by structural
operations, because constructing the DP node requires structure not in
the substitution source. Hence no ACI arises (matching Lo Guercio's
prediction for the out-of-the-blue case).
-/
def bastardJohnArrived : Tree Cat EWord :=
  .node .S [.node .DP [.terminal .Det .that_,
                       .terminal .N .bastard,
                       .terminal .N .john],
            .node .VP [.terminal .V .arrived, .terminal .Adv .first]]

/-- The epithet DP contains a DP category node. -/
theorem epithet_has_dp :
    bastardJohnArrived.containsCat .DP = true := by native_decide

/-- The bare sentence does NOT contain a DP category node. -/
theorem bare_lacks_dp :
    johnArrived.containsCat .DP = false := by native_decide

/-- The substitution source (out of the blue) lacks DP. -/
theorem source_lacks_dp :
    (substitutionSource epithetLex johnArrived).all
      (fun t => !t.containsCat .DP) = true := by native_decide

/-- Out of the blue, the epithet sentence is NOT a structural alternative.

Proof by `category_preservation`: no item in L(φ) has DP, φ has no DP,
so no reachable tree has DP. But the epithet sentence has DP. QED.

This formalizes Lo Guercio's prediction: out of the blue, "that bastard
John arrived first" is not a formal alternative to "John arrived first",
so no ACI arises.
-/
theorem epithet_not_alternative_outOfBlue :
    bastardJohnArrived ∉ structuralAlternatives epithetLex johnArrived := by
  intro h
  have h_preserved := category_preservation
    (substitutionSource epithetLex johnArrived) .DP
    johnArrived bastardJohnArrived
    (by intro s hs
        have := List.all_eq_true.mp source_lacks_dp s hs
        simp at this; exact this)
    (by native_decide)
    h
  exact absurd epithet_has_dp (by rw [h_preserved]; decide)

end EpithetExample


-- ============================================================================
-- §5  Grounding theorem: ACI from CI ordering
-- ============================================================================

/--
The ACI mechanism is grounded in:
1. @cite{potts-2005}: CI content is independent of at-issue content
2. @cite{fox-katzir-2011}: Formal alternatives are structurally constrained
3. Gricean reasoning: Cooperative speakers maximize informativeness

Given these, MCIs! derives ACIs compositionally: if the speaker used φ
when a CI-stronger formal alternative ψ was available and relevant, the
hearer infers the speaker believes the CI of ψ does not hold.
-/
theorem aci_grounded_in_mcis {W : Type*}
    (φ ψ : TwoDimProp W)
    (h_ci_stronger : ciStrongerThan ψ φ)  -- ψ has stronger CI
    : -- Then ACI arises: ∃ world where φ's CI holds but ψ's does not
      ∃ w : W, φ.ci w = true ∧ ψ.ci w = false :=
  h_ci_stronger.2

end Implicature.ConventionalImplicatures
