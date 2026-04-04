import Linglib.Theories.Semantics.Dynamic.IntensionalCDRT.Update

/-!
# Hofmann (2025): Anaphoric Accessibility with Flat Update

@cite{hofmann-2025}

Formalizes the core empirical and theoretical contributions of
@cite{hofmann-2025}'s unified account of anaphoric accessibility.

## Core Claim

Anaphoric accessibility is governed by **veridicality** — speaker
commitments about discourse referents — not by structural scope.
Indefinites under nonveridical operators introduce drefs globally
(flat update), and constraints on anaphora emerge from two principles:

1. **Local contextual entailment**: a dref's referent must exist
   throughout the pronoun's local context.
2. **Discourse consistency**: the speaker's commitment set must remain
   non-empty after the update.

## Phenomena Unified

The paper provides a single analysis for four previously disparate
patterns of anaphora to negated antecedents:

- **Double negation** (@cite{krahmer-muskens-1995}): "It's not the case
  that there isn't a bathroom. It's upstairs."
- **Bathroom disjunctions** (@cite{roberts-1989}): "Either there isn't
  a bathroom, or it's upstairs."
- **Disagreement** (@cite{hofmann-2019}): A: "There isn't a bathroom."
  B: "It's upstairs."
- **Modal subordination** (@cite{frank-1996}, @cite{roberts-1989}):
  "There isn't a bathroom. It would be upstairs."

## Theoretical Framework

The analysis is implemented in Intensional CDRT (ICDRT), extending
@cite{muskens-1996}'s Compositional DRT with intensionality and
propositional drefs, following @cite{stone-1999} and
@cite{brasoveanu-2006}'s flat-update approach.
-/

namespace Phenomena.Anaphora.Studies.Hofmann2025

-- ════════════════════════════════════════════════════════════════
-- § 1. Empirical Data
-- ════════════════════════════════════════════════════════════════

/-! ## Veridicality and anaphoric accessibility

@cite{hofmann-2025} classifies drefs along a veridicality dimension
that determines accessibility:
- **Veridical**: the speaker commits to the referent's existence.
- **Hypothetical**: the speaker is not committed, but the referent
  may exist in considered possibilities.
- **Counterfactual**: the speaker is committed to the referent's
  non-existence (in the actual world).

Anaphora is possible when:
- Veridical antecedent + veridical anaphor context (standard case)
- Hypothetical/counterfactual antecedent + nonveridical anaphor context
  (bathroom disjunctions, modal subordination, disagreement)
- Doubly negated antecedent (= veridical, by complementation)

Anaphora fails when:
- Counterfactual antecedent + veridical anaphor context (standard
  negation blocking: "There isn't a bathroom. #It's upstairs.")
-/

/-- Epistemic status of a discourse referent relative to a speaker. -/
inductive DrefStatus where
  /-- Speaker commits to existence -/
  | veridical
  /-- Speaker not committed; referent exists in some possibilities -/
  | hypothetical
  /-- Speaker commits to non-existence -/
  | counterfactual
  deriving DecidableEq, Repr

/-- Veridicality of the anaphor's embedding context. -/
inductive AnaphorContext where
  /-- Veridical assertion -/
  | veridical
  /-- Nonveridical: modal, attitude, disjunct, disagreement -/
  | nonveridical
  deriving DecidableEq, Repr

/--
Accessibility prediction: a dref of the given status is accessible
in the given anaphor context.

@cite{hofmann-2025} §1.2.2, generalization (7):
A pronoun can be interpreted anaphorically if
  (a) its semantic value is provided by an overt antecedent, and
  (b) the presupposition that its referent exists is met in its
      local context (under some consistent interpretation).
-/
def accessible (status : DrefStatus) (ctx : AnaphorContext) : Bool :=
  match status, ctx with
  | .veridical,      _              => true   -- exists in all DC worlds
  | .hypothetical,    .nonveridical  => true   -- exists locally
  | .counterfactual,  .nonveridical  => true   -- exists locally (§4.3, §4.4)
  | .hypothetical,    .veridical     => false  -- might not exist globally
  | .counterfactual,  .veridical     => false  -- doesn't exist globally

/-- An empirical datum on anaphoric accessibility. -/
structure AccessDatum where
  /-- Brief label -/
  label : String
  /-- The antecedent sentence (introducing the dref) -/
  antecedentSentence : String
  /-- The anaphor sentence -/
  anaphorSentence : String
  /-- Epistemic status of the antecedent dref -/
  antecedentStatus : DrefStatus
  /-- Veridicality of the anaphor's context -/
  anaphorCtx : AnaphorContext
  /-- Felicity judgment -/
  felicitous : Bool
  /-- Source -/
  source : String
  deriving Repr

-- ────────────────────────────────────────────────────────────────
-- § 1.1 Basic contrast: veridical vs. negated antecedent
-- ────────────────────────────────────────────────────────────────

/-- (1a): "Mary owns a car. It is red." @cite{hofmann-2025} -/
def veridicalBasic : AccessDatum := {
  label := "veridical-basic"
  antecedentSentence := "Mary owns a car."
  anaphorSentence := "It is red."
  antecedentStatus := .veridical
  anaphorCtx := .veridical
  felicitous := true
  source := "Hofmann 2025: (1a)"
}

/-- (1b): "Mary doesn't own a car. #It is red." @cite{hofmann-2025} -/
def negatedBasic : AccessDatum := {
  label := "negated-basic"
  antecedentSentence := "Mary doesn't own a car."
  anaphorSentence := "#It is red."
  antecedentStatus := .counterfactual
  anaphorCtx := .veridical
  felicitous := false
  source := "Hofmann 2025: (1b)"
}

-- ────────────────────────────────────────────────────────────────
-- § 1.2 Four counterexamples to nested update
-- ────────────────────────────────────────────────────────────────

/-- (2a)/(42a): Double negation. @cite{krahmer-muskens-1995} -/
def doubleNegation : AccessDatum := {
  label := "double-negation"
  antecedentSentence := "It's not true that there isn't a bathroom."
  anaphorSentence := "It is upstairs."
  antecedentStatus := .veridical  -- ¬¬∃ = veridical
  anaphorCtx := .veridical
  felicitous := true
  source := "Krahmer & Muskens 1995: (5)"
}

/-- (2b)/(42b): Bathroom disjunction. @cite{roberts-1989} -/
def bathroomDisjunction : AccessDatum := {
  label := "bathroom-disjunction"
  antecedentSentence := "Either there isn't a bathroom in this house"
  anaphorSentence := "or it's in a funny place."
  antecedentStatus := .counterfactual
  anaphorCtx := .nonveridical  -- second disjunct is nonveridical
  felicitous := true
  source := "Roberts 1989: (12)"
}

/-- (2c)/(42c): Disagreement. @cite{hofmann-2019} -/
def disagreement : AccessDatum := {
  label := "disagreement"
  antecedentSentence := "A: There isn't a bathroom in this house."
  anaphorSentence := "B: (What are you talking about?) It is just in a weird place."
  antecedentStatus := .counterfactual  -- for speaker A
  anaphorCtx := .nonveridical  -- B's assertion contradicts A's
  felicitous := true
  source := "Hofmann 2019: (2d)"
}

/-- (2d)/(42d): Modal subordination. @cite{frank-1996} -/
def modalSubordination : AccessDatum := {
  label := "modal-subordination"
  antecedentSentence := "Fred didn't buy a microwave oven."
  anaphorSentence := "He wouldn't know what to do with it."
  antecedentStatus := .counterfactual
  anaphorCtx := .nonveridical  -- 'would' is nonveridical
  felicitous := true
  source := "Frank 1996: (8a)"
}

-- ────────────────────────────────────────────────────────────────
-- § 1.3 Veridical under negation (factives, negative implicatives)
-- ────────────────────────────────────────────────────────────────

/-- (5a): Negated factive. @cite{karttunen-1976} -/
def negatedFactive : AccessDatum := {
  label := "negated-factive"
  antecedentSentence := "Bill didn't realize that he had a dime."
  anaphorSentence := "It was in his pocket."
  antecedentStatus := .veridical  -- factive: dime exists
  anaphorCtx := .veridical
  felicitous := true
  source := "Karttunen 1976: (16)"
}

/-- (5b): Negative implicative. @cite{karttunen-1976} -/
def negativeImplicative : AccessDatum := {
  label := "negative-implicative"
  antecedentSentence := "John forgot not to bring an umbrella."
  anaphorSentence := "...but we had no room for it."
  antecedentStatus := .veridical  -- 'forgot not to' entails existence
  anaphorCtx := .veridical
  felicitous := true
  source := "Karttunen 1976: (14b)"
}

-- ────────────────────────────────────────────────────────────────
-- § 1.4 Look-ahead: anaphor context matters
-- ────────────────────────────────────────────────────────────────

/-- (6a): Counterfactual antecedent + veridical anaphor → fails. -/
def counterfactualVeridical : AccessDatum := {
  label := "counterfactual-veridical"
  antecedentSentence := "Mary doesn't own a car."
  anaphorSentence := "#It is parked outside."
  antecedentStatus := .counterfactual
  anaphorCtx := .veridical
  felicitous := false
  source := "Hofmann 2025: (6a)"
}

/-- (6b): Same antecedent + nonveridical anaphor → succeeds. -/
def counterfactualModal : AccessDatum := {
  label := "counterfactual-modal"
  antecedentSentence := "Mary doesn't own a car."
  anaphorSentence := "It would be parked outside."
  antecedentStatus := .counterfactual
  anaphorCtx := .nonveridical
  felicitous := true
  source := "Hofmann 2025: (6b)"
}

/-- (6c): Counterfactual antecedent + concessive → succeeds. -/
def counterfactualConcessive : AccessDatum := {
  label := "counterfactual-concessive"
  antecedentSentence := "Mary doesn't own a car."
  anaphorSentence := "...even though Cole said that it's red."
  antecedentStatus := .counterfactual
  anaphorCtx := .nonveridical  -- 'said' is nonveridical for speaker
  felicitous := true
  source := "Hofmann 2025: (6c)"
}

-- ────────────────────────────────────────────────────────────────
-- § 1.5 Modal subordination variants
-- ────────────────────────────────────────────────────────────────

/-- (8)/(11): Wolf might walk in — indicative anaphor fails.
    @cite{roberts-1989} -/
def wolfIndicative : AccessDatum := {
  label := "wolf-indicative"
  antecedentSentence := "A wolf might walk in."
  anaphorSentence := "#It is gray."
  antecedentStatus := .hypothetical
  anaphorCtx := .veridical
  felicitous := false
  source := "Roberts 1989: (11)"
}

/-- (8b): Wolf might walk in — 'would' anaphor succeeds.
    @cite{roberts-1989} -/
def wolfWould : AccessDatum := {
  label := "wolf-would"
  antecedentSentence := "A wolf might walk in."
  anaphorSentence := "It would eat you first."
  antecedentStatus := .hypothetical
  anaphorCtx := .nonveridical
  felicitous := true
  source := "Roberts 1989: (11)"
}

-- ────────────────────────────────────────────────────────────────
-- § 1.6 Infelicitous contrasts
-- ────────────────────────────────────────────────────────────────

/-- Negation blocks veridical anaphora across sentence boundary.
    This is the basic observation motivating all dynamic accounts.
    @cite{karttunen-1976} -/
def negationBlocks : AccessDatum := {
  label := "negation-blocks"
  antecedentSentence := "There isn't a bathroom."
  anaphorSentence := "#It is upstairs."
  antecedentStatus := .counterfactual
  anaphorCtx := .veridical
  felicitous := false
  source := "Karttunen 1976"
}

/-- Conjunction with negated antecedent is infelicitous (same speaker,
    veridical context). -/
def conjunctionBlocks : AccessDatum := {
  label := "conjunction-blocks"
  antecedentSentence := "There's no bathroom"
  anaphorSentence := "and it's upstairs."
  antecedentStatus := .counterfactual
  anaphorCtx := .veridical  -- conjunction = both veridical
  felicitous := false
  source := "Contrast case"
}

-- ════════════════════════════════════════════════════════════════
-- § 2. Per-datum Verification
-- ════════════════════════════════════════════════════════════════

/-! Each datum's felicity judgment should match the `accessible` prediction. -/

theorem veridicalBasic_correct :
    accessible veridicalBasic.antecedentStatus veridicalBasic.anaphorCtx
    = veridicalBasic.felicitous := rfl

theorem negatedBasic_correct :
    accessible negatedBasic.antecedentStatus negatedBasic.anaphorCtx
    = negatedBasic.felicitous := rfl

theorem doubleNegation_correct :
    accessible doubleNegation.antecedentStatus doubleNegation.anaphorCtx
    = doubleNegation.felicitous := rfl

theorem bathroomDisjunction_correct :
    accessible bathroomDisjunction.antecedentStatus bathroomDisjunction.anaphorCtx
    = bathroomDisjunction.felicitous := rfl

theorem disagreement_correct :
    accessible disagreement.antecedentStatus disagreement.anaphorCtx
    = disagreement.felicitous := rfl

theorem modalSubordination_correct :
    accessible modalSubordination.antecedentStatus modalSubordination.anaphorCtx
    = modalSubordination.felicitous := rfl

theorem negatedFactive_correct :
    accessible negatedFactive.antecedentStatus negatedFactive.anaphorCtx
    = negatedFactive.felicitous := rfl

theorem negativeImplicative_correct :
    accessible negativeImplicative.antecedentStatus negativeImplicative.anaphorCtx
    = negativeImplicative.felicitous := rfl

theorem counterfactualVeridical_correct :
    accessible counterfactualVeridical.antecedentStatus counterfactualVeridical.anaphorCtx
    = counterfactualVeridical.felicitous := rfl

theorem counterfactualModal_correct :
    accessible counterfactualModal.antecedentStatus counterfactualModal.anaphorCtx
    = counterfactualModal.felicitous := rfl

theorem counterfactualConcessive_correct :
    accessible counterfactualConcessive.antecedentStatus counterfactualConcessive.anaphorCtx
    = counterfactualConcessive.felicitous := rfl

theorem wolfIndicative_correct :
    accessible wolfIndicative.antecedentStatus wolfIndicative.anaphorCtx
    = wolfIndicative.felicitous := rfl

theorem wolfWould_correct :
    accessible wolfWould.antecedentStatus wolfWould.anaphorCtx
    = wolfWould.felicitous := rfl

theorem negationBlocks_correct :
    accessible negationBlocks.antecedentStatus negationBlocks.anaphorCtx
    = negationBlocks.felicitous := rfl

theorem conjunctionBlocks_correct :
    accessible conjunctionBlocks.antecedentStatus conjunctionBlocks.anaphorCtx
    = conjunctionBlocks.felicitous := rfl

/-- All 15 data points match the accessibility prediction. -/
theorem all_data_correct :
    accessible veridicalBasic.antecedentStatus veridicalBasic.anaphorCtx = veridicalBasic.felicitous ∧
    accessible negatedBasic.antecedentStatus negatedBasic.anaphorCtx = negatedBasic.felicitous ∧
    accessible doubleNegation.antecedentStatus doubleNegation.anaphorCtx = doubleNegation.felicitous ∧
    accessible bathroomDisjunction.antecedentStatus bathroomDisjunction.anaphorCtx = bathroomDisjunction.felicitous ∧
    accessible disagreement.antecedentStatus disagreement.anaphorCtx = disagreement.felicitous ∧
    accessible modalSubordination.antecedentStatus modalSubordination.anaphorCtx = modalSubordination.felicitous ∧
    accessible negatedFactive.antecedentStatus negatedFactive.anaphorCtx = negatedFactive.felicitous ∧
    accessible negativeImplicative.antecedentStatus negativeImplicative.anaphorCtx = negativeImplicative.felicitous ∧
    accessible counterfactualVeridical.antecedentStatus counterfactualVeridical.anaphorCtx = counterfactualVeridical.felicitous ∧
    accessible counterfactualModal.antecedentStatus counterfactualModal.anaphorCtx = counterfactualModal.felicitous ∧
    accessible counterfactualConcessive.antecedentStatus counterfactualConcessive.anaphorCtx = counterfactualConcessive.felicitous ∧
    accessible wolfIndicative.antecedentStatus wolfIndicative.anaphorCtx = wolfIndicative.felicitous ∧
    accessible wolfWould.antecedentStatus wolfWould.anaphorCtx = wolfWould.felicitous ∧
    accessible negationBlocks.antecedentStatus negationBlocks.anaphorCtx = negationBlocks.felicitous ∧
    accessible conjunctionBlocks.antecedentStatus conjunctionBlocks.anaphorCtx = conjunctionBlocks.felicitous :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


end Phenomena.Anaphora.Studies.Hofmann2025
