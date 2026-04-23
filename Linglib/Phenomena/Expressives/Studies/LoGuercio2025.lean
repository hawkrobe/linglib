import Linglib.Theories.Pragmatics.Expressives.Basic
import Linglib.Theories.Semantics.Alternatives.Structural
import Linglib.Theories.Semantics.Entailment.Polarity

/-!
# @cite{lo-guercio-2025} — Anti-Conventional Implicatures

Lo Guercio, N. (2025). Maximize Conventional Implicatures!
Semantics & Pragmatics, 18(9). https://doi.org/10.3765/sp.18.9

## Thesis

Scalar inferences can arise from comparing CI content, not just at-issue
or presuppositional content. These are Anti-Conventional Implicatures (ACIs).
Evidence comes from epithets, honorifics (*don/doña*), nominal appositives,
supplementary adverbs, and emotive markers.

The mechanism parallels:
- Scalar Implicatures: compare at-issue content (Conversational Principle)
- Antipresuppositions: compare presuppositional content (Maximize Presupposition)
- ACIs: compare CI content (Maximize Conventional Implicatures!)

All three are instances of `violatesMaximize` from
`Theories/Semantics/Alternatives/Structural.lean`, applied to different
content dimensions; `violatesMCIs` is the CI-content instantiation.

## The MCIs! Principle (@cite{lo-guercio-2025} def 15)

Do not use φ if there's a formal alternative φ' ∈ F(φ) such that:
a. ⟦φ'⟧ᵘ ⊂ ⟦φ⟧ᵘ (CI-stronger)
b. φ' ∈ C (contextually relevant)
c. ¬⟦φ'⟧ᵘ doesn't contradict C given φ (innocently excludable)

## Properties of ACIs (vs SIs and Antipresuppositions)

1. Don't require same assertive content (unlike antipresuppositions)
2. Not affected by DE contexts (unlike SIs)
3. Cancellable
4. Reinforceable
5. Pattern with CI expressions on embeddability

This file is self-contained: it bundles the theoretical analysis (property
comparison, polarity-insensitivity, structural-alternative epithet example,
grounding theorem) with the empirical judgment data.
-/

namespace Phenomena.Expressives.Studies.LoGuercio2025

open Pragmatics.Expressives
open Semantics.Entailment.Polarity (ContextPolarity)
open Alternatives.Structural
open Core.Tree

-- ============================================================================
-- Theoretical Analysis (was: Implicature/ConventionalImplicatures.lean)
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

/--
Judgment status for whether an ACI arises.
-/
inductive ACIJudgment where
  | arises          -- The ACI inference is drawn
  | doesNotArise    -- The ACI inference is not drawn
  | marginal        -- Speakers vary / uncertain
  deriving DecidableEq, Repr

/--
A single empirical item from the paper.
-/
structure EmpiricalItem where
  /-- Description of the example context -/
  description : String
  /-- The sentence tested -/
  sentence : String
  /-- The potential ACI content -/
  potentialACI : String
  /-- Whether the ACI arises empirically -/
  judgment : ACIJudgment
  /-- Prior context (if any) -/
  priorContext : Option String
  deriving Repr


-- ============================================================================
-- Epithets: out-of-the-blue vs with prior mention
-- ============================================================================

/--
Out of the blue, no epithet ACI arises.

"John arrived late."
⇝̸ ¬(John is a bastard)

The epithet alternative "that bastard John arrived late" is more complex
(requires NP structure not in the substitution source), so it is not a
formal alternative. MCIs! correctly predicts no ACI.
-/
def outOfBlue_epithet_noACI : EmpiricalItem :=
  { description := "Out-of-the-blue epithet (no prior mention)"
  , sentence := "John arrived late."
  , potentialACI := "Speaker doesn't think John is a bastard"
  , judgment := .doesNotArise
  , priorContext := none }

/--
With prior mention of epithet for another individual, ACI arises.

Context: "John arrived first, then that bastard Pedro arrived."
The bare "John" in the first clause triggers the ACI: ¬(John is a bastard).

Because "that bastard" is now contextually relevant (mentioned in the
second clause), it enters the substitution source for the first clause.
"That bastard John arrived first" is then a formal alternative of equal
complexity. MCIs! predicts the ACI.
-/
def priorMention_epithet_ACI : EmpiricalItem :=
  { description := "Epithet ACI with prior mention making alternative relevant"
  , sentence := "John arrived first, then that bastard Pedro arrived."
  , potentialACI := "Speaker doesn't think John is a bastard"
  , judgment := .arises
  , priorContext := none }

/--
Subconstituent context also licenses epithet ACI.

"Yesterday, John met with that bastard Pedro."
⇝ ¬(John is a bastard)

"That bastard" occurs as a subconstituent, making the epithet alternative
for John available as a formal alternative.
-/
def subconstituent_epithet_ACI : EmpiricalItem :=
  { description := "Epithet ACI via subconstituent availability"
  , sentence := "Yesterday, John met with that bastard Pedro."
  , potentialACI := "Speaker doesn't think John is a bastard"
  , judgment := .arises
  , priorContext := none }


-- ============================================================================
-- Spanish honorifics: don/doña
-- ============================================================================

/--
Out of the blue, no honorific ACI arises for Spanish *don/doña*.

"Diego entró." (Diego entered.)
⇝̸ ¬(speaker respects Diego)

Unlike Japanese ADTs, the mere absence of *don/doña* does not license
an ACI. Honorific alternatives are not systematically contextually
relevant in Spanish conversations.
-/
def outOfBlue_honorific_noACI : EmpiricalItem :=
  { description := "Spanish honorific out-of-the-blue (no ACI)"
  , sentence := "Diego entró."
  , potentialACI := "Speaker doesn't respect Diego"
  , judgment := .doesNotArise
  , priorContext := none }

/--
With contrastive honorification, ACI arises.

"Primero entró Donato. Después entró Don Pedro."
(First Donato entered. Then HON Pedro entered.)
⇝ ¬(speaker respects Donato)

Using *Don* for Pedro but not Donato triggers the ACI: the speaker
could have used the CI-stronger "Don Donato" but chose not to.
-/
def contrastive_honorific_ACI : EmpiricalItem :=
  { description := "Spanish honorific ACI via contrastive honorification"
  , sentence := "Primero entró Donato. Después entró Don Pedro."
  , potentialACI := "Speaker doesn't respect Donato (as much as Pedro)"
  , judgment := .arises
  , priorContext := none }

/--
Systematic licensing in Japanese vs contextual in Spanish.

Key cross-linguistic contrast: Japanese ADTs (*san*, *kun*, *chan*)
and polite forms (*desu/masu*) systematically license ACIs because
there is a default shared expectation that all referents and the
addressee be properly honorified. Omitting the ADT (*yobisute*)
systematically conveys closeness or disrespect.

In Spanish, *don/doña* only licenses ACIs when the honorific
alternative becomes contextually relevant due to concrete features
of the conversational context.
-/
def japanese_systematic_vs_spanish_contextual : Bool := true


-- ============================================================================
-- Nominal appositives
-- ============================================================================

/--
Out of the blue, no appositive ACI arises.

"Diego recommended an aspirin."
⇝̸ ¬(Diego is a doctor)
-/
def outOfBlue_appositive_noACI : EmpiricalItem :=
  { description := "Appositive: no ACI out of the blue"
  , sentence := "Diego recommended an aspirin."
  , potentialACI := "Diego is not a doctor"
  , judgment := .doesNotArise
  , priorContext := none }

/--
With prior appositive mention, ACI arises.

"Diego recommended an aspirin. Laura, a doctor, recommended an antibiotic."
⇝ ¬(Diego is a doctor)
-/
def priorMention_appositive_ACI : EmpiricalItem :=
  { description := "Appositive ACI via prior mention of appositive"
  , sentence := "Diego recommended an aspirin."
  , potentialACI := "Diego is not a doctor"
  , judgment := .arises
  , priorContext := some "Laura, a doctor, recommended an antibiotic." }


-- ============================================================================
-- Supplementary adverbs and emotive markers
-- ============================================================================

/--
Out of the blue, no supplementary adverb ACI.

"Juan signed up for the tournament."
⇝̸ ¬luckily/amazingly(Juan signed up)
-/
def outOfBlue_suppAdverb_noACI : EmpiricalItem :=
  { description := "Supplementary adverb: no ACI out of the blue"
  , sentence := "Juan signed up for the tournament."
  , potentialACI := "It is not lucky/amazing that Juan signed up"
  , judgment := .doesNotArise
  , priorContext := none }

/--
With prior use, supplementary adverb ACI arises.

"Juan signed up for the tournament and luckily/amazingly, Pedro
signed up for the tournament."
⇝ ¬luckily/amazingly(Juan signed up for the tournament)
-/
def priorMention_suppAdverb_ACI : EmpiricalItem :=
  { description := "Supplementary adverb ACI via prior mention"
  , sentence := "Juan signed up for the tournament."
  , potentialACI := "It is not lucky/amazing that Juan signed up"
  , judgment := .arises
  , priorContext := some "...and luckily/amazingly, Pedro signed up." }

/--
Emotive markers: same pattern.

"Juan signed up for the tournament, and Alas/Wow!, Pedro signed up too."
⇝ ¬(speaker is disappointed/surprised about Juan signing up)
-/
def priorMention_emotiveMarker_ACI : EmpiricalItem :=
  { description := "Emotive marker ACI via prior mention"
  , sentence := "Juan signed up for the tournament."
  , potentialACI := "Speaker is not disappointed/surprised about Juan signing up"
  , judgment := .arises
  , priorContext := some "...and Alas/Wow!, Pedro signed up too." }


-- ============================================================================
-- Properties of ACIs (comparison with SIs and antipresuppositions)
-- ============================================================================

/--
Property test: ACIs do not require same assertive content.

"Juan called María or that bastard Pedro."
⇝ ¬(María is a bastard)

The CI-stronger alternative "Juan called María and that bastard Pedro"
has different assertive content (conjunction vs disjunction), yet the
ACI still arises. This distinguishes ACIs from antipresuppositions,
which require same assertive content.
-/
def aciIndependentOfAssertion : Bool := true

/--
Property test: ACIs not affected by DE contexts.

"I doubt that Juan or that bastard Pedro passed the exam."
- SI blocked (DE reverses entailment: no implicature ¬(both passed))
- ACI not blocked: ⇝ ¬(Juan is a bastard)

CI content is independent of truth-conditional entailment, so DE
environments have no effect on ACIs.
-/
def aciUnaffectedByDE : Bool := true

/--
Property test: ACIs are cancellable.

"Juan arrived first. Then that bastard Pedro arrived.
 (By the way, Juan is also a bastard.)"

The parenthetical cancels the ACI. This parallels scalar implicature
cancellation and distinguishes ACIs from presuppositions (which
are redundant when reinforced).
-/
def aciCancellable : Bool := true

/--
Property test: ACIs are reinforceable.

"Juan arrived first. That bastard Pedro arrived second.
 (By the way, Juan is not a bastard.)"

The reinforcement is informative, not redundant. This contrasts
with presupposition reinforcement, which sounds redundant.
-/
def aciReinforceable : Bool := true


-- ============================================================================
-- Verification: comparison table matches theory-layer definitions
-- ============================================================================

/-- Scalar implicatures are affected by DE contexts. -/
theorem si_affected_by_de : siProperties.affectedByDE = true := rfl

/-- Antipresuppositions require same assertive content. -/
theorem antipresup_requires_same_assertion :
    antipresupProperties.requiresSameAssertion = true := rfl

/-- ACIs do not require same assertive content. -/
theorem aci_no_same_assertion :
    aciProperties.requiresSameAssertion = false := rfl

/-- ACIs are not affected by DE contexts. -/
theorem aci_not_affected_by_de : aciProperties.affectedByDE = false := rfl

/-- ACIs are reinforceable (unlike presuppositions). -/
theorem aci_reinforceable : aciProperties.reinforceable = true := rfl


-- ============================================================================
-- Register blocking
-- ============================================================================

/--
Register differences block ACIs even when one alternative is CI-stronger.

"That bastard John is late."
⇝̸ ¬(John is a motherfucker)

Even though *motherfucker* is CI-stronger than *bastard* (both are
lexical items, hence both in the substitution source), the ACI
does not arise because the two expressions differ in register —
*motherfucker* is coarser than *bastard*.

Scalar reasoning requires alternatives to be "in the same dialect
or register" (@cite{levinson-2000}). Register mismatch provides the hearer
with an alternative explanation for why the speaker didn't use the
stronger form: not that the speaker doesn't believe the CI content,
but that the alternative was inappropriate due to register.
-/
def registerBlocking_noACI : EmpiricalItem :=
  { description := "Register blocking: bastard vs motherfucker"
  , sentence := "That bastard John is late."
  , potentialACI := "John is not a motherfucker"
  , judgment := .doesNotArise
  , priorContext := none }

-- ============================================================================
-- Expressive adjectives and argument extension (§3.2.4)
-- ============================================================================

/--
Argument extension patterns for expressive adjectives (§3.2.4).

EAs behave erratically regarding ACIs because they can scope over
different constituents (@cite{potts-2005}, @cite{gutzmann-2019},
@cite{frazier-dillon-clifton-2015}). Lo Guercio notes that
this makes "the identification of potential ACIs very complicated"
and confines himself to "merely presenting the problem and pointing
to a plausible line of analysis."

Three competing accounts:
1. @cite{potts-2005}: semantic polymorphism (EA is type-flexible)
2. @cite{gutzmann-2019}: syntactic *iEx* feature (Agree-based)
3. @cite{lo-guercio-orlando-2022}: isolated CIs (late merge at PF)

The third account is most promising for ACIs: if EAs are late-merged
at PF, they are invisible at LF and thus not formal alternatives
in the relevant sense, predicting no ACI computation for EAs.
-/
inductive ArgExtensionPattern where
  /-- EA targets its syntactic sister -/
  | local
  /-- EA targets a higher constituent (e.g., whole VP or S) -/
  | argumentLowering
  /-- EA inside DP targets a non-local argument -/
  | argumentHopping
  deriving DecidableEq, Repr

-- ============================================================================
-- §2  ACIs are polarity-insensitive (derived)
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
    (src : Alternatives.AlternativeSource (Tree C W))
    (ciContentFn : Tree C W → World → Bool)
    (φ : Tree C W) (weaklyAssertable : Tree C W → Bool)
    (_ctx1 _ctx2 : ContextPolarity) :
    -- The same violation holds regardless of polarity
    violatesMCIs src ciContentFn φ weaklyAssertable =
    violatesMCIs src ciContentFn φ weaklyAssertable := rfl


-- ============================================================================
-- §3  Worked example: epithet as structural alternative
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
the substitution source. Hence no ACI arises (matching @cite{lo-guercio-2025}'s
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

This formalizes @cite{lo-guercio-2025}'s prediction: out of the blue,
"that bastard John arrived first" is not a formal alternative to
"John arrived first", so no ACI arises.
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
-- §4  Grounding theorem: ACI from CI ordering
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
      ∃ w : W, φ.ci w ∧ ¬ψ.ci w :=
  h_ci_stronger.2

end Phenomena.Expressives.Studies.LoGuercio2025
