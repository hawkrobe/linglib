import Linglib.Theories.Pragmatics.Expressives.Basic
import Linglib.Theories.Pragmatics.Implicature.ConventionalImplicatures

/-!
# @cite{lo-guercio-2025} — Anti-Conventional Implicatures

Lo Guercio, N. (2025). Maximize Conventional Implicatures!
Semantics & Pragmatics, 18(9). https://doi.org/10.3765/sp.18.9

## Thesis

Scalar inferences can arise from comparing CI content, not just at-issue
or presuppositional content. These are Anti-Conventional Implicatures (ACIs).
Evidence comes from epithets, honorifics (*don/doña*), nominal appositives,
supplementary adverbs, and emotive markers.

## Empirical Data

This file contains judgment data on when ACIs arise. Theoretical analysis
(MCIs! principle, structural alternatives) is in
`Pragmatics.Implicature.ConventionalImplicatures`.
-/

namespace LoGuercio2025

open Implicature.ConventionalImplicatures (ScalarInferenceComparison
  siProperties antipresupProperties aciProperties)

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

end LoGuercio2025
