import Linglib.Theories.Montague.Question.ProbabilisticAnswerhood
import Linglib.Theories.Montague.Question.Basic

/-!
# Additive Particles: too, also, either

Felicity conditions for additive particles following Thomas (2026)
"A probabilistic, question-based approach to additivity".

## Key Insight: Argument-Building Use

The novel contribution of Thomas (2026) is explaining the "argument-building"
use of "too" where the antecedent and prejacent aren't focus alternatives
but jointly build an argument for some conclusion.

Example: "Sue cooks, and she has a lot of free time, too."
- Not asserting "Sue cooks" AND "has free time" as focus alternatives
- Both contribute toward conclusion: "Sue should host the dinner party"

## Definition 64: Felicity Conditions for TOO(π)

Given resolved question RQ and antecedent ANT:
1. **Antecedent Condition**: ANT probabilistically answers RQ
2. **Conjunction Condition**: ANT ∧ ⟦π⟧ evidences some resolution A more
   strongly than ANT alone
3. **Prejacent Conditions**:
   - ⟦π⟧ doesn't entail the evidenced resolution
   - No weaker proposition works as well

## Standard vs Argument-Building Uses

**Standard use**: ANT and π are focus alternatives
- "John came. Mary came too."
- ANT = "John came", π = "Mary came", RQ = "Who came?"

**Argument-building use**: ANT and π jointly support a conclusion
- "Sue cooks, and she has free time, too."
- ANT = "Sue cooks", π = "Sue has free time"
- RQ = "Who should host?" (implicit)
- Together they evidence "Sue should host"

## References

- Thomas (2026). A probabilistic, question-based approach to additivity.
- Kripke (2009). Presupposition and Anaphora: Remarks on the Formulation of
  the Projection Problem.
- Heim (1992). Presupposition Projection and the Semantics of Attitude Verbs.
-/

namespace Montague.Particle.Additive

open Montague.Question
open Montague.Question.Inquisitive
open Montague.Question.ProbabilisticAnswerhood

-- Additive Particle Types

/-- Types of additive particles. -/
inductive AdditiveParticle where
  | too    -- positive polarity, typically sentence-final
  | also   -- positive polarity, typically medial position
  | either -- negative polarity
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Polarity requirement for additive particles.

"too" and "also" require positive polarity contexts.
"either" requires negative polarity contexts. -/
def AdditiveParticle.requiresPositive : AdditiveParticle → Bool
  | .too => true
  | .also => true
  | .either => false

/-- Check if particle is licensed in a given polarity context. -/
def AdditiveParticle.isLicensed (p : AdditiveParticle) (positive : Bool) : Bool :=
  p.requiresPositive == positive

-- Discourse Context for Additive Particles

/-- Discourse context for evaluating additive particle felicity.

Thomas (2026) requires:
- A resolved question (RQ) in the discourse
- An antecedent proposition (ANT) that answers RQ
- A prior probability distribution -/
structure AdditiveContext (W : Type*) [Fintype W] where
  /-- The resolved question (RQ) -/
  resolvedQuestion : Issue W
  /-- The antecedent proposition (ANT) - what was just established -/
  antecedent : W → Bool
  /-- Prior probability distribution over worlds -/
  prior : ExactDist W
  /-- The actual world (for truth evaluation) -/
  actualWorld : Option W := none

namespace AdditiveContext

variable {W : Type*} [Fintype W]

/-- Create a context from a polar question. -/
def fromPolar (p : W → Bool) (ant : W → Bool) (prior : ExactDist W) :
    AdditiveContext W :=
  { resolvedQuestion := Issue.polar p
  , antecedent := ant
  , prior := prior }

/-- Create a context from a list of alternatives. -/
def fromAlternatives (alts : List (InfoState W)) (ant : W → Bool)
    (prior : ExactDist W) : AdditiveContext W :=
  { resolvedQuestion := Issue.ofAlternatives alts
  , antecedent := ant
  , prior := prior }

end AdditiveContext

-- Felicity Conditions (Definition 64)

/-- Condition 1: Antecedent probabilistically answers RQ.

The antecedent must raise the probability of some resolution. -/
def antecedentCondition {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) : Bool :=
  probAnswers ctx.antecedent ctx.resolvedQuestion ctx.prior

/-- Condition 2: Conjunction evidences more strongly.

ANT ∧ π must evidence some resolution A more strongly than ANT alone. -/
def conjunctionCondition {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) : Bool :=
  someResolutionStrengthened ctx.antecedent prejacent ctx.resolvedQuestion ctx.prior

/-- Get the resolution(s) that are strengthened by the conjunction. -/
def strengthenedResolutions' {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) : List (InfoState W) :=
  strengthenedResolutions ctx.antecedent prejacent ctx.resolvedQuestion ctx.prior

/-- Condition 3a: Prejacent doesn't entail the evidenced resolution.

π shouldn't make the conclusion trivially certain.
Uses a provided world list for computability. -/
def nonTrivialityConditionWith {W : Type*}
    (prejacent : W → Bool) (strengthened : List (InfoState W))
    (worlds : List W) : Bool :=
  strengthened.any fun alt =>
    -- π doesn't entail alt (there's a π-world that's not in alt)
    !(worlds.all fun w => prejacent w → alt w)

/-- Condition 3b: No weaker proposition works as well.

This is a maximality condition: π should be minimal in some sense.
We approximate this by checking that π is informative. -/
def maximalityCondition {W : Type*} [Fintype W]
    (prejacent : W → Bool) (prior : ExactDist W) : Bool :=
  -- π should have positive probability (informative)
  probOfProp prior prejacent > 0 &&
  -- π shouldn't be a tautology
  probOfProp prior prejacent < 1

/-- Full felicity conditions for TOO(π) with explicit world list.

Definition 64 from Thomas (2026). -/
def tooFelicitousWith {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool)
    (worlds : List W) : Bool :=
  -- Condition 1: ANT probabilistically answers RQ
  antecedentCondition ctx &&
  -- Condition 2: ANT ∧ π evidences some resolution more strongly than ANT alone
  conjunctionCondition ctx prejacent &&
  -- Condition 3a: π doesn't entail the strengthened resolution
  nonTrivialityConditionWith prejacent (strengthenedResolutions' ctx prejacent) worlds &&
  -- Condition 3b: Maximality (π is properly informative)
  maximalityCondition prejacent ctx.prior

/-- Noncomputable version using Fintype.elems. -/
noncomputable def tooFelicitous {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) : Bool :=
  tooFelicitousWith ctx prejacent Fintype.elems.toList

/-- Felicity for "also" - same conditions as "too". -/
noncomputable def alsoFelicitous {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) : Bool :=
  tooFelicitous ctx prejacent

/-- Felicity for "either" - requires negative polarity context.

For now, we use the same core conditions as "too", but in actual use
"either" appears in negative contexts. -/
noncomputable def eitherFelicitous {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool)
    (inNegativeContext : Bool) : Bool :=
  inNegativeContext && tooFelicitous ctx prejacent

-- Additive Utterances

/-- An utterance with an additive particle. -/
structure AdditiveUtterance (W : Type*) where
  /-- The additive particle used -/
  particle : AdditiveParticle
  /-- The prejacent (main content) -/
  prejacent : W → Bool
  /-- Optional: the focused element (for focus-based analyses) -/
  focus : Option (W → Bool) := none

namespace AdditiveUtterance

variable {W : Type*} [Fintype W]

/-- Check if the utterance is felicitous in the given context. -/
noncomputable def isFelicitous (utt : AdditiveUtterance W) (ctx : AdditiveContext W)
    (polarityPositive : Bool := true) : Bool :=
  match utt.particle with
  | .too => polarityPositive && tooFelicitous ctx utt.prejacent
  | .also => polarityPositive && alsoFelicitous ctx utt.prejacent
  | .either => eitherFelicitous ctx utt.prejacent (!polarityPositive)

/-- The asserted content of the utterance (just the prejacent). -/
def assertedContent (utt : AdditiveUtterance W) : W → Bool :=
  utt.prejacent

/-- The presupposed content: that the antecedent is established. -/
def presupposedContent (_utt : AdditiveUtterance W) (ctx : AdditiveContext W) :
    W → Bool :=
  ctx.antecedent

end AdditiveUtterance

-- Use Type Classification

/-- Types of additive particle uses. -/
inductive AdditiveUseType where
  | standard        -- ANT and π are focus alternatives
  | argumentBuilding -- ANT and π jointly support a conclusion
  | scalar          -- π is scalar alternative to ANT
  deriving DecidableEq, Repr, BEq

/-- Check if ANT and π could be focus alternatives (with explicit world list).

In standard use, the antecedent and prejacent are typically:
1. About different entities with the same property, OR
2. About the same entity with different properties (focus alternatives) -/
def isFocusAlternativeUseWith {W : Type*}
    (ant prejacent : W → Bool) (rq : Issue W) (worlds : List W) : Bool :=
  -- Both ANT and π should be (non-trivial) partial answers to RQ
  rq.alternatives.any (fun alt => worlds.any fun w => ant w && alt w) &&
  rq.alternatives.any (fun alt => worlds.any fun w => prejacent w && alt w)

/-- Noncomputable version using Fintype. -/
noncomputable def isFocusAlternativeUse {W : Type*} [Fintype W]
    (ant prejacent : W → Bool) (rq : Issue W) : Bool :=
  isFocusAlternativeUseWith ant prejacent rq Fintype.elems.toList

/-- Check if this is an argument-building use.

In argument-building use:
1. ANT and π are NOT focus alternatives
2. Together they provide cumulative evidence for some conclusion -/
noncomputable def isArgumentBuildingUse {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) : Bool :=
  -- Not standard focus alternatives
  !isFocusAlternativeUse ctx.antecedent prejacent ctx.resolvedQuestion &&
  -- But conjunction still strengthens evidence
  conjunctionCondition ctx prejacent

/-- Classify the use type of an additive particle. -/
noncomputable def classifyUse {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) : AdditiveUseType :=
  if isFocusAlternativeUse ctx.antecedent prejacent ctx.resolvedQuestion then
    .standard
  else if isArgumentBuildingUse ctx prejacent then
    .argumentBuilding
  else
    .scalar

-- Core Theoretical Results (Thomas 2026)

/-!
## Central Theorems

These theorems capture the key linguistic insights of Thomas (2026):

1. **Standard Use Reduction**: When π directly determines an alternative of RQ,
   the probabilistic felicity conditions reduce to the traditional analysis.

2. **Argument-Building Characterization**: Argument-building arises exactly when
   neither ANT nor π directly determines an alternative, but together they
   provide cumulative evidence.

3. **Cumulative Evidence Necessity**: If π provides no additional evidence
   beyond ANT, "too" is infelicitous.
-/

-- Result 1: Standard Use as Special Case

/-- A proposition "directly determines" an alternative if it entails that alternative.

When p directly determines alt, learning p makes P(alt) = 1. -/
def directlyDetermines {W : Type*} (p : W → Bool) (alt : W → Bool)
    (worlds : List W) : Bool :=
  -- p entails alt: every p-world is an alt-world
  worlds.all fun w => p w → alt w

/-- Check if a proposition directly determines SOME alternative of an issue. -/
def determinesSomeAlternative {W : Type*} (p : W → Bool) (q : Issue W)
    (worlds : List W) : Bool :=
  q.alternatives.any fun alt => directlyDetermines p alt worlds

/-- **Theorem: Standard Use Reduction**

When π directly determines an alternative A of the resolved question,
and that alternative isn't already certain given ANT, then the conjunction
condition is automatically satisfied.

This captures why standard "too" works: if π = "Mary came" and this IS
an alternative of "Who came?", then learning π guarantees that alternative,
so ANT ∧ π always evidences it more strongly than ANT alone (unless ANT
already entailed it).

Linguistically: In standard focus-alternative uses, the general probabilistic
conditions REDUCE TO the simple requirement that ANT be true and π be true.
The complex probability calculations aren't needed - direct entailment suffices.

Note: We require universal entailment (π → alt for all worlds), not just
over a specific world list, because probability calculations use the full
Fintype. -/
theorem standard_use_reduction {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool)
    (alt : InfoState W)
    (_hAltInQ : alt ∈ ctx.resolvedQuestion.alternatives)
    -- Universal entailment: π implies alt in all worlds
    (hEntails : ∀ w : W, prejacent w = true → alt w = true)
    (hNotAlreadyCertain : conditionalProb ctx.prior ctx.antecedent alt < 1)
    (_hAntPossible : probOfProp ctx.prior ctx.antecedent > 0)
    (hConjPossible : probOfProp ctx.prior (fun w => ctx.antecedent w && prejacent w) > 0) :
    -- Then π raises the probability of alt given ANT
    conditionalProb ctx.prior (fun w => ctx.antecedent w && prejacent w) alt >
    conditionalProb ctx.prior ctx.antecedent alt := by
  -- When π entails alt, P(alt | ANT ∧ π) = 1 (since every ANT∧π world is an alt world)
  -- And we're given P(alt | ANT) < 1
  -- So P(alt | ANT ∧ π) > P(alt | ANT)

  -- Step 1: Show P(alt | ANT ∧ π) = 1
  have hCondEq1 : conditionalProb ctx.prior (fun w => ctx.antecedent w && prejacent w) alt = 1 := by
    simp only [conditionalProb]
    simp only [hConjPossible, ↓reduceIte]
    -- P((ANT ∧ π) ∧ alt) = P(ANT ∧ π) because π entails alt
    have hEqMass : probOfProp ctx.prior (fun w => (ctx.antecedent w && prejacent w) && alt w) =
                   probOfProp ctx.prior (fun w => ctx.antecedent w && prejacent w) := by
      simp only [probOfProp]
      congr 1
      ext w
      -- If ANT ∧ π holds, then alt holds (by hEntails)
      by_cases hp : prejacent w
      · have halt : alt w = true := hEntails w hp
        simp only [halt, Bool.and_true]
      · simp only [Bool.not_eq_true] at hp
        simp only [hp, Bool.and_false, Bool.false_and]
    rw [hEqMass]
    -- P(ANT ∧ π) / P(ANT ∧ π) = 1
    have hne : probOfProp ctx.prior (fun w => ctx.antecedent w && prejacent w) ≠ 0 :=
      ne_of_gt hConjPossible
    exact div_self hne

  -- Step 2: Conclude using P(alt | ANT) < 1
  rw [hCondEq1]
  exact hNotAlreadyCertain

/-- Corollary: Standard use satisfies the conjunction condition.

When π directly determines some alternative and that alternative isn't
already certain given ANT, the conjunction condition holds. -/
theorem standard_use_conjunction_condition {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool)
    (alt : InfoState W)
    (hAltInQ : alt ∈ ctx.resolvedQuestion.alternatives)
    -- Universal entailment: π implies alt
    (hEntails : ∀ w : W, prejacent w = true → alt w = true)
    (hNotAlreadyCertain : conditionalProb ctx.prior ctx.antecedent alt < 1)
    (hAntPossible : probOfProp ctx.prior ctx.antecedent > 0)
    (hConjPossible : probOfProp ctx.prior (fun w => ctx.antecedent w && prejacent w) > 0) :
    conjunctionCondition ctx prejacent = true := by
  -- Use standard_use_reduction to show the conjunction strengthens evidence for alt
  have hStrengthens : conditionalProb ctx.prior (fun w => ctx.antecedent w && prejacent w) alt >
                      conditionalProb ctx.prior ctx.antecedent alt :=
    standard_use_reduction ctx prejacent alt hAltInQ hEntails hNotAlreadyCertain hAntPossible hConjPossible

  -- conjunctionCondition requires some resolution to be strengthened
  simp only [conjunctionCondition, someResolutionStrengthened, strengthenedResolutions]
  simp only [decide_eq_true_eq]

  -- Show the filtered list is non-empty (alt is in it)
  have hInFiltered : alt ∈ ctx.resolvedQuestion.alternatives.filter
      (fun a => conjunctionStrengthens ctx.antecedent prejacent a ctx.prior) := by
    simp only [List.mem_filter]
    constructor
    · exact hAltInQ
    · -- conjunctionStrengthens holds for alt
      simp only [conjunctionStrengthens, evidencesMoreStronglyProp]
      simp only [decide_eq_true_eq]
      exact hStrengthens

  -- Non-empty list has positive length
  exact List.length_pos_of_mem hInFiltered

-- Result 2: Argument-Building Characterization

/-- **Theorem: Argument-Building Characterization**

Argument-building use arises exactly when:
1. Neither ANT nor π directly determines any alternative of RQ
2. But together, ANT ∧ π evidences some alternative more strongly than ANT alone

This is the DEFINITION of argument-building: ANT and π are not themselves
answers to RQ, but jointly serve as EVIDENCE for some answer.

Example: "Sue cooks, and she has free time, too."
- RQ = "Who should host?" (implicit)
- ANT = "Sue cooks" - doesn't determine who should host
- π = "Sue has free time" - doesn't determine who should host
- But ANT ∧ π together raise the probability that Sue should host -/
def isArgumentBuildingUseCharacterized {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool)
    (worlds : List W) : Bool :=
  -- Condition 1: ANT doesn't directly determine any alternative
  !determinesSomeAlternative ctx.antecedent ctx.resolvedQuestion worlds &&
  -- Condition 2: π doesn't directly determine any alternative
  !determinesSomeAlternative prejacent ctx.resolvedQuestion worlds &&
  -- Condition 3: But conjunction still strengthens evidence for some alternative
  conjunctionCondition ctx prejacent

/-- Argument-building requires that the resolved question be about something
OTHER than what ANT and π directly assert.

This captures the "implicit QUD" requirement: in argument-building,
the question being addressed isn't "Did ANT happen?" or "Did π happen?"
but rather some further question that ANT and π provide evidence for. -/
theorem argumentBuilding_requires_implicit_qud {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) (worlds : List W)
    (hArgBuild : isArgumentBuildingUseCharacterized ctx prejacent worlds = true) :
    -- Neither ANT nor π directly determines any alternative
    determinesSomeAlternative ctx.antecedent ctx.resolvedQuestion worlds = false ∧
    determinesSomeAlternative prejacent ctx.resolvedQuestion worlds = false := by
  unfold isArgumentBuildingUseCharacterized at hArgBuild
  -- hArgBuild : (!a && !b && c) = true
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hArgBuild
  -- Now hArgBuild should be: (a = false ∧ b = false) ∧ c = true
  exact hArgBuild.1

-- Result 3: Cumulative Evidence Necessity

/-- Two propositions are probabilistically independent given a third if
P(A | B ∧ C) = P(A | B).

When π is independent of all alternatives given ANT, π provides no
additional evidence - it's irrelevant to the question at hand. -/
def conditionallyIndependent {W : Type*} [Fintype W]
    (p1 p2 target : W → Bool) (prior : ExactDist W) : Prop :=
  let pBoth := fun w => p1 w && p2 w
  conditionalProb prior pBoth target = conditionalProb prior p1 target

/-- π is evidentially irrelevant to Q given ANT if π doesn't change the
probability of any alternative when we already know ANT. -/
def evidentiallyIrrelevant {W : Type*} [Fintype W]
    (ant prejacent : W → Bool) (q : Issue W) (prior : ExactDist W) : Prop :=
  ∀ alt ∈ q.alternatives, conditionallyIndependent ant prejacent alt prior

/-- **Theorem: Cumulative Evidence Necessity**

If π is evidentially irrelevant to RQ given ANT (i.e., π doesn't change
the probability of any alternative), then the conjunction condition fails,
and "too" is infelicitous.

This explains WHY "too" requires the prejacent to contribute something:
if π is just noise that doesn't affect the question at hand, it can't
felicitously be marked with "too".

Example of failure:
- "Sue cooks, and she has brown hair, too."
- If hair color is independent of who should host the dinner party,
  this is infelicitous (or requires a different implicit QUD). -/
theorem cumulative_evidence_necessary {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool)
    (hIrrelevant : evidentiallyIrrelevant ctx.antecedent prejacent
                     ctx.resolvedQuestion ctx.prior) :
    -- Then conjunction doesn't strengthen evidence for any alternative
    conjunctionCondition ctx prejacent = false := by
  -- Conjunction condition requires some alternative where P(alt | ANT ∧ π) > P(alt | ANT)
  -- But evidential irrelevance means P(alt | ANT ∧ π) = P(alt | ANT) for all alt
  -- So no alternative is strengthened, hence conjunctionCondition = false
  unfold conjunctionCondition someResolutionStrengthened strengthenedResolutions
  -- The list of strengthened alternatives is empty
  have hEmpty : (ctx.resolvedQuestion.alternatives.filter
      fun alt => conjunctionStrengthens ctx.antecedent prejacent alt ctx.prior) = [] := by
    rw [List.filter_eq_nil_iff]
    intro alt halt
    simp only [conjunctionStrengthens, evidencesMoreStronglyProp]
    -- By hypothesis, P(alt | ANT ∧ π) = P(alt | ANT)
    have h := hIrrelevant alt halt
    simp only [conditionallyIndependent] at h
    rw [h]
    -- ¬(x > x) is trivially true
    simp only [lt_irrefl, decide_false]
    exact Bool.false_ne_true
  simp only [hEmpty, List.length_nil, Nat.not_lt_zero, decide_false]

/-- Corollary: If π is irrelevant, "too" is infelicitous.

This follows from cumulative_evidence_necessary plus the fact that
conjunctionCondition is required for felicity. -/
theorem irrelevant_prejacent_infelicitous {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) (worlds : List W)
    (hIrrelevant : evidentiallyIrrelevant ctx.antecedent prejacent
                     ctx.resolvedQuestion ctx.prior) :
    tooFelicitousWith ctx prejacent worlds = false := by
  simp only [tooFelicitousWith]
  have hConj := cumulative_evidence_necessary ctx prejacent hIrrelevant
  simp only [hConj, Bool.and_false, Bool.false_and]

-- Standard Theorems

/-- Standard use satisfies felicity when both ANT and π answer RQ.

In standard "too" use where ANT and π are both partial answers to the
resolved question, the felicity conditions are satisfied. -/
theorem standard_use_felicitous {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) (worlds : List W)
    (hAnt : antecedentCondition ctx = true)
    (hConj : conjunctionCondition ctx prejacent = true)
    (hNonTriv : nonTrivialityConditionWith prejacent
      (strengthenedResolutions' ctx prejacent) worlds = true)
    (hMax : maximalityCondition prejacent ctx.prior = true) :
    tooFelicitousWith ctx prejacent worlds = true := by
  simp only [tooFelicitousWith, hAnt, hConj, hNonTriv, hMax, Bool.and_self]

/-- Argument-building use is distinct from standard use.

If we have an argument-building use, the antecedent and prejacent
are not focus alternatives. -/
theorem argumentBuilding_not_standard {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool)
    (hArgBuild : isArgumentBuildingUse ctx prejacent = true) :
    isFocusAlternativeUse ctx.antecedent prejacent ctx.resolvedQuestion = false := by
  simp only [isArgumentBuildingUse] at hArgBuild
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hArgBuild
  exact hArgBuild.1

/-- If ANT alone doesn't answer RQ, "too" is infelicitous.

The antecedent must be established as relevant to the resolved question. -/
theorem no_antecedent_infelicitous {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) (worlds : List W)
    (hNoAnt : antecedentCondition ctx = false) :
    tooFelicitousWith ctx prejacent worlds = false := by
  simp only [tooFelicitousWith, hNoAnt, Bool.false_and]

-- Examples Infrastructure

/-- Structure for storing additive particle examples for testing. -/
structure AdditiveExample (W : Type*) [Fintype W] where
  description : String
  context : AdditiveContext W
  prejacent : W → Bool
  expectedFelicitous : Bool
  useType : AdditiveUseType

/-- Verify an example matches expectations (with explicit world list). -/
def AdditiveExample.verifyWith {W : Type*} [Fintype W]
    (ex : AdditiveExample W) (worlds : List W) : Bool :=
  tooFelicitousWith ex.context ex.prejacent worlds == ex.expectedFelicitous

/-- Noncomputable verification using Fintype. -/
noncomputable def AdditiveExample.verify {W : Type*} [Fintype W]
    (ex : AdditiveExample W) : Bool :=
  tooFelicitous ex.context ex.prejacent == ex.expectedFelicitous

end Montague.Particle.Additive
