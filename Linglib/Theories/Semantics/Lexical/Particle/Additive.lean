import Linglib.Theories.Semantics.Questions.Answerhood.ProbabilisticAnswerhood
import Linglib.Theories.Semantics.Questions.Denotation.Basic

/-!
# Additive Particles: too, also, either
@cite{heim-1992} @cite{thomas-2026}

Felicity conditions for additive particles following @cite{thomas-2026}
"A probabilistic, question-based approach to additivity".

## Related modules

- `Semantics.FocusParticles` (`Theories/Semantics/Focus/Particles.lean`):
  Traditional focus particle semantics (EVEN, only). @cite{thomas-2026} §6
  argues that Def. 64 subsumes @cite{heim-1992}'s individual-based
  presupposition as a special case of the standard focus-alternative use.
- `Ahn2015`: Ahn's ⊓/⊔ Boolean
  semantics for too/either. Independent analysis; Thomas does not discuss it.
- `ProbabilisticAnswerhood`: Core definitions (Defs. 61–63) used here.

## Heim 1992 Subsumption

@cite{thomas-2026} §6 argues that Def. 64 subsumes @cite{heim-1992}'s
individual-based additive presupposition as a special case. This is
proved formally by `heim_subsumption`: when ANT and π each entail
distinct alternatives of RQ (the Heim setup), the Antecedent and
Conjunction Conditions (Def. 64a-b) hold automatically.

## Insight: Argument-Building Use

The novel contribution of @cite{thomas-2026} is explaining the "argument-building"
use of "too" where the antecedent and prejacent aren't focus alternatives
but jointly build an argument for some conclusion.

Example (@cite{thomas-2026}, ex. 1c/14c/65):
"A room just opened up at this hotel. It looks kind of fancy, too."
- ANT = "room just opened up", π = "looks fancy" are not focus alternatives
- Both contribute toward conclusion: "This hotel would be a good place to stay"

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
- "A room just opened up at this hotel. It looks kind of fancy, too."
  (@cite{thomas-2026}, ex. 1c/14c/65)
- ANT = "room just opened up", π = "looks fancy"
- RQ = "What would be a good hotel?" (implicit)
- Together they evidence "This hotel would be a good place to stay"

-/

namespace Semantics.Lexical.Particle.Additive

open Semantics.Questions
open Discourse
open Semantics.Questions.ProbabilisticAnswerhood

-- Additive Particle Types

/-- Types of additive particles. -/
inductive AdditiveParticle where
  | too    -- positive polarity, typically sentence-final
  | also   -- positive polarity, typically medial position
  | either -- negative polarity
  deriving DecidableEq, Repr, Inhabited

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

@cite{thomas-2026} requires:
- A resolved question (RQ) in the discourse
- An antecedent proposition (ANT) that answers RQ
- A prior probability distribution -/
structure AdditiveContext (W : Type*) [Fintype W] where
  /-- The resolved question (RQ) -/
  resolvedQuestion : Issue W
  /-- The antecedent proposition (ANT) - what was just established -/
  antecedent : W → Bool
  /-- Prior probability distribution over worlds -/
  prior : Prior W

namespace AdditiveContext

variable {W : Type*} [Fintype W]

/-- Create a context from a polar question. -/
def fromPolar (p : W → Bool) (ant : W → Bool) (prior : Prior W) :
    AdditiveContext W :=
  { resolvedQuestion := Issue.polar p
  , antecedent := ant
  , prior := prior }

/-- Create a context from a list of alternatives. -/
def fromAlternatives (alts : List (InfoState W)) (ant : W → Bool)
    (prior : Prior W) : AdditiveContext W :=
  { resolvedQuestion := Issue.ofAlternatives alts
  , antecedent := ant
  , prior := prior }

end AdditiveContext

-- Felicity Conditions (Definition 64)

/-- Condition 1: Antecedent probabilistically answers RQ (Def. 64a).

The antecedent must raise the probability of some resolution.

Uses `probAnswers` (condition (a) of Def. 62 only), which checks that some
alternative's conditional probability exceeds its prior. For polar/binary
QUDs, this is equivalent to the full Def. 62 (`probAnswersFull`) by
`probAnswersFull_eq_simple_binary`. For non-binary questions, the full
definition additionally requires Bayes-factor dominance (condition (b)). -/
def antecedentCondition {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) : Bool :=
  probAnswers ctx.antecedent ctx.resolvedQuestion ctx.prior

/-- Condition 2: Conjunction answers RQ and evidences more strongly.

@cite{thomas-2026} Def. 64b: ANT ∩ ⟦π⟧ Answers RQ, AND RQ|_{ANT∩⟦π⟧}
is Evidenced more strongly by ANT ∩ ⟦π⟧ than by ANT. -/
def conjunctionCondition {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) : Bool :=
  let conj := λ w => ctx.antecedent w && prejacent w
  -- Def. 64b(i): ANT∧π Answers RQ
  probAnswers conj ctx.resolvedQuestion ctx.prior &&
  -- Def. 64b(ii): ANT∧π evidences some resolution more strongly than ANT alone
  someResolutionStrengthened ctx.antecedent prejacent ctx.resolvedQuestion ctx.prior

/-- Get the resolution(s) that are strengthened by the conjunction. -/
def strengthenedResolutions' {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) : List (InfoState W) :=
  strengthenedResolutions ctx.antecedent prejacent ctx.resolvedQuestion ctx.prior

/-- Condition 3a: Prejacent doesn't entail the evidenced resolution.

π shouldn't make the conclusion trivially certain.
Uses a provided world list for computability.

TODO: This checks `.any` over all strengthened alternatives, but should check
against the specific Q|_{ANT∩π} from Def. 62. For singleton resolutions (all
paper examples), the behavior is identical. -/
def nonTrivialityConditionWith {W : Type*}
    (prejacent : W → Bool) (strengthened : List (InfoState W))
    (worlds : List W) : Bool :=
  strengthened.any λ alt =>
    -- π doesn't entail alt (there's a π-world that's not in alt)
    !(worlds.all λ w => prejacent w → alt w)

/-- Condition 3b: No weaker proposition works as well (Def. 64c.ii).

For every strengthened resolution R, no strict weakening S ⊃ ⟦π⟧
should evidence R at least as strongly as π does given ANT.

Over finite types this reduces to an entailment check: for every
world w with positive prior, ANT(w) ∧ R(w) → π(w). If this holds,
then for any S ⊃ ⟦π⟧, since ANT ∩ S ⊇ ANT ∩ π, conditioning on
the larger set ANT ∩ S can only dilute the probability of R
(subset dilution of conditional probability), so P(R | ANT ∩ π) ≥
P(R | ANT ∩ S), preserving strict evidence advantage.

TODO: Like `nonTrivialityConditionWith`, this uses all strengthened
alternatives instead of the specific Q|_{ANT∩π}. Correct for singleton
resolutions (all paper examples). -/
def maximalityCondition {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool)
    (strengthened : List (InfoState W))
    (worlds : List W) : Bool :=
  strengthened.all fun resolution =>
    worlds.all fun w =>
      if ctx.prior w > 0 then
        !(ctx.antecedent w && resolution w && !prejacent w)
      else true

/-- Full felicity conditions for TOO(π) with explicit world list.

Definition 64 from @cite{thomas-2026}. -/
def tooFelicitousWith {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool)
    (worlds : List W) : Bool :=
  -- Condition 1: ANT probabilistically answers RQ
  antecedentCondition ctx &&
  -- Condition 2: ANT ∧ π evidences some resolution more strongly than ANT alone
  conjunctionCondition ctx prejacent &&
  -- Condition 3a: π doesn't entail the strengthened resolution
  nonTrivialityConditionWith prejacent (strengthenedResolutions' ctx prejacent) worlds &&
  -- Condition 3b: Maximality — no weaker proposition works as well (Def. 64c.ii)
  maximalityCondition ctx prejacent (strengthenedResolutions' ctx prejacent) worlds

/-- Noncomputable version using Fintype.elems. -/
noncomputable def tooFelicitous {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) : Bool :=
  tooFelicitousWith ctx prejacent Fintype.elems.toList

/-- Felicity for "also" — same core conditions as "too".

@cite{thomas-2026} §6 (ex. 86) observes that sentence-initial "also" is
NOT subject to the Prejacent Condition part (ii) (maximality):
"Also, Bailey plays the cello" is acceptable where "#Bailey plays the
cello, too" is not. This implementation does not model syntactic position
and applies full felicity conditions regardless. A position-sensitive
version would skip `maximalityCondition` for sentence-initial "also". -/
noncomputable def alsoFelicitous {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool) : Bool :=
  tooFelicitous ctx prejacent

/-- Felicity for "either" — placeholder, gates on negative polarity.

@cite{thomas-2026} explicitly defers a precise characterization of
"either" to future work (footnote 9). This placeholder simply gates
on polarity; the actual felicity conditions for "either" likely involve
additional constraints (see @cite{ahn-2015} for an alternative account
using ⊔ in a Boolean algebra). -/
noncomputable def eitherFelicitous {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool)
    (inNegativeContext : Bool) : Bool :=
  inNegativeContext && tooFelicitous ctx prejacent

-- Core Theoretical Results (@cite{thomas-2026})

/-!
## Central Theorems

These theorems capture the key linguistic insights of @cite{thomas-2026}:

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
  worlds.all λ w => p w → alt w

/-- Check if a proposition directly determines SOME alternative of an issue. -/
def determinesSomeAlternative {W : Type*} (p : W → Bool) (q : Issue W)
    (worlds : List W) : Bool :=
  q.alternatives.any λ alt => directlyDetermines p alt worlds

/-- When π entails alt, P(alt | ANT ∧ π) = 1 (every ANT∧π world is an alt world). -/
private lemma condProb_conj_eq_one_of_entails {W : Type*} [Fintype W]
    (prior : Prior W) (ant prejacent alt : W → Bool)
    (hEntails : ∀ w : W, prejacent w = true → alt w = true)
    (hConjPossible : probOfProp prior (λ w => ant w && prejacent w) > 0) :
    conditionalProb prior (λ w => ant w && prejacent w) alt = 1 := by
  have hEqMass : probOfProp prior (λ w => (ant w && prejacent w) && alt w) =
                 probOfProp prior (λ w => ant w && prejacent w) := by
    congr 1; ext w
    by_cases hp : prejacent w
    · simp only [hEntails w hp, Bool.and_true]
    · simp only [Bool.not_eq_true] at hp; simp only [hp, Bool.and_false, Bool.false_and]
  rw [show conditionalProb prior (λ w => ant w && prejacent w) alt =
        probOfProp prior (λ w => (ant w && prejacent w) && alt w) /
        probOfProp prior (λ w => ant w && prejacent w) from
    Core.FinitePMF.condProb_of_pos prior _ alt hConjPossible,
    hEqMass]
  exact div_self (ne_of_gt hConjPossible)

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
The complex probability calculations aren't needed - direct entailment suffices. -/
theorem standard_use_reduction {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool)
    (alt : InfoState W)
    (_hAltInQ : alt ∈ ctx.resolvedQuestion.alternatives)
    (hEntails : ∀ w : W, prejacent w = true → alt w = true)
    (hNotAlreadyCertain : conditionalProb ctx.prior ctx.antecedent alt < 1)
    (_hAntPossible : probOfProp ctx.prior ctx.antecedent > 0)
    (hConjPossible : probOfProp ctx.prior (λ w => ctx.antecedent w && prejacent w) > 0) :
    conditionalProb ctx.prior (λ w => ctx.antecedent w && prejacent w) alt >
    conditionalProb ctx.prior ctx.antecedent alt := by
  rw [condProb_conj_eq_one_of_entails ctx.prior ctx.antecedent prejacent alt hEntails hConjPossible]
  exact hNotAlreadyCertain

/-- Corollary: Standard use satisfies the conjunction condition.

When π directly determines some alternative and that alternative isn't
already certain (neither given ANT nor a priori), the conjunction
condition holds. -/
theorem standard_use_conjunction_condition {W : Type*} [Fintype W]
    (ctx : AdditiveContext W) (prejacent : W → Bool)
    (alt : InfoState W)
    (hAltInQ : alt ∈ ctx.resolvedQuestion.alternatives)
    (hEntails : ∀ w : W, prejacent w = true → alt w = true)
    (hNotAlreadyCertain : conditionalProb ctx.prior ctx.antecedent alt < 1)
    (hAntPossible : probOfProp ctx.prior ctx.antecedent > 0)
    (hConjPossible : probOfProp ctx.prior (λ w => ctx.antecedent w && prejacent w) > 0)
    (hAltNotCertain : probOfState ctx.prior alt < 1) :
    conjunctionCondition ctx prejacent = true := by
  have hCondEq1 := condProb_conj_eq_one_of_entails ctx.prior ctx.antecedent prejacent alt
    hEntails hConjPossible
  have hStrengthens := standard_use_reduction ctx prejacent alt hAltInQ hEntails
    hNotAlreadyCertain hAntPossible hConjPossible
  simp only [conjunctionCondition]
  rw [Bool.and_eq_true]
  constructor
  · -- Def. 64b(i): probAnswers — P(alt | ANT ∧ π) = 1 > P(alt)
    unfold probAnswers probOfState
    rw [List.any_eq_true]
    exact ⟨alt, hAltInQ, by simp only [decide_eq_true_eq]; rw [hCondEq1]; exact hAltNotCertain⟩
  · -- Def. 64b(ii): someResolutionStrengthened
    unfold someResolutionStrengthened strengthenedResolutions
    simp only [decide_eq_true_eq]
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hAltInQ, by
      simp only [conjunctionStrengthens, evidencesMoreStronglyProp, decide_eq_true_eq]
      exact hStrengthens⟩)

-- Heim 1992 Subsumption

/-- **Theorem: Heim 1992 Subsumption** (@cite{thomas-2026} §6).

@cite{heim-1992}'s additive presupposition for TOO(π) requires:
∃x ≠ y such that P(x) is established and π = "y P'd".

Under @cite{thomas-2026}'s Def. 64, this falls out as a SPECIAL CASE of
the standard focus-alternative use. When ANT and π each entail distinct
alternatives of RQ:

- The **Antecedent Condition** holds because ANT entails an alternative,
  raising its probability to 1 (by `probAnswers_when_entailing`).
- The **Conjunction Condition** holds because π entails another alternative
  that wasn't already certain given ANT, so ANT ∧ π provides new evidence
  (by `standard_use_conjunction_condition`).

The remaining conditions (non-triviality, maximality) depend on the
question structure and are verified concretely in the pizza/spaghetti
scenario (`Thomas2026.pizza_spaghetti_too_felicitous`).

This theorem makes precise the claim in @cite{thomas-2026} §6 that
Def. 64 **subsumes** @cite{heim-1992}'s individual-based presupposition:
every Heim-felicitous "too" is Thomas-felicitous, but Thomas additionally
explains argument-building uses that Heim cannot. -/
theorem heim_subsumption {W : Type*} [Fintype W] [DecidableEq W]
    (ctx : AdditiveContext W) (prejacent : W → Bool)
    (altAnt altPi : InfoState W)
    -- Heim's setup: ANT entails one alternative, π entails another
    (hAntInQ : altAnt ∈ ctx.resolvedQuestion.alternatives)
    (hPiInQ : altPi ∈ ctx.resolvedQuestion.alternatives)
    (hAntEntails : ∀ w, ctx.antecedent w = true → altAnt w = true)
    (hPiEntails : ∀ w, prejacent w = true → altPi w = true)
    -- Probability assumptions (non-degeneracy)
    (hAntPossible : probOfProp ctx.prior ctx.antecedent > 0)
    (hConjPossible : probOfProp ctx.prior (λ w => ctx.antecedent w && prejacent w) > 0)
    (hAntAltNotCertain : probOfState ctx.prior altAnt < 1)
    (hPiAltNotCertain : probOfState ctx.prior altPi < 1)
    (hPiNotCertainGivenAnt : conditionalProb ctx.prior ctx.antecedent altPi < 1) :
    -- Then Def. 64a and 64b hold
    antecedentCondition ctx = true ∧
    conjunctionCondition ctx prejacent = true := by
  exact ⟨
    probAnswers_when_entailing ctx.antecedent ctx.resolvedQuestion ctx.prior
      altAnt hAntInQ hAntEntails hAntPossible hAntAltNotCertain,
    standard_use_conjunction_condition ctx prejacent altPi hPiInQ hPiEntails
      hPiNotCertainGivenAnt hAntPossible hConjPossible hPiAltNotCertain
  ⟩

-- Result 2: Argument-Building Characterization

/-- **Theorem: Argument-Building Characterization**

Argument-building use arises exactly when:
1. Neither ANT nor π directly determines any alternative of RQ
2. But together, ANT ∧ π evidences some alternative more strongly than ANT alone

This is the DEFINITION of argument-building: ANT and π are not themselves
answers to RQ, but jointly serve as EVIDENCE for some answer.

Example (@cite{thomas-2026}, ex. 1c/65):
"A room just opened up at this hotel. It looks kind of fancy, too."
- RQ = "What would be a good hotel?" (implicit)
- ANT = "room just opened up" - doesn't determine which hotel is good
- π = "looks fancy" - doesn't determine which hotel is good
- But ANT ∧ π together raise the probability that this hotel is good -/
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
    (p1 p2 target : W → Bool) (prior : Prior W) : Prop :=
  let pBoth := λ w => p1 w && p2 w
  conditionalProb prior pBoth target = conditionalProb prior p1 target

/-- π is evidentially irrelevant to Q given ANT if π doesn't change the
probability of any alternative when we already know ANT. -/
def evidentiallyIrrelevant {W : Type*} [Fintype W]
    (ant prejacent : W → Bool) (q : Issue W) (prior : Prior W) : Prop :=
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
      λ alt => conjunctionStrengthens ctx.antecedent prejacent alt ctx.prior) = [] := by
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
  simp only [hEmpty, List.length_nil, Nat.not_lt_zero, decide_false, Bool.and_false]

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

end Semantics.Lexical.Particle.Additive
