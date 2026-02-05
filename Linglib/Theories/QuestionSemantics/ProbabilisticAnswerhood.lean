import Linglib.Theories.QuestionSemantics.Inquisitive
import Linglib.Theories.RSA.Core.Distribution

/-!
# Probabilistic Answerhood (Thomas 2026)

Answerhood in terms of probability changes, following Thomas (2026)
"A probabilistic, question-based approach to additivity".

## Core Definitions

**Definition 61 - Relevance**: A proposition P is relevant to question Q iff
P changes the probability of some alternative:
```
Relevant(P, Q) ≡ ∃A ∈ Q: P(A|P) ≠ P(A)
```

**Definition 62 - Probabilistic Answerhood**: P probabilistically answers Q iff
P raises the probability of some alternative:
```
ProbAnswers(P, Q) ≡ ∃A ∈ Q: P(A|P) > P(A)
```

**Definition 63 - Evidences More Strongly**: R evidences A more strongly than R':
```
EvidencesMoreStrongly(R, R', A) ≡ P(A|info(R)) > P(A|info(R'))
```

These probabilistic notions of answerhood are central to Thomas's analysis
of additive particles like "too", "also", "either".

## Connection to Mention-Some

Probabilistic answerhood generalizes the mention-some/mention-all distinction:
- Under uniform priors, probabilistic answerhood reduces to standard partial answerhood
- Non-uniform priors allow context-sensitive answerhood

## References

- Thomas (2026). A probabilistic, question-based approach to additivity.
- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
-/

namespace QuestionSemantics.ProbabilisticAnswerhood

open QuestionSemantics
open QuestionSemantics.Inquisitive

-- Conditional Probability Infrastructure

/-- Compute P(φ) - probability that φ is true.

This sums the probability mass over worlds where φ holds. -/
def probOfProp {W : Type*} [Fintype W]
    (prior : ExactDist W) (φ : W → Bool) : ℚ :=
  ∑ w : W, if φ w then prior.mass w else 0

/-- Compute P(A | C) - conditional probability of A given C.

Returns P(A ∧ C) / P(C) when P(C) > 0, otherwise 0. -/
def conditionalProb {W : Type*} [Fintype W]
    (prior : ExactDist W) (condition : W → Bool) (target : W → Bool) : ℚ :=
  let pCondition := probOfProp prior condition
  if pCondition > 0 then
    let pBoth := probOfProp prior (λ w => condition w && target w)
    pBoth / pCondition
  else
    0

/-- Probability of an info state being actual.

P(σ) = probability that the actual world is in σ. -/
def probOfState {W : Type*} [Fintype W]
    (prior : ExactDist W) (σ : InfoState W) : ℚ :=
  probOfProp prior σ

-- Definition 61: Relevance

/-- Relevance: P changes the probability of some alternative in Q.

Definition 61 from Thomas (2026):
```
Relevant(P, Q) ≡ ∃A ∈ Q: P(A|P) ≠ P(A)
```

A proposition P is relevant to question Q iff learning P would change
the probability distribution over Q's alternatives. -/
def relevant {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : ExactDist W) : Bool :=
  q.alternatives.any λ alt =>
    let condProb := conditionalProb prior p alt
    let priorProb := probOfState prior alt
    condProb != priorProb

/-- Non-relevance: P doesn't change any alternative's probability. -/
def irrelevant {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : ExactDist W) : Bool :=
  !relevant p q prior

-- Definition 62: Probabilistic Answerhood

/-- Probabilistic answerhood: P raises the probability of some alternative.

Definition 62 from Thomas (2026):
```
ProbAnswers(P, Q) ≡ ∃A ∈ Q: P(A|P) > P(A)
```

This is a weaker condition than standard partial answerhood:
- Standard: P is consistent with some cell and rules out others
- Probabilistic: P raises probability of some answer

Under uniform priors on partitions, these coincide. -/
def probAnswers {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : ExactDist W) : Bool :=
  q.alternatives.any λ alt =>
    let condProb := conditionalProb prior p alt
    let priorProb := probOfState prior alt
    condProb > priorProb

/-- Which alternative(s) are supported by P.

Returns the alternatives whose probability is raised by learning P. -/
def supportedAlternatives {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : ExactDist W) : List (InfoState W) :=
  q.alternatives.filter λ alt =>
    let condProb := conditionalProb prior p alt
    let priorProb := probOfState prior alt
    condProb > priorProb

/-- The maximally supported alternative: the one whose probability
increases the most when P is learned. -/
def maxSupportedAlternative {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : ExactDist W) : Option (InfoState W × ℚ) :=
  let increases := q.alternatives.filterMap λ alt =>
    let condProb := conditionalProb prior p alt
    let priorProb := probOfState prior alt
    let increase := condProb - priorProb
    if increase > 0 then some (alt, increase) else none
  increases.foldl (λ best current =>
    match best with
    | none => some current
    | some (_, bestInc) =>
      if current.2 > bestInc then some current else best
  ) none

-- Definition 63: Evidences More Strongly

/-- Informational content of a resolving state.

For a single info state σ (representing a potential resolution),
info(σ) is just σ itself - the proposition that the actual world is in σ.

For multiple resolving states, info({σ₁, ..., σₙ}) is their union. -/
def infoContent {W : Type*} (states : List (InfoState W)) : W → Bool :=
  λ w => states.any λ σ => σ w

/-- Evidences more strongly: R evidences A more strongly than R' does.

Definition 63 from Thomas (2026):
```
EvidencesMoreStrongly(R, R', A) ≡ P(A|info(R)) > P(A|info(R'))
```

Used in the felicity conditions for additive particles: the prejacent
combined with the antecedent must evidence some resolution more strongly
than the antecedent alone. -/
def evidencesMoreStrongly {W : Type*} [Fintype W]
    (r r' : List (InfoState W)) (a : InfoState W)
    (prior : ExactDist W) : Bool :=
  let infoR := infoContent r
  let infoR' := infoContent r'
  let probGivenR := conditionalProb prior infoR a
  let probGivenR' := conditionalProb prior infoR' a
  probGivenR > probGivenR'

/-- Simpler version: single propositions instead of state lists. -/
def evidencesMoreStronglyProp {W : Type*} [Fintype W]
    (evidence evidence' : W → Bool) (conclusion : W → Bool)
    (prior : ExactDist W) : Bool :=
  let probGivenEvidence := conditionalProb prior evidence conclusion
  let probGivenEvidence' := conditionalProb prior evidence' conclusion
  probGivenEvidence > probGivenEvidence'

-- Strength of Evidence

/-- Compute how much evidence raises the probability of a conclusion.

This is P(A|E) - P(A), measuring the "boost" from learning E. -/
def evidentialBoost {W : Type*} [Fintype W]
    (evidence : W → Bool) (conclusion : W → Bool)
    (prior : ExactDist W) : ℚ :=
  let condProb := conditionalProb prior evidence conclusion
  let priorProb := probOfProp prior conclusion
  condProb - priorProb

/-- Evidence is positive if it raises the probability of the conclusion. -/
def isPositiveEvidence {W : Type*} [Fintype W]
    (evidence : W → Bool) (conclusion : W → Bool)
    (prior : ExactDist W) : Bool :=
  evidentialBoost evidence conclusion prior > 0

/-- Evidence is negative if it lowers the probability of the conclusion. -/
def isNegativeEvidence {W : Type*} [Fintype W]
    (evidence : W → Bool) (conclusion : W → Bool)
    (prior : ExactDist W) : Bool :=
  evidentialBoost evidence conclusion prior < 0

-- Connection to Standard Answerhood

/-- Check if a prior is uniform over a world list.

For proving that probabilistic answerhood reduces to standard answerhood
under uniform priors. -/
def isUniformOver {W : Type*} [Fintype W] [DecidableEq W]
    (prior : ExactDist W) (worlds : List W) : Bool :=
  match worlds with
  | [] => true
  | w :: ws =>
    let prob := prior.mass w
    ws.all λ v => prior.mass v == prob

/-- Under uniform priors, positive propositions raise alternative probability.

This connects probabilistic answerhood to classical partial answerhood.
If P is consistent with alternative A (P ∩ A ≠ ∅) and P rules out some
worlds outside A, then P raises A's probability. -/
theorem probAnswers_when_consistent {W : Type*} [Fintype W] [DecidableEq W]
    (p : W → Bool) (q : Issue W) (prior : ExactDist W)
    (_hUniform : isUniformOver prior (Fintype.elems.toList) = true)
    (_hConsistent : q.alternatives.any λ alt =>
      Fintype.elems.toList.any λ w => p w && alt w) :
    -- If P is consistent with some alternative and has positive probability
    probOfProp prior p > 0 →
    -- Then P is at least relevant to Q
    relevant p q prior = true := by
  sorry

-- Combined Evidence (for Additive Particles)

/-- Check if conjunction of two propositions provides stronger evidence
than the first proposition alone.

This is the core of Thomas's analysis of additive particles:
TOO(π) requires that ANT ∧ π evidences some resolution more strongly
than ANT alone. -/
def conjunctionStrengthens {W : Type*} [Fintype W]
    (p1 p2 : W → Bool) (conclusion : W → Bool)
    (prior : ExactDist W) : Bool :=
  evidencesMoreStronglyProp (λ w => p1 w && p2 w) p1 conclusion prior

/-- Find resolutions that the conjunction evidences more strongly. -/
def strengthenedResolutions {W : Type*} [Fintype W]
    (p1 p2 : W → Bool) (q : Issue W)
    (prior : ExactDist W) : List (InfoState W) :=
  q.alternatives.filter λ alt =>
    conjunctionStrengthens p1 p2 alt prior

/-- Check if there exists some resolution that is strengthened. -/
def someResolutionStrengthened {W : Type*} [Fintype W]
    (p1 p2 : W → Bool) (q : Issue W)
    (prior : ExactDist W) : Bool :=
  (strengthenedResolutions p1 p2 q prior).length > 0

-- Probabilistic Mention-Some

/-- Probabilistic mention-some: P gives a "partial" probabilistic answer.

P is a probabilistic mention-some answer to Q if:
1. P raises the probability of some alternative(s)
2. P doesn't resolve Q completely (doesn't make one alternative certain) -/
def isProbMentionSomeAnswer {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : ExactDist W) : Bool :=
  let supported := supportedAlternatives p q prior
  -- Raises probability of some alternatives
  supported.length > 0 &&
  -- But doesn't make any alternative certain (probability 1)
  supported.all λ alt => conditionalProb prior p alt < 1

/-- Probabilistic mention-all: P resolves Q completely.

P is a probabilistic mention-all answer if learning P makes
exactly one alternative have probability 1. -/
def isProbMentionAllAnswer {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : ExactDist W) : Bool :=
  let certainAlts := q.alternatives.filter λ alt =>
    conditionalProb prior p alt == 1
  certainAlts.length == 1

-- Theorems

/-- Probabilistic answerhood implies relevance.

If P raises the probability of some alternative, then P changes
the probability of that alternative. -/
theorem probAnswers_implies_relevant {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : ExactDist W) :
    probAnswers p q prior = true → relevant p q prior = true := by
  intro h
  simp only [probAnswers, relevant] at *
  simp only [List.any_eq_true, decide_eq_true_eq] at *
  obtain ⟨alt, hmem, hgt⟩ := h
  refine ⟨alt, hmem, ?_⟩
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  exact ne_of_gt hgt

/-- Stronger evidence is positive evidence.

If R evidences A more strongly than R', then R is positive evidence for A
relative to R'. -/
theorem strongerEvidence_is_positive {W : Type*} [Fintype W]
    (r r' : List (InfoState W)) (a : InfoState W)
    (prior : ExactDist W) :
    evidencesMoreStrongly r r' a prior = true →
    conditionalProb prior (infoContent r) a >
    conditionalProb prior (infoContent r') a := by
  intro h
  simp only [evidencesMoreStrongly, decide_eq_true_eq] at h
  exact h

end QuestionSemantics.ProbabilisticAnswerhood
