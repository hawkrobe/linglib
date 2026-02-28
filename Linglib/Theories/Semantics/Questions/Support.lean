import Linglib.Theories.Semantics.Questions.ProbabilisticAnswerhood

/-!
# Evidential Support (IKW 2025, Thomas 2026)

Named abstraction over probabilistic answerhood primitives, factored out for
reuse across discourse particles that share the notion of "supporting an
answer to a QUD" — additive particles (Thomas 2026) and discourse *only*
(Ippolito, Kiss & Williams 2025).

## Two layers of SUPPORT

IKW (2025) Definition 13 decomposes SUPPORT into two independent conditions:

1. **Doxastic**: the speaker believes some alternative q of the sentence's
   denotation (DOX_sp ⊆ q for some q ∈ ⟦S⟧)
2. **Probabilistic**: q provides evidence for answer r (P(r|q) > P(r))

The doxastic condition is what blocks canonical info-seeking questions as the
left argument of discourse *only*: the speaker doesn't believe any answer, so
DOX_sp ⊄ q for all q ∈ ⟦S⟧. Biased/rhetorical questions CAN satisfy the
doxastic condition because the speaker does believe an answer.

## Definitions

- `probSupports` — probabilistic support: P(α|E) > P(α) (wraps `isPositiveEvidence`)
- `probAntiSupports` — probabilistic anti-support: P(α|E) < P(α)
- `fullSupport` — IKW Def. 13: doxastic + probabilistic (DOX_sp ⊆ q ∧ P(r|q) > P(r))
- `supportedAnswers` — which alternatives are supported
- `supportStrength` — magnitude of evidential boost

## References

- Thomas (2026). A probabilistic, question-based approach to additivity.
- Ippolito, Kiss & Williams (2025). Discourse *only*. WCCFL 41.
-/

namespace Semantics.Questions.Support

open Semantics.Questions.Inquisitive
open Semantics.Questions.ProbabilisticAnswerhood

-- Probabilistic Support

/-- Probabilistic support: evidence E raises the probability of answer α.

This is the probabilistic component of IKW (2025) Definition 13:
P(α|E) > P(α). Wraps `isPositiveEvidence` from `ProbabilisticAnswerhood`. -/
def probSupports {W : Type*} [Fintype W]
    (prior : Prior W) (evidence : W → Bool) (answer : W → Bool) : Bool :=
  isPositiveEvidence evidence answer prior

/-- Probabilistic anti-support: evidence E lowers the probability of answer α.

P(α|E) < P(α). Wraps `isNegativeEvidence`. -/
def probAntiSupports {W : Type*} [Fintype W]
    (prior : Prior W) (evidence : W → Bool) (answer : W → Bool) : Bool :=
  isNegativeEvidence evidence answer prior

/-- Which answers in a QUD are probabilistically supported by evidence E. -/
def supportedAnswers {W : Type*} [Fintype W]
    (evidence : W → Bool) (q : Issue W) (prior : Prior W) :
    List (InfoState W) :=
  supportedAlternatives evidence q prior

/-- The magnitude of evidential support: P(α|E) − P(α). -/
def supportStrength {W : Type*} [Fintype W]
    (evidence : W → Bool) (conclusion : W → Bool)
    (prior : Prior W) : ℚ :=
  evidentialBoost evidence conclusion prior

/-- Conjunction of two propositions strengthens support for a conclusion
beyond what the first proposition provides alone. -/
def conjunctionStrengthensSupport {W : Type*} [Fintype W]
    (p1 p2 : W → Bool) (conclusion : W → Bool)
    (prior : Prior W) : Bool :=
  conjunctionStrengthens p1 p2 conclusion prior

-- Doxastic Support (IKW 2025 Def. 13)

/-- Full SUPPORT predicate from IKW (2025) Definition 13.

SUPPORT(S, r) holds iff:
1. (Doxastic) ∃q ∈ ⟦S⟧: DOX_sp ⊆ q — the speaker believes some alternative
   of S's denotation
2. (Probabilistic) q provides evidence for r — P(r|q) > P(r)

Parameters:
- `dox`: the speaker's doxastic state DOX_sp (an info state)
- `sentDen`: the inquisitive denotation ⟦S⟧ (its alternatives are the q's)
- `prior`: probability distribution over worlds
- `answer`: the answer r being supported
- `worlds`: list of worlds for evaluating the doxastic subset check -/
def fullSupport {W : Type*} [Fintype W]
    (dox : InfoState W) (sentDen : Issue W) (prior : Prior W)
    (answer : W → Bool) (worlds : List W) : Bool :=
  sentDen.alternatives.any λ q =>
    -- Doxastic: DOX_sp ⊆ q
    supports dox q worlds &&
    -- Probabilistic: P(r|q) > P(r)
    probSupports prior q answer

-- Theorems

/-- `probSupports` is definitionally `isPositiveEvidence`. -/
theorem probSupports_iff_positive_boost {W : Type*} [Fintype W]
    (prior : Prior W) (evidence answer : W → Bool) :
    probSupports prior evidence answer = isPositiveEvidence evidence answer prior :=
  rfl

/-- Supporting some answer implies relevance to the QUD. -/
theorem probSupports_implies_relevant {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : Prior W)
    (h : probAnswers p q prior = true) :
    relevant p q prior = true :=
  probAnswers_implies_relevant p q prior h

/-- Entailing an alternative guarantees support, given positive probability
and non-certainty. -/
theorem probSupports_when_entailing {W : Type*} [Fintype W] [DecidableEq W]
    (p : W → Bool) (q : Issue W) (prior : Prior W)
    (alt : W → Bool)
    (hAltMem : alt ∈ q.alternatives)
    (hEntails : ∀ w, p w = true → alt w = true)
    (hPosP : probOfProp prior p > 0)
    (hNotCertain : probOfState prior alt < 1) :
    probAnswers p q prior = true :=
  probAnswers_when_entailing p q prior alt hAltMem hEntails hPosP hNotCertain

/-- Full support for declaratives: a declarative's denotation has one
alternative (its propositional content). If the speaker believes p
(DOX_sp ⊆ p) and p provides evidence for r, then SUPPORT(S, r) holds.

This is a convenience lemma — fullSupport applied to a singleton Issue. -/
theorem fullSupport_declarative {W : Type*} [Fintype W]
    (dox : InfoState W) (p : W → Bool) (prior : Prior W)
    (answer : W → Bool) (worlds : List W)
    (hBelief : supports dox p worlds = true)
    (hEvidence : probSupports prior p answer = true) :
    fullSupport dox ⟨[p]⟩ prior answer worlds = true := by
  simp only [fullSupport, List.any_cons, List.any_nil, Bool.or_false,
    Bool.and_eq_true]
  exact ⟨hBelief, hEvidence⟩

/-- Full support fails when the speaker doesn't believe any alternative.

For canonical info-seeking questions, the speaker doesn't know the answer:
DOX_sp ⊄ q for ALL q ∈ ⟦S⟧. This blocks SUPPORT entirely, regardless of
the probabilistic component. This is IKW's explanation of the interrogative
left-argument restriction (§5.2). -/
theorem fullSupport_fails_unbelieved {W : Type*} [Fintype W]
    (dox : InfoState W) (sentDen : Issue W) (prior : Prior W)
    (answer : W → Bool) (worlds : List W)
    (hNoBelief : ∀ q, q ∈ sentDen.alternatives →
      supports dox q worlds = false) :
    fullSupport dox sentDen prior answer worlds = false := by
  unfold fullSupport
  rw [List.any_eq_false]
  intro q hMem
  rw [hNoBelief q hMem]
  simp

/-- Anti-support implies non-support: if evidence lowers P(α), it certainly
doesn't raise it.

This captures the key asymmetry between *but* and discourse *only*:
*but* requires `negRelevant` (anti-support / BF < 1), while discourse *only*
only requires `¬probSupports` (failure to support). Since anti-support implies
non-support, *but*'s condition is strictly stronger. -/
theorem probAntiSupports_implies_not_probSupports {W : Type*} [Fintype W]
    (prior : Prior W) (evidence answer : W → Bool)
    (h : probAntiSupports prior evidence answer = true) :
    probSupports prior evidence answer = false := by
  simp only [probAntiSupports, isNegativeEvidence, probSupports, isPositiveEvidence,
    decide_eq_true_eq, decide_eq_false_iff_not] at *
  linarith

end Semantics.Questions.Support
