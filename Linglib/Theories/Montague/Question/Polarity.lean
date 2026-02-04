import Linglib.Theories.Montague.Question.DecisionTheory
import Linglib.Theories.Montague.Core.Polarity

/-!
# Questions/Polarity.lean

Van Rooy & Šafářová (2003) Decision-Theoretic Account of Polar Question Choice.

## The Problem

Standard G&S/Hamblin semantics predicts that:
- PPQ: "Is Luke right?"
- NPQ: "Is Luke not right?"
- Alt: "Is Luke right or not?"

All have the same denotation: {q, ¬q}. But they're NOT interchangeable:
- "Will you marry me?" vs "Will you marry me or not?" (latter is rude)
- "Is it raining?" works after seeing wet jacket; "Is it raining or not?" is odd
- Rhetorical questions must be polar, not alternative

## The Solution

Question polarity choice depends on **utility of answers**:

| Question Type | Utility Condition |
|--------------|-------------------|
| PPQ (?q)     | UV(q) > UV(¬q)   |
| NPQ (?¬q)    | UV(¬q) > UV(q)   |
| Alt (?q∨¬q)  | UV(q) ≈ UV(¬q)   |

Two sources of utility:
1. **Goal-based**: UV(q) > UV(¬q) iff P(g|q) > P(g|¬q)
2. **Informativity**: UV(q) = inf(q) = -log P(q) (surprisal)

## Applications

- **Requests/Pleas**: Goal = questioned prop, so PPQ is forced
- **Conversation starters**: Positive answer more useful for goals
- **Rhetorical questions**: High prior for ¬q, but signal new evidence for q
- **Grounding questions**: Check surprising new information
- **Medical diagnosis**: Truth of ¬q helps reach diagnostic goal

## References

- Van Rooy & Šafářová (2003). On Polar Questions. SALT 13.
- Ladd (1981). Semantics and pragmatics of negative questions.
- Büring & Gunlogson (2000). Aren't positive and negative polar questions the same?
-/

namespace Montague.Question.Polarity

open Montague.Question

-- Polar Question Types

/-- The three types of polar questions (semantically equivalent, pragmatically distinct). -/
inductive PolarQuestionType where
  | positive     -- PPQ: "Is Luke right?"
  | negative     -- NPQ: "Is Luke not right?"
  | alternative  -- Alt: "Is Luke right or not?"
  deriving DecidableEq, Repr

/-- A polar question with its associated proposition and type. -/
structure PolarQuestion (W : Type*) where
  /-- The positive proposition -/
  prop : W -> Bool
  /-- The question type (positive, negative, or alternative) -/
  qtype : PolarQuestionType

namespace PolarQuestion

variable {W : Type*}

/-- All polar questions have the same G&S denotation: {q, ¬q}. -/
def toGSQuestion (pq : PolarQuestion W) : GSQuestion W :=
  polarQuestion pq.prop

/-- This is the key semantic equivalence that the pragmatic account explains. -/
theorem all_types_same_semantics (p : W -> Bool) :
    (PolarQuestion.mk p .positive).toGSQuestion =
    (PolarQuestion.mk p .negative).toGSQuestion ∧
    (PolarQuestion.mk p .positive).toGSQuestion =
    (PolarQuestion.mk p .alternative).toGSQuestion := by
  constructor <;> rfl

end PolarQuestion

-- Utility of Answers

/-- Utility value of learning proposition p is true.

For goal-based utility: UV(p) = P(g|p) - P(g)
For informativity: UV(p) = inf(p) = -log P(p)

We use a general definition: improvement in expected utility after conditioning. -/
def answerUtility {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (p : W -> Bool) : ℚ :=
  utilityValue dp worlds actions p

/-- Compare utility of positive vs negative answer. -/
def compareUtility {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (p : W -> Bool) : Ordering :=
  let uvPos := answerUtility dp worlds actions p
  let uvNeg := answerUtility dp worlds actions (pnot p)
  if uvPos > uvNeg then .gt
  else if uvPos < uvNeg then .lt
  else .eq

-- Optimal Question Type Selection

/-- The Van Rooy & Šafářová criterion: choose question type based on answer utilities.

- PPQ if UV(q) > UV(¬q)
- NPQ if UV(¬q) > UV(q)
- Alt if UV(q) ≈ UV(¬q) -/
def optimalQuestionType {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (p : W -> Bool) : PolarQuestionType :=
  match compareUtility dp worlds actions p with
  | .gt => .positive
  | .lt => .negative
  | .eq => .alternative

/-- Threshold-based comparison (for approximate equality). -/
def optimalQuestionTypeWithThreshold {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (p : W -> Bool) (threshold : ℚ) : PolarQuestionType :=
  let uvPos := answerUtility dp worlds actions p
  let uvNeg := answerUtility dp worlds actions (pnot p)
  let diff := uvPos - uvNeg
  if diff > threshold then .positive
  else if diff < -threshold then .negative
  else .alternative

-- Special Cases: Goal-Based Utility

/-- A decision problem where the agent has a single goal proposition.

U(w) = 1 if w ∈ g, 0 otherwise
Then EU(P,U) = P(g), and UV(q) = P(g|q) - P(g) -/
def goalBasedDP {W : Type*} (goal : W -> Bool) (prior : W -> ℚ) : DecisionProblem W Bool where
  utility w a := if a && goal w then 1 else 0
  prior := prior

/-- For goal-based utility: UV(q) > UV(¬q) iff P(g|q) > P(g|¬q). -/
def conditionalGoalProb {W : Type*}
    (goal : W -> Bool) (prior : W -> ℚ) (worlds : List W)
    (condition : W -> Bool) : ℚ :=
  let condWorlds := worlds.filter condition
  let totalProb := condWorlds.foldl (fun acc w => acc + prior w) 0
  if totalProb == 0 then 0
  else condWorlds.foldl (fun acc w =>
    acc + if goal w then prior w / totalProb else 0
  ) 0

/-- Goal probability advantage: P(g|q) - P(g|¬q). -/
def goalProbAdvantage {W : Type*}
    (goal : W -> Bool) (prior : W -> ℚ) (worlds : List W)
    (p : W -> Bool) : ℚ :=
  let pgGivenP := conditionalGoalProb goal prior worlds p
  let pgGivenNotP := conditionalGoalProb goal prior worlds (pnot p)
  pgGivenP - pgGivenNotP

/-- When goal = questioned proposition, PPQ is always optimal.

For requests like "Will you marry me?", g = q, so:
- P(g|q) = P(q|q) = 1
- P(g|¬q) = P(q|¬q) = 0
Thus UV(q) > UV(¬q) necessarily. -/
theorem request_forces_ppq {W : Type*}
    (p : W -> Bool) (prior : W -> ℚ) (worlds : List W)
    (hNonempty : worlds.length > 0) :
    goalProbAdvantage p prior worlds p >= 0 := by
  sorry -- P(p|p) = 1 >= P(p|¬p) = 0

-- Special Cases: Informativity-Based Utility

/-- Surprisal (negative log probability) of a proposition.

inf(q) = -log P(q)

Higher surprisal = lower probability = more informative if true.

Note: We approximate log with a rational function for computability. -/
def surprisal {W : Type*} (prior : W -> ℚ) (worlds : List W)
    (p : W -> Bool) : ℚ :=
  let prob := worlds.foldl (fun acc w => acc + if p w then prior w else 0) 0
  -- Approximation: surprisal ∝ 1/prob (for small probabilities)
  if prob == 0 then 1000  -- Very surprising
  else if prob >= 1 then 0  -- Not surprising
  else 1 / prob - 1  -- Monotonic in -log(prob)

/-- For informativity: UV(q) > UV(¬q) iff P(q) < P(¬q).

Less likely propositions are more informative when confirmed. -/
def informativenessAdvantage {W : Type*} (prior : W -> ℚ) (worlds : List W)
    (p : W -> Bool) : ℚ :=
  surprisal prior worlds p - surprisal prior worlds (pnot p)

/-- Givón's generalization: by default, positive propositions are less likely.

For most natural language statements q: P(q) < P(¬q)
This explains why PPQs are the default form of polar questions. -/
def positiveIsLessLikely {W : Type*} (prior : W -> ℚ) (worlds : List W)
    (p : W -> Bool) : Bool :=
  let pProb := worlds.foldl (fun acc w => acc + if p w then prior w else 0) 0
  let notPProb := worlds.foldl (fun acc w => acc + if !p w then prior w else 0) 0
  pProb < notPProb

-- Question Uses (Van Rooy & Šafářová Classification)

/-- Classification of polar question uses based on utility source. -/
inductive QuestionUse where
  /-- Goal = questioned prop (requests, pleas) -/
  | request
  /-- Goal is facilitated by positive answer (invitations) -/
  | invitation
  /-- Checking surprising new information -/
  | grounding
  /-- Drawing inferences from context -/
  | inference
  /-- Speaker indicates believed answer (rhetorical) -/
  | rhetorical
  /-- Pure information seeking with no bias -/
  | neutral
  deriving DecidableEq, Repr

/-- Expected question type for each use. -/
def expectedTypeForUse : QuestionUse -> PolarQuestionType
  | .request    => .positive  -- Goal = prop forces PPQ
  | .invitation => .positive  -- Positive answer helps goal
  | .grounding  => .positive  -- Checking unexpected positive info
  | .inference  => .positive  -- Following up on positive evidence
  | .rhetorical => .positive  -- Signal positive might be true after all
  | .neutral    => .alternative  -- No preference between answers

/-- For requests, alternative questions are pragmatically degraded.

"Will you marry me or not?" signals indifference to outcome,
which is inconsistent with a genuine request. -/
theorem request_disprefers_alt (use : QuestionUse) :
    use = .request -> expectedTypeForUse use ≠ .alternative := by
  intro h
  simp [h, expectedTypeForUse]

-- Negative Polar Questions

/-- When is a negative polar question appropriate?

NPQ (?¬q) requires UV(¬q) > UV(q), which can happen when:
1. Goal is reached by ¬q being true (medical diagnosis, ecological quiz)
2. Prior strongly favors q, so ¬q is more informative (tag questions) -/
def npqAppropriate {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (p : W -> Bool) : Bool :=
  compareUtility dp worlds actions p == .lt

/-- Example: Medical diagnosis questions.

"Is your child not eating?" is appropriate when:
- Goal: diagnose illness
- ¬(eating properly) is a symptom that helps diagnosis
- Thus P(diagnosis|¬eating) > P(diagnosis|eating) -/
def medicalDiagnosisDP {W : Type*}
    (_symptom illness : W -> Bool) (prior : W -> ℚ) : DecisionProblem W Bool where
  utility w a := if a && illness w then 1 else 0
  prior := prior

/-- For tag questions like "John isn't bad, is he?":
The speaker takes the declarative as likely true, making the tag's
positive prop (that John IS bad) low probability, hence informative. -/
def tagQuestionInformativity {W : Type*} (prior : W -> ℚ) (worlds : List W)
    (declarative tag : W -> Bool)
    (hDeclarativeIsNotTag : ∀ w, declarative w = !tag w)
    (hDeclarativeLikely : positiveIsLessLikely prior worlds tag) :
    informativenessAdvantage prior worlds tag > 0 := by
  sorry -- If tag is less likely, it's more informative

-- Alternative Questions

/-- Alternative questions are appropriate when utilities are balanced.

UV(q) ≈ UV(¬q) signals:
1. No preference for one answer over the other
2. Genuine information seeking without bias
3. Higher urgency (explicit enumeration of alternatives) -/
def altAppropriate {W A : Type*} [DecidableEq A]
    (dp : DecisionProblem W A) (worlds : List W) (actions : List A)
    (p : W -> Bool) (threshold : ℚ) : Bool :=
  let uvPos := answerUtility dp worlds actions p
  let uvNeg := answerUtility dp worlds actions (pnot p)
  let diff := uvPos - uvNeg
  -- Check if |diff| < threshold using rational comparison
  ((-threshold) < diff) && (diff < threshold)

/-- Alternative questions can be impolite as invitations.

"Do you want something to drink or not?" implies:
- Speaker doesn't care about hearer's preference
- Violates politeness by not encoding hearer's benefit -/
theorem alt_impolite_for_invitation :
    expectedTypeForUse .invitation = .positive := rfl

/-- Degrees of insistence in alternative questions:
1. "Did you buy it or not?"
2. "Did you buy it or didn't you?"
3. "Did you buy it or didn't you buy it?"
4. "Did you or did you not buy it?"

These have increasing insistence while maintaining UV(q) ≈ UV(¬q). -/
inductive AltInsistence where
  | minimal     -- "or not?"
  | contracted  -- "or didn't you?"
  | expanded    -- "or didn't you buy it?"
  | fronted     -- "Did you or did you not"
  deriving DecidableEq, Repr, Inhabited

-- Ladd's Inner/Outer Negation (Rejected)

/-!
## On Ladd's INPQ/ONPQ Distinction

Ladd (1981) distinguished:
- **INPQ** (inner negation): negation scopes narrowly, speaker expects negative answer
- **ONPQ** (outer negation): negation scopes widely, speaker expects positive answer

Van Rooy & Šafářová argue this distinction is **superfluous**:
- Both types involve UV(¬q) > UV(q)
- The difference is only whether it's goal-based or informativity-based utility

The German examples:
- "Gibt es kein vegetarisches Restaurant?" (INPQ reading possible)
- "Gibt es nicht ein vegetarisches Restaurant?" (only ONPQ reading)

Can be explained by whether the negation can bear verum focus (INPQ = checking
surprising negative info) or not (ONPQ = standard informativity-based NPQ).
-/

/-- We don't distinguish INPQ from ONPQ semantically.
The distinction is purely pragmatic (source of utility). -/
structure NPQAnalysis (W : Type*) where
  /-- The proposition being negated -/
  prop : W -> Bool
  /-- Whether utility is goal-based or informativity-based -/
  utilitySource : Bool  -- true = goal-based, false = informativity

/-- Both INPQ and ONPQ have the same semantic content. -/
def npqSemantics {W : Type*} (analysis : NPQAnalysis W) : GSQuestion W :=
  polarQuestion analysis.prop

-- Connection to Core Polarity

/-- Question polarity (positive/negative) connects to entailment polarity.

In an upward-entailing context, stronger propositions are preferred.
PPQ prefers the positive answer when it's more useful/informative.

This connects question pragmatics to scalar implicature contexts. -/
def questionPolarity (qtype : PolarQuestionType) : Option Montague.Core.Polarity.ContextPolarity :=
  match qtype with
  | .positive => some .upward    -- Positive proposition is "marked"
  | .negative => some .downward  -- Negative proposition is "marked"
  | .alternative => none         -- No polarity preference

-- Rhetorical Questions

/-- A rhetorical question is one where the speaker presupposes an answer
but uses question form for pragmatic effect.

Key insight: Rhetorical questions MUST be polar, not alternative.
"Are you crazy?" works rhetorically; "Are you crazy or not?" doesn't. -/
structure RhetoricalQuestion (W : Type*) where
  /-- The questioned proposition -/
  prop : W -> Bool
  /-- The presupposed answer (true = positive, false = negative) -/
  presupposedPositive : Bool
  /-- Speaker's evidence/belief strength -/
  beliefStrength : ℚ

/-- Rhetorical effect requires polar form.

The speaker:
1. Has high prior for one answer (say ¬q)
2. Uses question form to highlight that recent evidence suggests q
3. Alternative form would remove this highlighting effect -/
theorem rhetorical_requires_polar {W : Type*} (_rq : RhetoricalQuestion W) :
    expectedTypeForUse .rhetorical ≠ .alternative := by
  simp [expectedTypeForUse]

/-- Why rhetorical questions use PPQ form even when expecting negative answer:

Speaker signals: "I have new evidence for q, even though I believed ¬q"
This makes q surprising (high surprisal), thus high informativity.
PPQ highlights this surprising-if-true proposition. -/
def rhetoricalUsePPQ {W : Type*}
    (prior : W -> ℚ) (worlds : List W) (p : W -> Bool)
    (hPriorFavorsNegative : positiveIsLessLikely prior worlds p) :
    informativenessAdvantage prior worlds p > 0 := by
  sorry -- If p is less likely, learning p is more informative

-- Grounding Questions

/-- A grounding question checks whether surprising new information should be accepted.

"Is David back?" after being told David returned (unexpectedly).
"Is it raining?" after seeing someone with a wet jacket.

The speaker double-checks because:
- P(q) was very low in prior state
- New evidence suggests q might be true
- Accepting q would significantly revise beliefs -/
structure GroundingQuestion (W : Type*) where
  /-- The proposition to be grounded -/
  prop : W -> Bool
  /-- Prior probability before new evidence -/
  priorProb : ℚ
  /-- Posterior probability after new evidence -/
  posteriorProb : ℚ
  /-- Evidence must have increased probability -/
  hIncreased : posteriorProb > priorProb

/-- Grounding questions prefer polar form to highlight the surprising proposition. -/
theorem grounding_prefers_polar :
    expectedTypeForUse .grounding = .positive := rfl

/-- The utility of grounding: revision magnitude.

If accepting q causes large belief revision, double-checking has high utility. -/
def groundingUtility {W : Type*} (gq : GroundingQuestion W) : ℚ :=
  gq.posteriorProb - gq.priorProb

end Montague.Question.Polarity
