import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval

/-! # Scontras & Tonhauser (2025)

Projection emerges from RSA over speaker's private assumptions, not lexical
presupposition. L1 infers what speaker takes for granted (dcS in F&B terms).
-/

namespace RSA.ScontrasTonhauser2025


/--
World state: tracks belief and complement truth.

⟨BEL, C⟩ where:
- BEL: Cole believes the complement
- C: The complement is actually true
-/
structure WorldState where
  bel : Bool  -- Cole believes C
  c : Bool    -- C is true
  deriving DecidableEq, Repr, BEq, Inhabited

/-- All four world states -/
def allWorlds : List WorldState := [
  ⟨true, true⟩,   -- Cole believes C, C is true
  ⟨true, false⟩,  -- Cole believes C, C is false
  ⟨false, true⟩,  -- Cole doesn't believe C, C is true
  ⟨false, false⟩  -- Cole doesn't believe C, C is false
]


/--
Attitude verb utterances about Cole's mental state.
-/
inductive Utterance where
  | knowPos     -- "Cole knows that C"
  | knowNeg     -- "Cole doesn't know that C"
  | thinkPos    -- "Cole thinks that C"
  | thinkNeg    -- "Cole doesn't think that C"
  deriving DecidableEq, Repr, BEq, Inhabited

def allUtterances : List Utterance := [.knowPos, .knowNeg, .thinkPos, .thinkNeg]


/--
Literal truth conditions.

"know" is factive: requires both belief AND truth
"think" is non-factive: requires only belief
-/
def literalMeaning : Utterance → WorldState → Bool
  -- "Cole knows C" = Cole believes C AND C is true
  | .knowPos, w => w.bel && w.c
  -- "Cole doesn't know C" = NOT (Cole believes C AND C is true)
  | .knowNeg, w => !(w.bel && w.c)
  -- "Cole thinks C" = Cole believes C
  | .thinkPos, w => w.bel
  -- "Cole doesn't think C" = Cole doesn't believe C
  | .thinkNeg, w => !w.bel

/-- "know" entails C -/
theorem know_entails_c : ∀ w, literalMeaning .knowPos w = true → w.c = true := by
  intro ⟨bel, c⟩ h
  simp [literalMeaning] at h
  exact h.2

/-- "think" does NOT entail C -/
theorem think_not_entails_c : ∃ w, literalMeaning .thinkPos w = true ∧ w.c = false := by
  use ⟨true, false⟩
  simp [literalMeaning]


/--
Two possible QUDs:
- BEL?: Is Cole's belief state the question?
- C?: Is the complement truth the question?
-/
inductive QUD where
  | bel   -- "Does Cole believe C?"
  | c     -- "Is C true?"
  deriving DecidableEq, Repr, BEq, Inhabited

def allQUDs : List QUD := [.bel, .c]

/--
QUD projection: two worlds are equivalent if they agree on the QUD dimension.
-/
def qudProject : QUD → WorldState → WorldState → Bool
  | .bel, w1, w2 => w1.bel == w2.bel  -- Same belief state
  | .c, w1, w2 => w1.c == w2.c        -- Same complement truth


/--
Speaker's private assumptions: a non-empty subset of worlds.

We represent this as a named subset for efficiency.
In the paper, A ranges over all non-empty subsets of W.
-/
inductive BeliefState where
  | all           -- Speaker considers all worlds possible
  | cTrue         -- Speaker assumes C is true: {⟨1,1⟩, ⟨0,1⟩}
  | cFalse        -- Speaker assumes C is false: {⟨1,0⟩, ⟨0,0⟩}
  | belTrue       -- Speaker assumes Cole believes: {⟨1,1⟩, ⟨1,0⟩}
  | belFalse      -- Speaker assumes Cole doesn't believe: {⟨0,1⟩, ⟨0,0⟩}
  | cTrueBelTrue  -- {⟨1,1⟩}
  | cTrueBelFalse -- {⟨0,1⟩}
  | cFalseBelTrue -- {⟨1,0⟩}
  | cFalseBelFalse -- {⟨0,0⟩}
  deriving DecidableEq, Repr, BEq, Inhabited

def allBeliefStates : List BeliefState := [
  .all, .cTrue, .cFalse, .belTrue, .belFalse,
  .cTrueBelTrue, .cTrueBelFalse, .cFalseBelTrue, .cFalseBelFalse
]

/--
Membership in belief state (as credence).
-/
def speakerCredenceBool : BeliefState → WorldState → Bool
  | .all, _ => true
  | .cTrue, w => w.c
  | .cFalse, w => !w.c
  | .belTrue, w => w.bel
  | .belFalse, w => !w.bel
  | .cTrueBelTrue, w => w.c && w.bel
  | .cTrueBelFalse, w => w.c && !w.bel
  | .cFalseBelTrue, w => !w.c && w.bel
  | .cFalseBelFalse, w => !w.c && !w.bel

def speakerCredence : BeliefState → WorldState → ℚ :=
  λ a w => boolToRat (speakerCredenceBool a w)

/--
Whether C is true in all worlds of the belief state.
This is what it means for C to be "assumed" by the speaker.
-/
def assumesC : BeliefState → Bool
  | .cTrue => true
  | .cTrueBelTrue => true
  | .cTrueBelFalse => true
  | _ => false


/--
World prior parameterized by P(C).

P(BEL, C) = P(BEL | C) · P(C)

We assume P(BEL | C) is uniform for simplicity.
-/
def worldPrior (pC : ℚ) : WorldState → ℚ
  | ⟨_, true⟩ => pC / 2      -- C true, split between bel/not-bel
  | ⟨_, false⟩ => (1 - pC) / 2  -- C false, split between bel/not-bel

/--
Belief state prior following Section 4 of Scontras & Tonhauser (2025):
- Knowledge of C is 4× as likely as knowledge of BEL
- Full knowledge (singletons) is 0.5× as likely as knowledge of BEL
- No beliefs (all) is 0.5× as likely as singletons

This captures that speakers more often have knowledge about C than about BEL.
-/
def beliefStatePrior : BeliefState → ℚ
  | .all => 1/4           -- No beliefs: 0.25 (half of singletons)
  | .cTrue => 4           -- Knowledge of C: 4× base
  | .cFalse => 4          -- Knowledge of C: 4× base
  | .belTrue => 1         -- Knowledge of BEL: 1 (base)
  | .belFalse => 1        -- Knowledge of BEL: 1 (base)
  | _ => 1/2              -- Singletons: 0.5 (half of knowledge of BEL)


/--
Projection strength (world-based): P(C=true | utterance, QUD)

This is the PRIMARY measure used in the paper (Section 3.1, footnote 11):
"We evaluate the predictions of our model based on the marginal posterior
probability of w, specifically, those w in which C is true."
-/
def projectionOfC_world (pC : ℚ) (u : Utterance) (q : QUD) (alpha : ℕ := 10) : ℚ :=
  -- Get L1 distribution over worlds GIVEN the QUD
  let worldDist := RSA.Eval.L1_world_givenGoal
    allUtterances allWorlds [()] [()] allBeliefStates allQUDs
    (λ _ _ u' w => if literalMeaning u' w then 1 else 0)
    (worldPrior pC) (λ _ => 1) (λ _ => 1) beliefStatePrior (λ _ => 1)
    speakerCredence qudProject (λ _ => 0) alpha u q
  -- Sum probability of worlds where C is true
  worldDist.foldl (λ acc (w, p) =>
    if w.c then acc + p else acc) 0

/--
Projection strength (belief-based): P(speaker assumes C | utterance, QUD)

Alternative measure (footnote 11): "if we evaluated its predictions based on
the marginal posterior probability of A, specifically those A that entail C."
-/
def projectionOfC_belief (pC : ℚ) (u : Utterance) (q : QUD) (alpha : ℕ := 10) : ℚ :=
  -- Get L1 distribution over belief states GIVEN the QUD
  let beliefDist := RSA.Eval.L1_beliefState_givenGoal
    allUtterances allWorlds [()] [()] allBeliefStates allQUDs
    (λ _ _ u' w => if literalMeaning u' w then 1 else 0)
    (worldPrior pC) (λ _ => 1) (λ _ => 1) beliefStatePrior (λ _ => 1)
    speakerCredence qudProject (λ _ => 0) alpha u q
  -- Sum probability of states that assume C
  beliefDist.foldl (λ acc (a, p) =>
    if assumesC a then acc + p else acc) 0

/-- Default projection function uses world-based measure (as in paper). -/
def projectionOfC (pC : ℚ) (u : Utterance) (q : QUD) : ℚ :=
  projectionOfC_world pC u q


/--
**Prediction (a)**: "know" projects more strongly than "think".

The entailment in "know" biases L1 toward belief states where C is true.

NOTE: The paper measures projection for NEGATED utterances ("doesn't know C",
"doesn't think C") because negation tests whether the complement projects.
-/
def prediction_know_gt_think (pC : ℚ) (q : QUD) : Bool :=
  projectionOfC pC .knowNeg q > projectionOfC pC .thinkNeg q

/--
**Prediction (b)**: Higher prior → stronger projection.

When P(C) is high, listener more readily infers speaker assumes C.
-/
def prediction_prior_effect (u : Utterance) (q : QUD) : Bool :=
  -- Projection with high prior > projection with low prior
  projectionOfC (3/4) u q > projectionOfC (1/4) u q

/--
**Prediction (c)**: C-at-issue → weaker projection.

When QUD = C?, the complement is at-issue, so less projection.
-/
def prediction_qud_effect (pC : ℚ) (u : Utterance) : Bool :=
  -- Projection under BEL? > projection under C?
  projectionOfC pC u .bel > projectionOfC pC u .c


-- Uncomment to evaluate predictions
-- #eval prediction_know_gt_think (1/2) .bel
-- #eval prediction_prior_effect .knowPos .bel
-- #eval prediction_qud_effect (1/2) .knowPos


end RSA.ScontrasTonhauser2025
