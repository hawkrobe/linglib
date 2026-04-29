import Linglib.Core.Word
import Linglib.Theories.Semantics.Entailment.Polarity

/-!
# Neo-Gricean Pragmatics: Basic Definitions

Core formalization of the Standard Recipe from @cite{geurts-2010} Chapter 2.

## Key Concepts

1. Belief States (Geurts p.39 diagram)
   - Belief: Bel_S(ψ)
   - Disbelief: Bel_S(¬ψ)
   - No Opinion: ¬Bel_S(ψ) ∧ ¬Bel_S(¬ψ)

2. Standard Recipe (Geurts p.32)
   The derivation mechanism for quantity implicatures:
   - Step 1: Speaker said φ
   - Step 2: There exists stronger alternative ψ
   - Step 3: Speaker didn't say ψ
   - Step 4: Therefore ¬Bel_S(ψ) (weak implicature)
   - Step 5: With competence, Bel_S(¬ψ) (strong implicature)

3. Competence Assumption
   Speaker knows whether ψ: Bel_S(ψ) ∨ Bel_S(¬ψ)

Reference: Geurts, B. (2010). Quantity Implicatures. Cambridge University Press.
-/

namespace Implicature


/--
Speaker's belief state about a proposition ψ.

Following Geurts' diagram on p.39:
- `belief`: Bel_S(ψ) — speaker believes ψ is true
- `disbelief`: Bel_S(¬ψ) — speaker believes ψ is false
- `noOpinion`: ¬Bel_S(ψ) ∧ ¬Bel_S(¬ψ) — speaker has no opinion
-/
inductive BeliefState where
  | belief      -- Bel_S(ψ)
  | disbelief   -- Bel_S(¬ψ)
  | noOpinion   -- ¬Bel_S(ψ) ∧ ¬Bel_S(¬ψ)
  deriving DecidableEq, Repr


/--
Competence: speaker knows whether ψ.
Formally: Bel_S(ψ) ∨ Bel_S(¬ψ)

A competent speaker is not agnostic — they have an opinion one way or the other.
-/
def competent : BeliefState → Bool
  | .belief => true
  | .disbelief => true
  | .noOpinion => false

/--
Non-belief: speaker doesn't believe ψ.
Formally: ¬Bel_S(ψ)

This is the weak implicature -- speaker might believe ¬ψ or have no opinion.
-/
def nonBelief : BeliefState → Bool
  | .belief => false
  | .disbelief => true
  | .noOpinion => true

/--
Strong implicature: speaker believes ¬ψ.
Formally: Bel_S(¬ψ)

This requires competence to derive from nonBelief.
-/
def strongImpl : BeliefState → Bool
  | .belief => false
  | .disbelief => true
  | .noOpinion => false


/--
The result of applying the Standard Recipe to an utterance.

- `weakImplicature`: ¬Bel_S(ψ) — always derivable from Quantity
- `competenceHolds`: Bel_S(ψ) ∨ Bel_S(¬ψ) — depends on context
- `strongImplicature`: Bel_S(¬ψ) — only if both weak + competence
-/
structure StandardRecipeResult where
  weakImplicature : Bool
  competenceHolds : Bool
  strongImplicature : Bool
  deriving Repr

/--
Apply the Standard Recipe to derive implicatures.

Given a belief state about the alternative ψ, determine what implicatures arise.
-/
def applyStandardRecipe (b : BeliefState) : StandardRecipeResult :=
  { weakImplicature := nonBelief b
  , competenceHolds := competent b
  , strongImplicature := strongImpl b
  }


/--
Theorem: Competence Strengthening

weak implicature + competence → strong implicature

If the speaker doesn't believe ψ (weak) AND is competent (knows whether ψ),
then the speaker must believe ¬ψ (strong).

Formally: ¬Bel_S(ψ) ∧ (Bel_S(ψ) ∨ Bel_S(¬ψ)) → Bel_S(¬ψ)
-/
theorem competence_strengthening :
    ∀ b : BeliefState, nonBelief b = true → competent b = true → strongImpl b = true := by
  intro b hweak hcomp
  cases b with
  | belief => simp [nonBelief] at hweak
  | disbelief => rfl
  | noOpinion => simp [competent] at hcomp

/--
Theorem: Weak Without Strong

A weak implicature can hold without the strong implicature
(when the speaker lacks competence).
-/
theorem weak_without_strong :
    ∃ b : BeliefState, nonBelief b = true ∧ strongImpl b = false := by
  exact ⟨.noOpinion, by native_decide⟩

/--
Theorem: Strong Implies Weak

If the strong implicature holds, the weak implicature holds.
Bel_S(¬ψ) → ¬Bel_S(ψ)
-/
theorem strong_implies_weak :
    ∀ b : BeliefState, strongImpl b = true → nonBelief b = true := by
  intro b hstrong
  cases b with
  | belief => simp [strongImpl] at hstrong
  | disbelief => rfl
  | noOpinion => simp [strongImpl] at hstrong

/--
Theorem: Strong Implies Competent

If the strong implicature holds, the speaker is competent.
Bel_S(¬ψ) → (Bel_S(ψ) ∨ Bel_S(¬ψ))
-/
theorem strong_implies_competent :
    ∀ b : BeliefState, strongImpl b = true → competent b = true := by
  intro b hstrong
  cases b with
  | belief => simp [strongImpl] at hstrong
  | disbelief => rfl
  | noOpinion => simp [strongImpl] at hstrong

/--
Theorem: No Belief Implies Weak Implicature

If the speaker doesn't believe ψ, the weak implicature holds.
This is direct from the definition.
-/
theorem no_belief_weak :
    ∀ b : BeliefState, b ≠ .belief → nonBelief b = true := by
  intro b h
  cases b with
  | belief => contradiction
  | disbelief => rfl
  | noOpinion => rfl


/--
Three possible outcomes for a hearer processing an implicature:

1. Undecided: Weak implicature only (¬Bel_S(ψ)), competence not assumed
2. Strong: Competence holds, derive Bel_S(¬ψ)
3. Incompetent: Competence rejected, speaker has no opinion

Following Geurts' discussion on p.40.
-/
inductive ImplicatureOutcome where
  | undecided       -- Only weak implicature, no competence assumption
  | strongInference -- Competence assumed, strong implicature derived
  | incompetent     -- Competence rejected, speaker is uncertain
  deriving DecidableEq, Repr

/--
Map a belief state to its implicature outcome.
-/
def outcomeOf : BeliefState → ImplicatureOutcome
  | .belief => .undecided      -- No implicature (speaker believes ψ)
  | .disbelief => .strongInference
  | .noOpinion => .incompetent

/--
Theorem: Outcomes are Exhaustive and Distinct

The three outcomes partition the space of competent/weak combinations.
-/
theorem outcomes_exhaustive :
    ∀ b : BeliefState,
      (outcomeOf b = .undecided ∧ nonBelief b = false) ∨
      (outcomeOf b = .strongInference ∧ strongImpl b = true) ∨
      (outcomeOf b = .incompetent ∧ nonBelief b = true ∧ competent b = false) := by
  intro b
  cases b with
  | belief => left; native_decide
  | disbelief => right; left; native_decide
  | noOpinion => right; right; native_decide


/--
When do scalar implicatures get triggered?

Both views are Neo-Gricean (pragmatic, maxim-based), but differ on triggering:
- Defaultism (Levinson): SIs fire by default, automatically
- Contextualism (Geurts): SIs depend on context (QUD, salience)

Reference:
- Levinson, S. (2000). Presumptive Meanings. MIT Press.
- Geurts, B. (2010). Quantity Implicatures. Ch. 5.
-/
inductive SITrigger where
  | default      -- Levinson: SIs fire automatically as presumptive meanings
  | contextual   -- Geurts: SIs depend on Question Under Discussion
  deriving DecidableEq, Repr

/--
Parameters that characterize a Neo-Gricean theory variant.
-/
structure NeoGriceanParams where
  /-- When do SIs get triggered? -/
  trigger : SITrigger
  /-- Is competence assumption enabled? -/
  competenceEnabled : Bool
  /-- Predicted baseline SI rate in neutral context (percentage) -/
  predictedNeutralRate : Nat
  deriving Repr

/--
Levinson's Defaultism: SIs are presumptive meanings that arise automatically.

Key claims:
- SIs are "default" inferences
- They arise rapidly and automatically
- Context can cancel them, but they're the default

Prediction: High SI rates (~90%+) even in neutral contexts.
-/
def levinsonParams : NeoGriceanParams :=
  { trigger := .default
  , competenceEnabled := true
  , predictedNeutralRate := 90  -- Expects high baseline
  }

/--
Geurts' Contextualism: SIs depend on the Question Under Discussion.

Key claims:
- SIs are not automatic defaults
- They arise when alternatives are contextually salient
- The QUD determines which alternatives matter

Prediction: Moderate SI rates (~35%) in truly neutral contexts;
asking about the SI raises salience and inflates rates.
-/
def geurtsParams : NeoGriceanParams :=
  { trigger := .contextual
  , competenceEnabled := true
  , predictedNeutralRate := 35  -- Expects lower baseline
  }

/--
Does this theory variant predict a task effect?

Contextualism predicts that asking "does this imply not-all?" will
raise SI rates by making the alternative salient.

Defaultism predicts no task effect since SIs are automatic.
-/
def predictsTaskEffect (p : NeoGriceanParams) : Bool :=
  match p.trigger with
  | .default => false     -- SIs automatic, asking shouldn't change rate
  | .contextual => true   -- Asking raises salience, inflates rate

/--
Does this theory variant predict high SI rates in neutral contexts?
-/
def predictsHighNeutralRate (p : NeoGriceanParams) : Bool :=
  p.predictedNeutralRate > 50


-- ============================================================
-- Word-driven NeoGricean Parsing
-- ============================================================

open Semantics.Entailment.Polarity (ContextPolarity) in
/-- Implicature's internal representation for implicature analysis.

    Bundles the Standard Recipe result with context information. -/
structure NeoGriceanStructure where
  /-- The Standard Recipe result (weak/strong implicature, competence) -/
  result : StandardRecipeResult
  /-- Context polarity (upward vs downward entailing) -/
  polarity : ContextPolarity
  /-- Position of the scalar item (if any) -/
  scalarPosition : Option Nat
  /-- Which variant of Implicature (for baseline rate) -/
  params : NeoGriceanParams := geurtsParams
  deriving Repr

/-- Check if a word is a scalar quantifier -/
def isScalarQuantifierWord (w : Word) : Bool :=
  w.form == "some" || w.form == "every" || w.form == "all" || w.form == "most"

/-- Find the position of a scalar item in a word list -/
def findScalarPositionInWords (ws : List Word) : Option Nat :=
  ws.findIdx? isScalarQuantifierWord

open Semantics.Entailment.Polarity (ContextPolarity) in
/-- Determine context polarity from words.
    Simplified: checks for negation markers. -/
def determinePolarityFromWords (ws : List Word) : ContextPolarity :=
  if ws.any (λ w => w.form == "no" || w.form == "not" || w.form == "never")
  then .downward
  else .upward

open Semantics.Entailment.Polarity (ContextPolarity) in
/-- Parse words into Implicature structure.

    For now, uses a simplified analysis:
    - Finds scalar item position
    - Determines polarity from negation markers
    - Assumes competence holds and derives strong implicature in UE -/
def parseToNeoGricean (ws : List Word) : Option NeoGriceanStructure :=
  let scalarPos := findScalarPositionInWords ws
  let polarity := determinePolarityFromWords ws
  let beliefState : BeliefState :=
    match scalarPos, polarity with
    | some _, .upward => .disbelief  -- Strong implicature in UE
    | some _, .downward => .noOpinion  -- Blocked in DE
    | some _, .nonMonotonic => .noOpinion  -- Blocked in NM
    | none, _ => .belief  -- No scalar item
  let result := applyStandardRecipe beliefState
  some { result := result
       , polarity := polarity
       , scalarPosition := scalarPos
       , params := geurtsParams
       }

end Implicature
