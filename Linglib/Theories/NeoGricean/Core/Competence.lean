/-
# Neo-Gricean Pragmatics: Competence

Detailed competence analysis from Geurts (2010) Chapter 2.3.

## Key Concepts

1. **Competence** (basic): Bel_S(ψ) ∨ Bel_S(¬ψ)
   Speaker knows whether ψ.

2. **Competence+** (Soames 1982): Bel_S(ψ) ↔ ψ
   Speaker's belief matches truth. Stronger than basic competence.

3. **Disjunction Blocks Competence**
   For "A or B", competence about A leads to contradiction via Quality.

4. **Three-Way Outcome** (p.40)
   - Weak only (undecided)
   - Strong (competence holds)
   - No opinion (competence rejected)

Reference: Geurts, B. (2010). Quantity Implicatures. Cambridge University Press.
-/

import Linglib.Theories.NeoGricean.Core.Basic

namespace NeoGricean.Competence

open NeoGricean

-- ============================================================================
-- PART 1: Competence+ (Soames 1982)
-- ============================================================================

/--
Competence+ (Soames 1982): Speaker's belief matches truth.

This is stronger than basic competence:
- Basic: Bel_S(ψ) ∨ Bel_S(¬ψ) (speaker has an opinion)
- Plus: Bel_S(ψ) ↔ ψ (speaker's opinion is correct)

Competence+ entails basic competence, but not vice versa.
-/
def competencePlus (truth : Bool) (b : BeliefState) : Bool :=
  match truth, b with
  | true, .belief => true      -- ψ true and speaker believes ψ
  | false, .disbelief => true  -- ψ false and speaker believes ¬ψ
  | _, _ => false

/--
**Theorem: Competence+ Implies Basic Competence**

If Competence+ holds, basic competence holds.
-/
theorem competence_plus_implies_basic :
    ∀ (truth : Bool) (b : BeliefState),
      competencePlus truth b = true → competent b = true := by
  intro truth b h
  cases truth <;> cases b <;> simp [competencePlus, competent] at *

/--
**Theorem: Basic Competence Doesn't Imply Competence+**

A speaker can be competent (have an opinion) but wrong.
-/
theorem basic_not_implies_plus :
    ∃ (truth : Bool) (b : BeliefState),
      competent b = true ∧ competencePlus truth b = false := by
  -- Speaker believes ψ when ψ is actually false
  exact ⟨false, .belief, by native_decide⟩

-- ============================================================================
-- PART 2: Disjunction and Competence
-- ============================================================================

/--
Represents a disjunction "A or B" with speaker's epistemic state.

For disjunctions, the standard competence assumption leads to problems.
If speaker is competent about A (knows whether A):
- Case 1: Bel_S(A) → but then why say "A or B"? (Quality violation)
- Case 2: Bel_S(¬A) → combined with "A or B" means Bel_S(B)

This explains why disjunction triggers IGNORANCE implicatures,
not scalar implicatures.
-/
structure DisjunctionState where
  /-- Speaker's belief about A -/
  beliefA : BeliefState
  /-- Speaker's belief about B -/
  beliefB : BeliefState
  deriving Repr

/--
Check if the speaker is competent about both disjuncts.
-/
def competentAboutBoth (d : DisjunctionState) : Bool :=
  competent d.beliefA && competent d.beliefB

/--
Check if saying "A or B" is consistent with Quality maxim.

Quality: Don't say what you believe to be false.
If speaker believes A is true, saying "A or B" is misleading.
If speaker believes B is true, saying "A or B" is misleading.
-/
def qualityConsistent (d : DisjunctionState) : Bool :=
  -- Speaker shouldn't believe exactly one is true
  -- (that would make "A or B" misleading)
  match d.beliefA, d.beliefB with
  | .belief, .disbelief => false  -- Knows A, not B → should say "A"
  | .disbelief, .belief => false  -- Knows B, not A → should say "B"
  | .belief, .belief => false     -- Knows both → should say "A and B"
  | _, _ => true

/--
**Theorem: Competence About Both Disjuncts Violates Quality**

If the speaker is competent about both A and B, and "A or B" is asserted,
Quality is likely violated (speaker should have been more specific).
-/
theorem disjunction_blocks_full_competence :
    ∀ d : DisjunctionState,
      competentAboutBoth d = true → qualityConsistent d = true →
      -- Only remaining case: both believed false (but then assertion is false!)
      d.beliefA = .disbelief ∧ d.beliefB = .disbelief := by
  intro ⟨beliefA, beliefB⟩ hcomp hqual
  cases beliefA <;> cases beliefB <;>
    simp [competentAboutBoth, competent, qualityConsistent] at *

/--
**Theorem: Disjunction Suggests Ignorance**

If "A or B" is asserted consistently with Quality, speaker lacks
full competence about both disjuncts.

Specifically: speaker doesn't believe exactly one disjunct is true.
-/
theorem disjunction_implies_partial_ignorance :
    ∀ d : DisjunctionState,
      qualityConsistent d = true →
      ¬(d.beliefA = .belief ∧ d.beliefB = .disbelief) ∧
      ¬(d.beliefA = .disbelief ∧ d.beliefB = .belief) ∧
      ¬(d.beliefA = .belief ∧ d.beliefB = .belief) := by
  intro ⟨beliefA, beliefB⟩ hqual
  cases beliefA <;> cases beliefB <;>
    simp [qualityConsistent] at hqual <;>
    simp_all

-- ============================================================================
-- PART 3: Three-Way Outcome in Detail
-- ============================================================================

/--
Detailed outcome of implicature processing, including the reason.
-/
structure ImplicatureProcessing where
  /-- The belief state inferred -/
  beliefState : BeliefState
  /-- Whether weak implicature ¬Bel_S(ψ) holds -/
  weakHolds : Bool
  /-- Whether competence was assumed -/
  competenceAssumed : Bool
  /-- Whether strong implicature Bel_S(¬ψ) was derived -/
  strongDerived : Bool
  deriving Repr

/--
Process an alternative given competence assumption.
-/
def processAlternative (assumeCompetence : Bool) (b : BeliefState) : ImplicatureProcessing :=
  { beliefState := b
  , weakHolds := nonBelief b
  , competenceAssumed := assumeCompetence && competent b
  , strongDerived := assumeCompetence && strongImpl b
  }

/--
**Theorem: Outcome i (Undecided)**

When competence is not assumed, only weak implicature holds.
-/
theorem outcome_i_undecided :
    ∀ b : BeliefState,
      b ≠ .belief →
      let p := processAlternative false b
      p.weakHolds = true ∧ p.strongDerived = false := by
  intro b hne
  cases b <;> simp_all [processAlternative, nonBelief]

/--
**Theorem: Outcome ii (Strong)**

When competence is assumed and speaker disbelieves,
strong implicature is derived.
-/
theorem outcome_ii_strong :
    let p := processAlternative true .disbelief
    p.weakHolds = true ∧ p.competenceAssumed = true ∧ p.strongDerived = true := by
  native_decide

/--
**Theorem: Outcome iii (Incompetent)**

When speaker has no opinion, competence assumption fails,
only weak implicature holds.
-/
theorem outcome_iii_incompetent :
    let p := processAlternative true .noOpinion
    p.weakHolds = true ∧ p.competenceAssumed = false ∧ p.strongDerived = false := by
  native_decide

-- ============================================================================
-- PART 4: Competence in Context
-- ============================================================================

/--
Factors that affect whether competence is assumed.

Following Geurts' discussion, competence is more likely assumed when:
- The proposition is simple/common knowledge
- The speaker is an authority on the topic
- Context suggests speaker should know

Competence is BLOCKED for disjunctions due to Quality interaction.
-/
inductive CompetenceContext where
  | simpleAssertion  -- Default: competence assumed
  | disjunction      -- Competence blocked by Quality
  | authority        -- Strong competence assumption
  | uncertain        -- Weak competence assumption
  deriving DecidableEq, BEq, Repr

/--
Should competence be assumed in this context?
-/
def shouldAssumeCompetence : CompetenceContext → Bool
  | .simpleAssertion => true
  | .disjunction => false      -- Key insight: disjunction blocks competence
  | .authority => true
  | .uncertain => false

/--
**Theorem: Disjunction Context Blocks Competence**

In disjunction context, we don't assume competence,
so only weak implicatures (ignorance) arise.
-/
theorem disjunction_context_weak_only :
    shouldAssumeCompetence .disjunction = false := by
  rfl

-- ============================================================================
-- PART 5: Summary
-- ============================================================================

/-
## What This Module Provides

### Types
- `DisjunctionState`: Epistemic state for "A or B"
- `ImplicatureProcessing`: Detailed processing result
- `CompetenceContext`: Factors affecting competence assumption

### Competence Variants
- `competent`: Basic competence (Bel(ψ) ∨ Bel(¬ψ))
- `competencePlus`: Soames' stronger version (Bel(ψ) ↔ ψ)

### Key Theorems
- `competence_plus_implies_basic`: Plus → basic
- `basic_not_implies_plus`: Basic ↛ plus
- `disjunction_blocks_full_competence`: Full competence + Quality → contradiction
- `disjunction_implies_partial_ignorance`: Disjunction → ignorance

### Three Outcomes
- `outcome_i_undecided`: No competence → weak only
- `outcome_ii_strong`: Competence + disbelief → strong
- `outcome_iii_incompetent`: No opinion → competence fails

### Connection to Geurts (2010)
- Ch. 2.3 (p.40-41): Three outcomes
- Ch. 3.3 (p.61): Disjunction blocks competence
-/

end NeoGricean.Competence
