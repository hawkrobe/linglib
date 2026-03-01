import Linglib.Theories.Pragmatics.RelevanceTheory.Comprehension
import Linglib.Phenomena.ScalarImplicatures.Basic

/-!
# Bridge: Relevance Theory → Scalar Implicatures

RT derives scalar implicatures through BOTH components of the theory:

1. **Comprehension procedure (clause a)**: the enriched "some but not all"
   interpretation is selected over the literal "at least some" because it
   produces more cognitive effects. The literal reading fails the relevance
   threshold — it's too weak for an optimally relevant stimulus.

2. **Clause (b) reasoning**: the speaker chose "some" over "all". Since "all"
   would have been more relevant (more informative, same effort), the hearer
   infers the speaker wasn't in a position to say "all" — deriving
   ¬Bel_S(all) (weak) or Bel_S(¬all) (strong, with competence).

3. **DE blocking**: in downward-entailing contexts, pragmatic enrichment
   ("not all") doesn't produce additional cognitive effects — narrowing
   "some" to "some but not all" actually WEAKENS the overall DE claim.
   The literal reading suffices, so the procedure stops there.

## RT vs NeoGricean

Both derive "some → not all", but by different mechanisms:
- **NeoGricean**: Horn scales + Standard Recipe (Q-principle generates,
  R-principle constrains). The scale ⟨some, all⟩ is a grammatical object.
- **RT**: Comprehension procedure + clause (b). No scales needed — the
  implicature follows from the general presumption of optimal relevance.

-/

set_option autoImplicit false

namespace Phenomena.ScalarImplicatures.Bridge.RelevanceTheory

open Theories.Pragmatics.RelevanceTheory
open Phenomena.ScalarImplicatures

-- ============================================================================
-- §1. Candidate Interpretations
-- ============================================================================

/-- Candidate interpretations for a scalar utterance like "Some students passed".
    The comprehension procedure considers these in order of accessibility. -/
inductive SIInterpretation where
  /-- Lower-bound (literal): "at least some", compatible with all -/
  | lowerBound
  /-- Pragmatically enriched: "some but not all" -/
  | enriched
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §2. UE Context: Implicature Arises
-- ============================================================================

/-- RT scenario for "Some students passed" in an upward-entailing context.

    - Lower-bound is more accessible (decoded semantic content, tried first)
    - But it fails the relevance threshold: an optimally relevant speaker who
      knew all students passed would have said "all" — so the mere lower-bound
      reading doesn't produce enough cognitive effects
    - The enriched reading produces more effects: "some passed" + "not all
      passed" + information about the speaker's epistemic state
    - The enriched reading is selected as the first acceptable interpretation -/
def somePassedUE : RTScenario SIInterpretation :=
  { candidates := [.lowerBound, .enriched]
  , accessibility := fun | .lowerBound => 1 | .enriched => 2
  , effects := fun | .lowerBound => 1 | .enriched => 3
  , effort := fun | .lowerBound => 0 | .enriched => 1
  , threshold := 2
  , effortWeight := 0
  }

/-- The comprehension procedure selects the enriched interpretation in UE.

    The literal reading fails its threshold (1 < 2), so the procedure moves
    on. The enriched reading passes (3 ≥ 2), so it's accepted. -/
theorem ue_selects_enriched :
    somePassedUE.comprehensionSelects .enriched := by
  refine ⟨List.Mem.tail _ (List.Mem.head _), ?_, ?_⟩
  · -- adjustedThreshold .enriched ≤ effects .enriched: 2 ≤ 3
    show somePassedUE.threshold + somePassedUE.effortWeight * somePassedUE.effort .enriched ≤ 3
    simp [somePassedUE]
  · -- Every more accessible candidate fails its threshold
    intro j hj hacc
    simp only [somePassedUE, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl
    · -- j = .lowerBound: effects 1 < adjustedThreshold 2
      show 1 < somePassedUE.threshold + somePassedUE.effortWeight * somePassedUE.effort .lowerBound
      simp [somePassedUE]
    · -- j = .enriched: accessibility 2 < 2, contradiction
      simp [somePassedUE] at hacc

/-- The literal reading is subthreshold: it doesn't produce enough effects
    to justify processing an optimally relevant stimulus.

    This is key to RT's account: the literal "at least some" is REJECTED
    not because it's false but because it's insufficiently informative. -/
theorem ue_literal_subthreshold :
    somePassedUE.effects .lowerBound < somePassedUE.adjustedThreshold .lowerBound := by
  simp [somePassedUE, RTScenario.adjustedThreshold]

-- ============================================================================
-- §3. DE Context: Implicature Blocked
-- ============================================================================

/-- RT scenario for "some" in a downward-entailing context
    (e.g., "No one ate some of the cookies").

    In DE contexts, enriching "some" to "some but not all" does NOT produce
    additional cognitive effects — narrowing the restrictor of a DE operator
    weakens the overall claim, which is the opposite of being informative.
    The literal reading suffices: it's already informative enough. -/
def somePassedDE : RTScenario SIInterpretation :=
  { candidates := [.lowerBound, .enriched]
  , accessibility := fun | .lowerBound => 1 | .enriched => 2
  , effects := fun | .lowerBound => 2 | .enriched => 2
  , effort := fun | .lowerBound => 0 | .enriched => 1
  , threshold := 2
  , effortWeight := 0
  }

/-- The comprehension procedure selects the literal reading in DE.

    The literal reading passes its threshold (2 ≥ 2) and is the most
    accessible candidate, so the procedure stops immediately. The enriched
    reading is never even considered — satisficing, not optimizing. -/
theorem de_selects_literal :
    somePassedDE.comprehensionSelects .lowerBound := by
  refine ⟨List.Mem.head _, ?_, ?_⟩
  · show somePassedDE.threshold + somePassedDE.effortWeight * somePassedDE.effort .lowerBound ≤ 2
    simp [somePassedDE]
  · -- No candidate is more accessible than .lowerBound (accessibility 1)
    intro j hj hacc
    simp only [somePassedDE, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl <;> simp [somePassedDE] at hacc

-- ============================================================================
-- §4. Processing Effort Argument
-- ============================================================================

/-- Processing effort can block enrichment even when effects are present.

    When the pragmatic enrichment is costly (e.g., in rapid conversational
    exchange, or when the context doesn't readily supply the enriched reading),
    the effort-adjusted threshold rises above the enriched reading's effects.

    The literal reading is selected because the enriched one isn't "worth the
    effort" — a distinctive RT argument with no NeoGricean counterpart. -/
def somePassedHighEffort : RTScenario SIInterpretation :=
  { candidates := [.lowerBound, .enriched]
  , accessibility := fun | .lowerBound => 1 | .enriched => 2
  , effects := fun | .lowerBound => 2 | .enriched => 3
  , effort := fun | .lowerBound => 0 | .enriched => 3
  , threshold := 2
  , effortWeight := 1
  }

/-- When effort is high, the literal reading is selected despite the
    enriched reading having more raw effects. -/
theorem effort_selects_literal :
    somePassedHighEffort.comprehensionSelects .lowerBound := by
  refine ⟨List.Mem.head _, ?_, ?_⟩
  · show somePassedHighEffort.threshold +
        somePassedHighEffort.effortWeight * somePassedHighEffort.effort .lowerBound ≤ 2
    simp [somePassedHighEffort]
  · intro j hj hacc
    simp only [somePassedHighEffort, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl <;> simp [somePassedHighEffort] at hacc

/-- The enriched reading is blocked by effort: it would pass at zero effort
    (threshold 2 ≤ effects 3) but the effort-adjusted threshold (2 + 1*3 = 5)
    exceeds its effects (3). -/
theorem enriched_blocked_by_effort :
    somePassedHighEffort.blockedByEffort .enriched := by
  constructor
  · -- threshold ≤ effects: 2 ≤ 3
    show somePassedHighEffort.threshold ≤ 3
    simp [somePassedHighEffort]
  · -- effects < adjustedThreshold: 3 < 5
    show 3 < somePassedHighEffort.threshold +
        somePassedHighEffort.effortWeight * somePassedHighEffort.effort .enriched
    simp [somePassedHighEffort]

-- ============================================================================
-- §5. Clause (b): Speaker's Alternatives
-- ============================================================================

/-- Clause (b) argument for the "some → not all" implicature.

    The speaker said "some" rather than "all". Since "all" would have been
    more relevant (more informative, similar effort), clause (b) of optimal
    relevance lets the hearer infer that the speaker wasn't able or willing
    to say "all".

    - Weak implicature: ¬Bel_S(all) — follows from clause (b) alone
    - Strong implicature: Bel_S(¬all) — requires additional competence
      assumption (speaker is opinionated about "all")

    This mechanism doesn't require Horn scales — any case where a more
    informative alternative was available triggers the same reasoning. -/
def someNotAllClauseB : ClauseBArgument String :=
  { actual := "some"
  , alternative := "all"
  , alternativeMoreRelevant := True
  , communicatorConstraint := True
  }

/-- The or/and clause (b) argument follows the same pattern. -/
def orNotAndClauseB : ClauseBArgument String :=
  { actual := "or"
  , alternative := "and"
  , alternativeMoreRelevant := True
  , communicatorConstraint := True
  }

/-- The possible/necessary clause (b) argument. -/
def possibleNotNecessaryClauseB : ClauseBArgument String :=
  { actual := "possible"
  , alternative := "necessary"
  , alternativeMoreRelevant := True
  , communicatorConstraint := True
  }

-- ============================================================================
-- §6. Bridge Theorems: RT Predictions Match Data
-- ============================================================================

/-- RT predicts that scalar implicature arises in UE contexts.
    The comprehension procedure selects the enriched reading, matching
    the empirical observation that "some" implicates "not all" in UE. -/
theorem rt_predicts_ue_implicature :
    somePassedUE.comprehensionSelects .enriched ∧
    someAllBlocking.implicatureInUE = true :=
  ⟨ue_selects_enriched, rfl⟩

/-- RT predicts that scalar implicature is blocked in DE contexts.
    The comprehension procedure selects the literal reading, matching
    the empirical observation that "some" does NOT implicate "not all" in DE. -/
theorem rt_predicts_de_blocking :
    somePassedDE.comprehensionSelects .lowerBound ∧
    someAllBlocking.implicatureInDE = false :=
  ⟨de_selects_literal, rfl⟩

/-- RT's effort mechanism is consistent with the weak/strong distinction:
    the weak implicature (¬Bel_S(all)) comes from clause (b) alone, while
    the strong (Bel_S(¬all)) requires a competence assumption.

    Data confirms: weak does not require competence, strong does. -/
theorem rt_matches_weak_strong :
    someStudents.weakRequiresCompetence = false ∧
    someStudents.strongRequiresCompetence = true := by
  exact ⟨rfl, rfl⟩

end Phenomena.ScalarImplicatures.Bridge.RelevanceTheory
