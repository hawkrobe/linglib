import Linglib.Theories.Pragmatics.Assertion.Krifka

/-!
# Krifka Bridge: Commitment Space Development (CSD) Tests
@cite{krifka-2015}

Worked examples exercising the tree-based commitment space operations
from Krifka (2015, §2–5). Each test uses a concrete 2-world model
(rain vs no rain) and verifies specific predictions about how assertions,
questions, acceptance, and rejection interact.

## Key Predictions Tested

1. Assertion narrows the CG (root changes immediately)
2. Questions preserve the CG (root unchanged)
3. Question-then-accept = assert (same CG)
4. Reject returns to pre-question state
5. Questions make settled spaces unsettled; acceptance re-settles
6. Bipolar questions create two continuations
7. Matching tags combine assertion + question bias

-/

namespace Phenomena.Assertion.Bridge.KrifkaCSD

open Theories.Pragmatics.Assertion.Krifka

-- ════════════════════════════════════════════════════
-- § 1. Finite World Setup
-- ════════════════════════════════════════════════════

/-- Two-world model: it's raining or it's not. -/
inductive Weather where | rain | noRain
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Proposition: it's raining. -/
private def isRaining : Weather → Bool
  | .rain => true
  | .noRain => false

/-- Proposition: it's NOT raining. -/
private def isNotRaining : Weather → Bool
  | .rain => false
  | .noRain => true

/-- Initial discourse state: empty commitments, settled space. -/
private def s₀ : KrifkaState Weather := KrifkaState.empty

-- ════════════════════════════════════════════════════
-- § 2. Assertion Tests
-- ════════════════════════════════════════════════════

/-- After asserting "it's raining", the root contains the rain
    proposition (the CG now reflects the assertion). -/
theorem assert_updates_root :
    (s₀.assert isRaining).space.root = [isRaining] := rfl

/-- After assertion, the rain-world is compatible with the CG. -/
theorem assert_rain_compatible :
    (s₀.assert isRaining).space.root.all (· .rain) = true := rfl

/-- After assertion, the no-rain-world is NOT compatible. -/
theorem assert_norain_excluded :
    (s₀.assert isRaining).space.root.all (· .noRain) = false := rfl

/-- Assertion preserves settledness: asserting into an empty (settled)
    space yields a settled space. -/
theorem assert_stays_settled :
    (s₀.assert isRaining).isStable = true := rfl

/-- The speaker's commitment slate records the assertion. -/
theorem assert_records_speaker :
    (s₀.assert isRaining).speakerCS.commitments = [isRaining] := rfl

/-- The addressee's slate is unchanged (they haven't accepted yet). -/
theorem assert_no_addressee_change :
    (s₀.assert isRaining).addresseeCS.commitments = [] := rfl

-- ════════════════════════════════════════════════════
-- § 3. Question Tests
-- ════════════════════════════════════════════════════

/-- After questioning "is it raining?", the root is unchanged
    (the CG is preserved — the question doesn't assert anything). -/
theorem question_preserves_root :
    (s₀.question isRaining).space.root = [] := rfl

/-- The question adds exactly one continuation (monopolar). -/
theorem question_one_continuation :
    (s₀.question isRaining).space.continuations.length = 1 := rfl

/-- The continuation contains the questioned proposition. -/
theorem question_continuation_content :
    (s₀.question isRaining).space.continuations = [[isRaining]] := rfl

/-- Questioning makes the state unstable (there's an unresolved proposal). -/
theorem question_makes_unstable :
    (s₀.question isRaining).isStable = false := rfl

/-- Both worlds are still compatible with the CG after a question. -/
theorem question_all_worlds_live :
    (s₀.question isRaining).space.root.all (· .rain) = true ∧
    (s₀.question isRaining).space.root.all (· .noRain) = true :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Accept/Reject Tests
-- ════════════════════════════════════════════════════

/-- Accepting the question's continuation puts rain in the root (CG). -/
theorem accept_updates_root :
    (s₀.question isRaining).acceptContinuation.space.root = [isRaining] := rfl

/-- After acceptance, the space is settled again. -/
theorem accept_resettles :
    (s₀.question isRaining).acceptContinuation.isStable = true := rfl

/-- After acceptance, rain-world is compatible, no-rain is excluded. -/
theorem accept_rain_only :
    (s₀.question isRaining).acceptContinuation.space.root.all (· .rain) = true ∧
    (s₀.question isRaining).acceptContinuation.space.root.all (· .noRain) = false :=
  ⟨rfl, rfl⟩

/-- Rejecting the question's continuation preserves the original root. -/
theorem reject_preserves_root :
    (s₀.question isRaining).rejectContinuation.space.root = [] := rfl

/-- After rejection, the space is settled again. -/
theorem reject_resettles :
    (s₀.question isRaining).rejectContinuation.isStable = true := rfl

/-- After rejection, both worlds are still live (we're back to start). -/
theorem reject_all_worlds_live :
    (s₀.question isRaining).rejectContinuation.space.root.all (· .rain) = true ∧
    (s₀.question isRaining).rejectContinuation.space.root.all (· .noRain) = true :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Assert = Question + Accept
-- ════════════════════════════════════════════════════

/-- The core equivalence: questioning φ and then accepting gives the
    same CG (root) as directly asserting φ. The two modes of updating
    converge on the same common ground. -/
theorem question_accept_eq_assert :
    (s₀.question isRaining).acceptContinuation.space.root =
    (s₀.assert isRaining).space.root := rfl

/-- The context sets are extensionally equal: same truth at every world. -/
theorem question_accept_eq_assert_context :
    (s₀.question isRaining).acceptContinuation.space.root.all (· .rain) =
    (s₀.assert isRaining).space.root.all (· .rain) ∧
    (s₀.question isRaining).acceptContinuation.space.root.all (· .noRain) =
    (s₀.assert isRaining).space.root.all (· .noRain) :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. Bipolar Questions
-- ════════════════════════════════════════════════════

/-- A bipolar question asks both "is it raining?" and "is it not raining?"
    This creates two continuations: one where rain holds, one where ¬rain holds.
    (Krifka 2015, §4: bipolar = two monopolar questions in sequence.) -/
private def bipolarQuestion : KrifkaState Weather :=
  s₀.question isRaining |>.question isNotRaining

/-- Bipolar question preserves root (CG unchanged). -/
theorem bipolar_preserves_root :
    bipolarQuestion.space.root = [] := rfl

/-- Bipolar question creates two continuations.

    After ?rain on empty space: { root = [], continuations = [[rain]] }
    After ?¬rain: root stays, new continuation [¬rain] added, existing [rain]
    narrowed to [¬rain, rain]. By Krifka's (14): {√C} ∪ (C + S₂⊢¬rain).

    Result: continuations = [[¬rain], [¬rain, rain]].

    The second continuation has both rain AND ¬rain — which is contradictory
    (no world satisfies both). This models Krifka's observation that stacking
    questions can create unsatisfiable continuations. -/
theorem bipolar_two_continuations :
    bipolarQuestion.space.continuations.length = 2 := rfl

/-- The first continuation of the bipolar question has ¬rain.
    Accepting this means we commit to no rain. -/
theorem bipolar_first_cont :
    bipolarQuestion.space.continuations.head? = some [isNotRaining] := rfl

/-- Accepting the first continuation of a bipolar question yields
    a CG where only the no-rain world is compatible. -/
theorem bipolar_accept_first :
    bipolarQuestion.acceptContinuation.space.root.all (· .rain) = false ∧
    bipolarQuestion.acceptContinuation.space.root.all (· .noRain) = true :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 7. Question Stacking (Assertion Narrows Continuations)
-- ════════════════════════════════════════════════════

/-- When we assert after questioning, the assertion narrows both the
    root AND the existing continuation.

    Start: question rain → { root = [], continuations = [[rain]] }
    Then assert ¬rain → { root = [¬rain], continuations = [[¬rain, rain]] }

    The continuation now requires BOTH rain AND ¬rain — contradiction.
    No world can satisfy [¬rain, rain]. -/
private def assertAfterQuestion : KrifkaState Weather :=
  s₀.question isRaining |>.assert isNotRaining

/-- After asserting ¬rain over a pending rain-question, the root
    is narrowed to ¬rain. -/
theorem assert_after_q_root :
    assertAfterQuestion.space.root = [isNotRaining] := rfl

/-- The continuation is contradictory: it requires both ¬rain and rain. -/
theorem assert_after_q_cont_contradictory :
    assertAfterQuestion.space.continuations = [[isNotRaining, isRaining]] := rfl

/-- The contradictory continuation has no compatible worlds. -/
theorem contradictory_cont_empty :
    [isNotRaining, isRaining].all (· Weather.rain) = false ∧
    [isNotRaining, isRaining].all (· Weather.noRain) = false :=
  ⟨by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 8. Matching Tag: Assert + Question (Krifka 2015, §5)
-- ════════════════════════════════════════════════════

/-- A matching tag "It's raining, isn't it?" = assert rain THEN question rain.
    The speaker first commits to rain (narrowing the CG), then asks the
    addressee to confirm (adding a biased continuation). -/
private def matchingTagState : KrifkaState Weather :=
  s₀.assert isRaining |>.question isRaining

/-- The root has rain (from the assertion). -/
theorem matching_tag_root :
    matchingTagState.space.root = [isRaining] := rfl

/-- There is one continuation (from the question). -/
theorem matching_tag_has_continuation :
    matchingTagState.space.continuations.length = 1 := rfl

/-- The continuation also has rain (the question adds rain to an
    already-rain root). The question is biased because it proposes
    what the speaker has already asserted. -/
theorem matching_tag_biased :
    matchingTagState.space.continuations = [[isRaining, isRaining]] := rfl

/-- Accepting the continuation of a matching tag gives the same CG
    as the assertion alone. The question was redundant in terms of
    content — its function is to seek confirmation, not new information. -/
theorem matching_tag_accept_eq_assert :
    matchingTagState.acceptContinuation.space.root.all (· .rain) =
    (s₀.assert isRaining).space.root.all (· .rain) ∧
    matchingTagState.acceptContinuation.space.root.all (· .noRain) =
    (s₀.assert isRaining).space.root.all (· .noRain) :=
  ⟨rfl, rfl⟩

end Phenomena.Assertion.Bridge.KrifkaCSD
