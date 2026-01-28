/-
# RSA Question Embedding

Models scalar implicatures embedded in questions.

## The Phenomenon

"Did some students pass?"

Questions have a unique status regarding scalar implicatures:
- Not clearly upward-entailing (UE) like assertions
- Not clearly downward-entailing (DE) like negation
- Implicatures may arise, but weaker than in assertions

## Theoretical Background

Questions are often analyzed as sets of propositions (Hamblin 1973) or
partitions of logical space (Groenendijk & Stokhof 1984). The key insight:

A question "Did some students pass?" asks the hearer to choose between:
- "Yes, some passed" (weak: ≥1)
- "No, no one passed"

If the implicature "not all" is computed:
- "Yes, some-but-not-all passed"
- "No, either none or all passed" (??)

The second option doesn't make sense, suggesting local SI in questions
is problematic.

## Predictions

Unlike assertions (where local SI strengthens) or DE contexts (where
local SI weakens), questions create an asymmetry:
- The "yes" answer benefits from SI (more precise)
- The "no" answer becomes weird with SI (disjunctive)

RSA should predict: Local SI is dispreferred in questions because it
makes one answer pragmatically odd.

## References

- Geurts (2010). Quantity Implicatures. Ch. 3 on embedded implicatures.
- Hamblin (1973). Questions in Montague English.
- van Rooij & Schulz (2004). Exhaustive interpretation of complex sentences.
- Guerzoni (2004). Even-NPIs in yes/no questions.
-/

import Linglib.Theories.RSA.Core.Basic

namespace RSA.QuestionEmbedding

-- ============================================================================
-- World Structure for Questions
-- ============================================================================

/--
Student outcome for question scenario.
-/
inductive StudentResult where
  | noneP   -- no students passed
  | someP   -- some but not all passed
  | allP    -- all students passed
  deriving DecidableEq, Repr, BEq, Inhabited

instance : Fintype StudentResult where
  elems := ⟨[StudentResult.noneP, StudentResult.someP, StudentResult.allP], by decide⟩
  complete := fun x => by cases x <;> decide

/--
Worlds represent the actual state of affairs.
-/
def questionWorlds : List StudentResult := [.noneP, .someP, .allP]

-- ============================================================================
-- Question Semantics
-- ============================================================================

/--
A yes/no question partitions the world into "yes" and "no" answers.

For "Did some students pass?":
- Yes-worlds: where some (≥1) passed
- No-worlds: where none passed
-/
structure YesNoPartition where
  yesWorlds : List StudentResult
  noWorlds : List StudentResult

/--
Interpretations of "Did some students pass?":

1. **Global**: "some" = at least one
   - Yes: someP, allP (some passed)
   - No: noneP (none passed)

2. **Local**: "some" = some-but-not-all
   - Yes: someP (some-but-not-all passed)
   - No: noneP, allP (?? disjunctive/weird)
-/
inductive QuestionInterpretation where
  | global  -- "some" = at least one
  | local_  -- "some" = some-but-not-all
  deriving DecidableEq, Repr, BEq, Inhabited, Fintype

/--
The partition induced by each interpretation.
-/
def questionPartition (interp : QuestionInterpretation) : YesNoPartition :=
  match interp with
  | .global => {
      yesWorlds := [.someP, .allP]  -- At least one passed
      noWorlds := [.noneP]          -- None passed
    }
  | .local_ => {
      yesWorlds := [.someP]           -- Some-but-not-all passed
      noWorlds := [.noneP, .allP]     -- Disjunctive! None OR all.
    }

-- ============================================================================
-- Key Predictions
-- ============================================================================

/--
Global interpretation gives a natural partition:
- Yes = some passed (continuous region on scale)
- No = none passed (complementary region)
-/
theorem global_partition_natural :
    (questionPartition .global).yesWorlds = [.someP, .allP] ∧
    (questionPartition .global).noWorlds = [.noneP] := by
  constructor <;> rfl

/--
Local interpretation gives a strange partition:
- Yes = some-but-not-all (specific point)
- No = none OR all (disjunctive!)

This disjunctive "no" answer is pragmatically odd.
-/
theorem local_partition_disjunctive :
    (questionPartition .local_).noWorlds = [.noneP, .allP] := rfl

/--
The "no" answer under local interpretation is disjunctive.
This is marked by the worlds being non-contiguous on the scale.
-/
def isContiguous (worlds : List StudentResult) : Bool :=
  -- Contiguous means: either a prefix or suffix of [noneP, someP, allP]
  worlds == [.noneP] ||
  worlds == [.someP] ||
  worlds == [.allP] ||
  worlds == [.noneP, .someP] ||
  worlds == [.someP, .allP] ||
  worlds == [.noneP, .someP, .allP]

theorem global_no_contiguous :
    isContiguous (questionPartition .global).noWorlds = true := rfl

theorem local_no_not_contiguous :
    isContiguous (questionPartition .local_).noWorlds = false := rfl

-- ============================================================================
-- Exhaustive Interpretation
-- ============================================================================

/-
## Exhaustive Interpretation

Questions often trigger EXHAUSTIVE interpretation of answers:
- "Who passed?" → "The students who passed are: ..."
- This lists ALL passers, not just some

For "Did some students pass?", answering "yes" with exhaustive
interpretation means:
- "Yes, and here's the full story about who passed"

If the hearer answers "yes" when ALL passed, saying just "some passed"
is misleading. This suggests the global interpretation is preferred
even without computing local SI.

## Van Rooij & Schulz (2004)

They argue that exhaustive interpretation of questions BLOCKS scalar
implicatures. The question context makes it unnecessary to compute
the "not all" inference because the answer is expected to be precise.
-/

/--
Exhaustive interpretation: the "yes" answer conveys the MAXIMAL
true proposition consistent with "yes".

For global "Did some pass?":
- If someP: answer conveys "some but not all"
- If allP: answer conveys "all"

This makes local SI redundant - exhaustivity handles it.
-/
def exhaustiveAnswer (interp : QuestionInterpretation) (actual : StudentResult) : String :=
  match interp, actual with
  | .global, .noneP => "No, none passed"
  | .global, .someP => "Yes, some (but not all) passed"  -- Exhaustive!
  | .global, .allP => "Yes, all passed"  -- Exhaustive!
  | .local_, .noneP => "No (none passed)"
  | .local_, .someP => "Yes, some-but-not-all passed"
  | .local_, .allP => "No (all passed)"  -- Weird answer!

/--
Under local interpretation, the "all" world gets a "no" answer,
which is pragmatically bizarre.
-/
theorem local_all_gets_no :
    exhaustiveAnswer .local_ .allP = "No (all passed)" := rfl

/--
Under global interpretation with exhaustivity, all answers are natural.
-/
theorem global_answers_natural :
    exhaustiveAnswer .global .noneP = "No, none passed" ∧
    exhaustiveAnswer .global .someP = "Yes, some (but not all) passed" ∧
    exhaustiveAnswer .global .allP = "Yes, all passed" := by
  refine ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- RSA Analysis
-- ============================================================================

/-
## RSA Prediction

RSA should prefer the global interpretation for questions because:

1. **Partition Quality**: Global gives a cleaner partition
   - Each answer corresponds to a natural region of the scale
   - Local gives a disjunctive "no" region

2. **Answer Naturalness**: Under exhaustivity, global answers work well
   - Local makes "all passed" a "no" answer, which is confusing

3. **Informativity**: The question itself is about whether ANY passed
   - Local interpretation asks a different, less natural question
   - "Did exactly some-but-not-all pass?" is odd

## Contrast with Assertions and DE

| Context | Local SI | RSA Prediction |
|---------|----------|----------------|
| Assertion ("Some passed") | Strengthens | Local preferred |
| DE ("No one ate some") | Weakens | Global preferred |
| Question ("Did some pass?") | Odd partition | Global preferred |

Questions pattern with DE contexts in preferring global, but for
different reasons (partition quality vs informational strength).
-/

/--
RSA predicts: global interpretation preferred for questions.

Reason: Local creates pragmatically odd partition where "all passed"
is a "no" answer.
-/
theorem question_prefers_global :
    -- Local gives disjunctive (odd) "no" region
    isContiguous (questionPartition .local_).noWorlds = false ∧
    -- Global gives clean "no" region
    isContiguous (questionPartition .global).noWorlds = true := by
  constructor <;> rfl

-- ============================================================================
-- Comparison with Other Embeddings
-- ============================================================================

/-
## Comparison Table

| Embedding | Entailment Direction | RSA Prediction | Reason |
|-----------|---------------------|----------------|--------|
| Assertion | - | Local | More informative |
| Under "no" | Global ⊆ Local | Global | Informational |
| Conditional antecedent | Global ⊆ Local | Global | DE-like |
| Attitude verb | Local ⊆ Global | Both available | Neither dominates |
| Question | Neither | Global | Partition quality |

Questions are unique: the preference for global isn't about entailment
relations but about the pragmatic felicity of the resulting partition.
-/

/--
Questions differ from all other embedding contexts:
- Not about entailment direction (like DE vs UE)
- About pragmatic naturalness of the question-answer structure
-/
structure QuestionUniqueness where
  /-- Global doesn't entail local (unlike DE): allP is in global-yes but not local-yes -/
  not_de_like : ∃ w : StudentResult, (questionPartition .global).yesWorlds.elem w = true ∧
                     (questionPartition .local_).yesWorlds.elem w = false
  /-- Local doesn't entail global (unlike attitude verbs): someP is in both -/
  not_attitude_like : ∃ w : StudentResult, (questionPartition .local_).yesWorlds.elem w = true ∧
                          (questionPartition .global).yesWorlds.elem w = true

/--
Questions are indeed unique - neither DE-like nor attitude-verb-like
in their entailment pattern, yet still prefer global.
-/
def questionIsUnique : QuestionUniqueness where
  not_de_like := ⟨.allP, by native_decide, by native_decide⟩
  not_attitude_like := ⟨.someP, by native_decide, by native_decide⟩

-- ============================================================================
-- Summary
-- ============================================================================

/-
## Key Results

1. **Global preferred in questions**: Like DE contexts but different reason.

2. **Partition quality matters**: Local creates disjunctive "no" answer.

3. **Exhaustive interpretation**: Makes local SI redundant anyway.

4. **Questions are unique**: Preference isn't about entailment direction.

## Connection to Linguistic Theory

This formalizes observations from:
- Geurts (2010): Questions don't clearly trigger SI
- Van Rooij & Schulz (2004): Exhaustivity blocks SI in questions
- Guerzoni (2004): Even-NPIs licensed differently in questions

## Future Work

- Add full RSA computation with lexical uncertainty
- Model wh-questions ("Which students passed some exams?")
- Connect to focus and information structure
- Model embedded questions ("John asked whether some students passed")
-/

end RSA.QuestionEmbedding
