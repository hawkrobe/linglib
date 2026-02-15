import Linglib.Fragments.English.Determiners
import Linglib.Theories.TruthConditional.Determiner.Quantifier

/-!
# Basic Quantifier Examples

End-to-end tests verifying that the English quantifier Fragment, composed
with a toy scenario, produces correct truth-value judgments, acceptability
predictions, and entailment patterns.

The **scenario** (entities, predicates, truth assignments) is defined here
in Phenomena — it is empirical data. The **compositional machinery**
(Model, FiniteModel, GQ denotations) comes from TruthConditional. The
**lexical entries** (strength, monotonicity) come from the Fragment.

## Test architecture

1. **Acceptability** (Tier 1): there-insertion from Fragment `Strength`
2. **Truth values** (Tier 2): sentence denotations evaluated in a scenario
3. **Entailment** (Tier 3): monotonicity-driven inferences
4. **Scalar distinctness** (Tier 4): quantifiers differ on at least one input
-/

namespace Phenomena.Quantification.Examples

open TruthConditional
open TruthConditional.Determiner.Quantifier
open Core.Quantification
open Fragments.English.Determiners (QuantityWord Strength Monotonicity)

-- ============================================================================
-- Scenario: a small world with students and predicates
-- ============================================================================

/-! ## Scenario

Four entities: Alice, Bob, Carol, Dave.
- Students: Alice, Bob (2 of 4)
- Passed: Alice (1 of 2 students)
- Laughed: Alice, Bob (all students)
- Cried: nobody
-/

inductive Person where
  | alice | bob | carol | dave
  deriving Repr, DecidableEq

def scenario : Model :=
  { Entity := Person, decEq := inferInstance }

instance : FiniteModel scenario where
  elements := [.alice, .bob, .carol, .dave]
  complete := λ x => by cases x <;> simp
  nodup := by simp [List.nodup_cons, List.mem_cons, List.mem_singleton]

def student : scenario.interpTy (.e ⇒ .t) :=
  λ x => match x with
  | .alice => true | .bob => true | _ => false

def passed : scenario.interpTy (.e ⇒ .t) :=
  λ x => match x with
  | .alice => true | _ => false

def laughed : scenario.interpTy (.e ⇒ .t) :=
  λ x => match x with
  | .alice => true | .bob => true | _ => false

def cried : scenario.interpTy (.e ⇒ .t) :=
  λ _ => false

def thing : scenario.interpTy (.e ⇒ .t) :=
  λ _ => true

-- ============================================================================
-- §1: Acceptability — there-insertion from Fragment Strength
-- ============================================================================

/-! ## Tier 1: Acceptability

B&C Table II: weak determiners allow there-insertion, strong ones don't.
These judgments are derived purely from the Fragment's `Strength` field.

- "There are some students in the room." (✓ weak)
- "There are no students in the room." (✓ weak)
- "There are few students in the room." (✓ weak)
- *"There is every student in the room." (✗ strong)
- *"There are most students in the room." (✗ strong)
- *"There are all students in the room." (✗ strong)
-/

/-- Weak quantifiers: acceptable in there-sentences. -/
theorem there_acceptable :
    QuantityWord.none_.entry.strength = .weak ∧
    QuantityWord.few.entry.strength = .weak ∧
    QuantityWord.some_.entry.strength = .weak ∧
    QuantityWord.half.entry.strength = .weak := ⟨rfl, rfl, rfl, rfl⟩

/-- Strong quantifiers: unacceptable in there-sentences. -/
theorem there_unacceptable :
    QuantityWord.most.entry.strength = .strong ∧
    QuantityWord.all.entry.strength = .strong := ⟨rfl, rfl⟩

/-- The 6-word scale partitions into 4 weak + 2 strong. -/
theorem weak_strong_partition :
    (QuantityWord.toList.filter (·.entry.strength == .weak)).length = 4 ∧
    (QuantityWord.toList.filter (·.entry.strength == .strong)).length = 2 := by
  native_decide

-- ============================================================================
-- §2: Truth-value judgments in the scenario
-- ============================================================================

/-! ## Tier 2: Truth Values

Compose Fragment denotations with scenario predicates and verify.

| Sentence                  | Expected | Why                           |
|---------------------------|----------|-------------------------------|
| Every student laughed     | true     | Alice ✓, Bob ✓               |
| Every student passed      | false    | Bob ✗                         |
| Some student passed       | true     | Alice ✓                       |
| Some student cried        | false    | nobody cried                  |
| No student cried          | true     | nobody cried                  |
| No student passed         | false    | Alice passed                  |
| Most students passed      | false    | 1 of 2 ≤ half                |
| Most students laughed     | true     | 2 of 2 > 0 (= |student\laughed|)|
-/

theorem every_student_laughed :
    every_sem scenario student laughed = true := rfl

theorem every_student_passed :
    every_sem scenario student passed = false := rfl

theorem some_student_passed :
    some_sem scenario student passed = true := rfl

theorem some_student_cried :
    some_sem scenario student cried = false := rfl

theorem no_student_cried :
    no_sem scenario student cried = true := rfl

theorem no_student_passed :
    no_sem scenario student passed = false := rfl

theorem most_students_passed :
    most_sem scenario student passed = false := rfl

theorem most_students_laughed :
    most_sem scenario student laughed = true := rfl

-- ============================================================================
-- §3: Entailment from monotonicity
-- ============================================================================

/-! ## Tier 3: Entailment

Fragment `monotonicity` metadata predicts entailment directions.
We verify these by composing semantic proofs with our scenario.

- Scope-↑ (every, some): if P ⊆ Q then Det(A)(P) → Det(A)(Q)
- Scope-↓ (no): if P ⊆ Q then Det(A)(Q) → Det(A)(P)
-/

/-- passed ⊆ laughed in our scenario (Alice passed ∧ laughed, Bob only laughed). -/
theorem passed_subset_laughed : ∀ x, passed x = true → laughed x = true := by
  intro x h; cases x <;> simp_all [passed, laughed]

/-- Fragment says "every"/"all" is scope-↑ monotone. -/
theorem every_mono_metadata :
    QuantityWord.all.entry.monotonicity = .increasing := rfl

/-- "Some student passed" entails "some student laughed" by scope-↑ mono. -/
theorem some_passed_entails_laughed :
    some_sem scenario student passed = true →
    some_sem scenario student laughed = true :=
  some_scope_up student passed laughed passed_subset_laughed

/-- "No student laughed" would entail "no student passed" by scope-↓ mono.
    (In our scenario, neither premise holds, but the implication is valid.) -/
theorem no_laughed_entails_no_passed :
    no_sem scenario student laughed = true →
    no_sem scenario student passed = true :=
  no_scope_down student passed laughed passed_subset_laughed

/-- Fragment monotonicity metadata matches semantic behavior. -/
theorem monotonicity_metadata_correct :
    QuantityWord.some_.entry.monotonicity = .increasing ∧
    QuantityWord.none_.entry.monotonicity = .decreasing ∧
    QuantityWord.all.entry.monotonicity = .increasing := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §4: Scalar distinctness
-- ============================================================================

/-! ## Tier 4: Scalar Distinctness

For scalar implicature to arise, adjacent scale-mates must differ on some input.
We verify this by finding *witnesses* — inputs where they diverge.
-/

/-- "Some" ≠ "every": some(student)(passed)=T but every(student)(passed)=F. -/
theorem some_ne_every :
    some_sem scenario student passed = true ∧
    every_sem scenario student passed = false :=
  ⟨some_student_passed, every_student_passed⟩

/-- "Some" ≠ "no": some(student)(passed)=T but no(student)(passed)=F. -/
theorem some_ne_no :
    some_sem scenario student passed = true ∧
    no_sem scenario student passed = false :=
  ⟨some_student_passed, no_student_passed⟩

/-- "Every" vs "most": they agree on students who laughed (both T)
    and students who passed (both F). The key difference is logical
    strength: every entails most but not vice versa. -/
theorem every_vs_most :
    every_sem scenario student laughed = true ∧
    most_sem scenario student laughed = true ∧
    every_sem scenario student passed = false ∧
    most_sem scenario student passed = false :=
  ⟨every_student_laughed, most_students_laughed,
   every_student_passed, most_students_passed⟩

/-- "No" ≠ "every": no(student)(cried)=T but every(student)(cried)=F. -/
private theorem every_student_cried :
    every_sem scenario student cried = false := rfl

theorem no_ne_every :
    no_sem scenario student cried = true ∧
    every_sem scenario student cried = false :=
  ⟨no_student_cried, every_student_cried⟩

end Phenomena.Quantification.Examples
