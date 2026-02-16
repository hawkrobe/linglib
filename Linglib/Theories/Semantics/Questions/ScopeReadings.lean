import Linglib.Theories.Semantics.Questions.Coordination
import Linglib.Theories.Semantics.Questions.MentionSome

/-!
# Questions/ScopeReadings.lean

Pair-List, Choice, and Mention-Some Readings (G&S 1984, Chapter VI, Sections 2-5).

## The Phenomenon

Embedded questions exhibit scope interactions with quantifiers:

**Pair-List Readings** (Section 2.1):
"Which student was recommended by each professor?"
→ For each professor, which student they recommended (list of pairs)

Here the universal quantifier takes WIDE scope over the wh-phrase.
The answer is a functional relation: professor → student.

**Choice Readings** (Section 2.2):
"John knows whom Mary or Sue invited"
→ John knows the answer, where the answer depends on whether
   Mary or Sue is the one asking

The disjunction/existential takes WIDE scope over the wh-phrase.
Different individuals can give different complete answers.

## Semantic Analysis

**Pair-List**: ∀y. ?x. R(y,x)
- The question is parameterized by the universal
- Answer must resolve the question for each y

**Choice**: ∃y. ?x. R(y,x) (or ∨)
- The question is parameterized by which y is relevant
- Answer resolves the question for SOME y (the one that matters)

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. VI, Sections 2.1-2.2.
- Szabolcsi (1997). Quantifiers in Pair-List Readings.
- Dayal (2016). Questions. MIT Press.
-/

namespace Semantics.Questions.ScopeReadings

open Semantics.Questions
open Semantics.Questions.Coordination
open Semantics.Questions.MentionSome
open scoped GSQuestion  -- For ⊑ notation


/-!
## Pair-List Readings

"Which student was recommended by each professor?"

**Standard Reading**: ?x. ∀y. Prof(y) → Recommended(y, x)
- One student recommended by ALL professors
- Very restrictive; often no such student exists

**Pair-List Reading**: ∀y. Prof(y) → ?x. Recommended(y, x)
- For each professor, which student they recommended
- Answer is a FUNCTION from professors to students

The pair-list reading arises when:
1. The universal takes wide scope over the wh-phrase
2. The answer is a function/relation
-/

/-- A pair-list question: for each element of a domain, ask a wh-question.

"Which X did each Y verb?" becomes:
∀y∈Y. ?x. R(y, x) -/
structure PairListQuestion (W E : Type*) where
  /-- The domain of the universal ("each professor") -/
  universalDomain : List E
  /-- The wh-domain ("which student") -/
  whDomain : List E
  /-- The relation being asked about -/
  relation : W -> E -> E -> Bool
  /-- Name of the universal NP -/
  universalNP : String
  /-- Name of the wh-phrase -/
  whPhrase : String

/-- A pair-list answer: a function from the universal domain to wh-answers. -/
structure PairListAnswer (E : Type*) where
  /-- The function mapping each universal element to its answer -/
  pairs : E -> Option E

/-- Convert a pair-list question to a GSQuestion.

The partition groups worlds by the ENTIRE function from Y to X:
Two worlds are equivalent iff they have the same pair-list. -/
def PairListQuestion.toGSQuestion {W E : Type*} [DecidableEq E]
    (plq : PairListQuestion W E) : GSQuestion W where
  sameAnswer w v :=
    -- Same iff for all y∈Y, the unique x with R(y,x) is the same
    plq.universalDomain.all λ y =>
      plq.whDomain.all λ x =>
        plq.relation w y x == plq.relation v y x
  refl w := by
    simp only [List.all_eq_true]
    intro y _ x _
    exact beq_self_eq_true _
  symm w v := by
    congr 1
    funext y
    congr 1
    funext x
    cases plq.relation w y x <;> cases plq.relation v y x <;> rfl
  trans w v x hwv hvx := by
    simp only [List.all_eq_true] at *
    intro y hy z hz
    have h1 := hwv y hy z hz
    have h2 := hvx y hy z hz
    rw [beq_iff_eq] at *
    exact h1.trans h2

/-- Build individual question for a specific universal element. -/
def PairListQuestion.individualQuestion {W E : Type} [DecidableEq E] [DecidableEq (List E)]
    (plq : PairListQuestion W E) (y : E) : GSQuestion W where
  sameAnswer w v :=
    decide (plq.whDomain.filter (λ x => plq.relation w y x) =
            plq.whDomain.filter (λ x => plq.relation v y x))
  refl w := by simp [decide_eq_true_iff]
  symm w v := by simp [decide_eq_decide]; exact eq_comm
  trans w v x hwv hvx := by
    simp only [decide_eq_true_iff] at *
    exact hvx ▸ hwv

/-- A pair-list question is equivalent to a conjunction of individual questions.

∀y. ?x. R(y,x) = ∧_{y∈Y} ?x. R(y,x)

Note: The formal statement requires universe matching; see pairListAsConjunction. -/
theorem pairList_as_conjunction {W E : Type} [DecidableEq E] [DecidableEq (List E)] [BEq W]
    (plq : PairListQuestion W E) :
    plq.toGSQuestion = pairListAsConjunction plq.universalDomain plq.individualQuestion := by
  sorry -- The partition induced by pair-list = conjunction of individual questions

/-- Number of cells in pair-list: can be up to |X|^|Y| (exponential).

If each professor can recommend any student, and there are n professors
and m students, the pair-list question has up to m^n cells. -/
def PairListQuestion.maxCells {W E : Type*}
    (plq : PairListQuestion W E) : Nat :=
  plq.whDomain.length ^ plq.universalDomain.length


/-!
## Choice Readings

"John knows whom Mary or Sue invited"

**Non-Choice Reading**: John knows: ?x. (Mary-invited(x) ∨ Sue-invited(x))
- John knows who was invited by at least one of them

**Choice Reading**: John knows: Mary-invited(?x) ∨ Sue-invited(?x)
- Depending on whether Mary or Sue is relevant, John knows that answer
- This is a de re reading of the disjunction

The choice reading arises when:
1. A disjunctive/existential NP takes wide scope over the wh-phrase
2. The embedded question is "parameterized" by which disjunct is true

"Whom does John or Mary love?" can be answered:
- "If John: Bill. If Mary: Sue."
This gives DIFFERENT answers depending on who is the lover.
-/

/-- A choice question: question parameterized by a disjunction.

"Whom does Y₁ or Y₂ verb?" -/
structure ChoiceQuestion (W E : Type*) where
  /-- The disjuncts -/
  disjuncts : List E
  /-- The wh-domain -/
  whDomain : List E
  /-- The relation -/
  relation : W -> E -> E -> Bool
  /-- Description of the disjunction -/
  disjunctionNP : String
  /-- The wh-phrase -/
  whPhrase : String

/-- A choice answer: potentially different answer for each disjunct. -/
structure ChoiceAnswer (E : Type*) where
  /-- Which disjunct is "active" -/
  activeDisjunct : E
  /-- The answer for that disjunct -/
  answer : E
  deriving Repr

/-- Under choice reading, different disjuncts can give different answers.

"Whom does John or Mary love?"
- Answer: "John loves Bill; Mary loves Sue"
- This is the CONDITIONAL ANSWER: for each disjunct, the answer. -/
def ChoiceQuestion.conditionalAnswer {W E : Type*} [DecidableEq E]
    (cq : ChoiceQuestion W E) (w : W) : List (E × List E) :=
  cq.disjuncts.map λ d =>
    (d, cq.whDomain.filter (cq.relation w d))

/-- Convert choice question to LiftedQuestion under choice reading.

The choice reading involves existential quantification over disjuncts,
which is like disjunction. Since disjunction of equivalence relations
is NOT an equivalence relation, we must use the lifted type.

Two worlds are equivalent iff for SOME disjunct, they give the same answer. -/
def ChoiceQuestion.toLiftedQuestion_choice {W E : Type*} [BEq W] [DecidableEq E]
    (cq : ChoiceQuestion W E) : LiftedTypes.LiftedQuestion W :=
  -- The choice reading is a disjunction over the per-disjunct questions
  -- We build each question directly to avoid LawfulBEq constraint on List E
  let mkQuestion (d : E) : GSQuestion W := {
    sameAnswer := λ w v =>
      decide (cq.whDomain.filter (λ x => cq.relation w d x) =
              cq.whDomain.filter (λ x => cq.relation v d x))
    refl := λ w => by simp [decide_eq_true_iff]
    symm := λ w v => by simp [decide_eq_decide]; exact eq_comm
    trans := λ w v x hwv hvx => by
      simp only [decide_eq_true_iff] at *
      exact hvx ▸ hwv
  }
  let perDisjunct := cq.disjuncts.map mkQuestion
  match perDisjunct with
  | [] => LiftedTypes.LiftedQuestion.lift GSQuestion.trivial
  | q :: qs =>
    qs.foldl (λ acc q' =>
      LiftedTypes.LiftedQuestion.disj acc (LiftedTypes.LiftedQuestion.lift q'))
      (LiftedTypes.LiftedQuestion.lift q)

/-- Under NON-choice reading, worlds match iff ALL disjunct-answers match. -/
def ChoiceQuestion.toGSQuestion_nonchoice {W E : Type*} [DecidableEq E]
    (cq : ChoiceQuestion W E) : GSQuestion W where
  sameAnswer w v :=
    -- Same iff all disjuncts give same answer
    cq.disjuncts.all λ d =>
      cq.whDomain.all λ x =>
        cq.relation w d x == cq.relation v d x
  refl w := by
    simp only [List.all_eq_true]
    intro _ _ _ _
    exact beq_self_eq_true _
  symm w v := by
    simp only [List.all_eq_true, Bool.beq_comm]
  trans w v x hwv hvx := by
    simp only [List.all_eq_true] at *
    intro d hd e he
    have h1 := hwv d hd e he
    have h2 := hvx d hd e he
    rw [beq_iff_eq] at *
    exact h1.trans h2

/-!
### Relationship between choice and non-choice readings

The choice reading (existential/disjunctive) is semantically COARSER than
the non-choice reading (universal/conjunctive). However, since they now
have different types (LiftedQuestion vs GSQuestion), direct comparison
via refinement (⊑) is not available.

To compare them, lift the non-choice reading and show that the lifted
non-choice "entails" the choice reading in the sense that any property
holding of all disjunct-questions holds of at least one.
-/


/-!
## Existential Wide Scope

"Which student does some professor recommend?"

Similar to choice readings, but with existential quantifier:

**Narrow Scope**: ?x. ∃y. Prof(y) ∧ Recommends(y,x)
- Which student is recommended by at least one professor?

**Wide Scope**: ∃y. Prof(y) ∧ ?x. Recommends(y,x)
- There is some professor; which student do they recommend?

The wide scope reading is a "functional" or "choice" reading where
the existential picks out a specific professor.
-/

/-- An existential-over-wh question. -/
structure ExistentialQuestion (W E : Type*) where
  /-- The existential domain -/
  existentialDomain : List E
  /-- The wh-domain -/
  whDomain : List E
  /-- The relation -/
  relation : W -> E -> E -> Bool

/-- Narrow scope: ∃y. ?x. R(y,x) collapses to ?x. ∃y. R(y,x) -/
def ExistentialQuestion.narrowScope {W E : Type} [DecidableEq E] [DecidableEq (List E)]
    (eq : ExistentialQuestion W E) : GSQuestion W where
  sameAnswer w v :=
    let answersW := eq.whDomain.filter λ x => eq.existentialDomain.any λ y => eq.relation w y x
    let answersV := eq.whDomain.filter λ x => eq.existentialDomain.any λ y => eq.relation v y x
    decide (answersW = answersV)
  refl w := by simp [decide_eq_true_iff]
  symm w v := by simp [decide_eq_decide]; exact eq_comm
  trans w v x hwv hvx := by
    simp only [decide_eq_true_iff] at *
    exact hvx ▸ hwv

/-- Wide scope: for the "relevant" y, what's the answer?

This is similar to choice reading - the answer can vary based on
which existential witness is considered.

Since this involves existential quantification (which is like disjunction),
we must use the lifted type to avoid the transitivity problem. -/
def ExistentialQuestion.wideScope {W E : Type*} [BEq W] [DecidableEq E]
    (eq : ExistentialQuestion W E) : LiftedTypes.LiftedQuestion W :=
  -- Wide scope is a disjunction over the per-witness questions
  -- Build each question directly to avoid LawfulBEq constraint on List E
  let mkQuestion (y : E) : GSQuestion W := {
    sameAnswer := λ w v =>
      decide (eq.whDomain.filter (λ x => eq.relation w y x) =
              eq.whDomain.filter (λ x => eq.relation v y x))
    refl := λ w => by simp [decide_eq_true_iff]
    symm := λ w v => by simp [decide_eq_decide]; exact eq_comm
    trans := λ w v x hwv hvx => by
      simp only [decide_eq_true_iff] at *
      exact hvx ▸ hwv
  }
  let perWitness := eq.existentialDomain.map mkQuestion
  match perWitness with
  | [] => LiftedTypes.LiftedQuestion.lift GSQuestion.trivial
  | q :: qs =>
    qs.foldl (λ acc q' =>
      LiftedTypes.LiftedQuestion.disj acc (LiftedTypes.LiftedQuestion.lift q'))
      (LiftedTypes.LiftedQuestion.lift q)


/-!
## Functional Readings

When the wh-answer is FUNCTIONALLY DEPENDENT on a wide-scope quantifier,
we get readings where the answer is a function.

"Which of his teachers does every student admire?"
→ Answer: "John admires Smith, Mary admires Jones, ..."
→ A function from students to teachers

The function IS the complete answer under the pair-list reading.
-/

/-- A functional answer: maps each element of one domain to another. -/
def FunctionalAnswer (D R : Type*) := D -> Option R

/-- The number of possible functional answers. -/
def numFunctionalAnswers (domainSize rangeSize : Nat) : Nat :=
  (rangeSize + 1) ^ domainSize  -- +1 for "no answer" option

/-- A question has a functional reading if the answer is a function.

This happens when:
1. There's a pair-list configuration (universal over wh)
2. For each domain element, there's a unique wh-answer -/
def hasFunctionalReading {W E : Type*} [DecidableEq E]
    (plq : PairListQuestion W E) (worlds : List W) : Bool :=
  -- In each world, each y has at most one x with R(y,x)
  worlds.all λ w =>
    plq.universalDomain.all λ y =>
      let answers := plq.whDomain.filter (plq.relation w y)
      answers.length <= 1


/-!
## Mention-Some and Scope

"Where can I buy an Italian newspaper?"

This has a mention-some reading: ONE place suffices.

The existential "an Italian newspaper" can take wide scope:
∃x. Paper(x) ∧ ?place. Sells(place, x)

But this doesn't fully explain mention-some, which is about
the QUESTIONER'S GOAL, not scope.

However, wide scope CAN interact with mention-some:
- "Which student does some professor recommend?" (choice + mention-some)
- "Who speaks some Scandinavian language?" (existential + mention-some)

See MentionSome.lean for full G&S Section 5 treatment:
- I-MS rule (formal semantic operation)
- P-ANS analysis and its problems
- Embedded mention-some under "know"/"wonder"
- Verb licensing (why "depends" blocks mention-some)
-/

/-- A question has mention-some reading when partial answers suffice. -/
structure MentionSomeQuestion (W : Type*) where
  /-- The underlying question -/
  question : GSQuestion W
  /-- Is mention-some licensed? -/
  mentionSome : Bool
  /-- Why mention-some is licensed -/
  explanation : String

/-- Wide scope existential can create mention-some-like readings.

If the question is parameterized by an existential, answering for
ANY witness can suffice, mimicking mention-some.

Note: We use the narrow scope GSQuestion here for compatibility with
MentionSomeQuestion, but the semantics is that mention-some is licensed
due to the wide-scope existential interpretation. For the true wide-scope
semantics as a LiftedQuestion, use `eq.wideScope` directly. -/
def existentialCreatesMentionSome {W E : Type} [DecidableEq E] [DecidableEq (List E)]
    (eq : ExistentialQuestion W E) : MentionSomeQuestion W :=
  { question := eq.narrowScope
  , mentionSome := true
  , explanation := "Wide-scope existential: answer for any witness suffices"
  }

/-- Convert an ExistentialQuestion to a MentionSomeInterrogative.

This connects the scope-based existential question to the G&S Section 5
formal treatment of mention-some. -/
def ExistentialQuestion.toMentionSomeInterrogative {W E : Type*}
    (eq : ExistentialQuestion W E) : MentionSomeInterrogative W E :=
  { whDomain := eq.whDomain
  , abstract := λ w x => eq.existentialDomain.any λ y => eq.relation w y x
  }

/-- Wide-scope existential implies mention-some is licensed.

G&S 1984, Section 5: When an existential takes wide scope over the wh-phrase,
the question receives a mention-some interpretation because any witness
for the existential provides a sufficient answer. -/
theorem wideScope_existential_licenses_mentionSome {W E : Type*} [DecidableEq E]
    (eq : ExistentialQuestion W E) (w : W)
    (_hExists : eq.existentialDomain.any λ y =>
      eq.whDomain.any λ x => eq.relation w y x) :
    (eq.toMentionSomeInterrogative).whDomain.any λ x =>
      (eq.toMentionSomeInterrogative).abstract w x := by
  unfold ExistentialQuestion.toMentionSomeInterrogative
  simp only [List.any_eq_true] at *
  obtain ⟨y, hy_mem, x, hx_mem, hx_rel⟩ := _hExists
  exact ⟨x, hx_mem, y, hy_mem, hx_rel⟩


/-!
## When Do These Readings Arise?

**Pair-List Licensing**:
1. Universal quantifier c-commands wh-phrase
2. The question has a "natural functional interpretation"
3. The answer can be presented as a list

"Which student did each professor recommend?" ✓
"Each professor recommended which student?"  (marked)

**Choice Licensing**:
1. Disjunction/existential c-commands wh-phrase
2. The different disjuncts/witnesses are contextually salient
3. Conditional answers are felicitous

"Whom does John or Mary love?" ✓ (if both John and Mary are salient)

**Factors**:
- Attitude verbs: "know" licenses pair-list more than "wonder"
- Definiteness: definite subjects are harder for pair-list
- Information structure: contrastive focus on universal
-/

/-- Factors affecting pair-list availability. -/
structure PairListFactors where
  /-- The attitude verb (if embedded) -/
  attitudeVerb : Option String
  /-- Is the universal definite? -/
  universalDefinite : Bool
  /-- Does the universal have contrastive focus? -/
  contrastiveFocus : Bool
  /-- Is the question matrix or embedded? -/
  isMatrix : Bool

/-- Predict pair-list availability from factors. -/
def predictPairList (factors : PairListFactors) : Bool :=
  -- Pair-list more likely with:
  -- - "know" than "wonder"
  -- - indefinite universals
  -- - contrastive focus
  -- - embedded questions
  let verbOK := match factors.attitudeVerb with
    | some "know" => true
    | some "wonder" => false
    | some "ask" => false
    | _ => true  -- matrix questions
  let defOK := !factors.universalDefinite
  let focusOK := factors.contrastiveFocus
  verbOK && (defOK || focusOK)

end Semantics.Questions.ScopeReadings
