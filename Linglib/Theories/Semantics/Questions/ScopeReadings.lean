import Linglib.Theories.Semantics.Questions.Coordination
import Linglib.Theories.Semantics.Questions.LiftedTypes
import Linglib.Theories.Semantics.Questions.Answerhood.MentionSome

/-!
# Questions/ScopeReadings.lean
@cite{dayal-2016} @cite{groenendijk-stokhof-1984} @cite{szabolcsi-1997}

Pair-List, Choice, and Mention-Some Readings (@cite{groenendijk-stokhof-1984}, Chapter VI, Sections 2-5).

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
    (plq : PairListQuestion W E) : GSQuestion W :=
  QUD.ofDecEq (λ w =>
    plq.universalDomain.map (λ y => plq.whDomain.map (λ x => plq.relation w y x)))

/-- Build individual question for a specific universal element. -/
def PairListQuestion.individualQuestion {W E : Type} [DecidableEq E]
    (plq : PairListQuestion W E) (y : E) : GSQuestion W :=
  QUD.ofDecEq (λ w => plq.whDomain.map (λ x => plq.relation w y x))

/-- Helper: foldl of GSQuestion conjunction decomposes into init && all. -/
private theorem foldl_conj_sameAnswer {W E : Type*}
    (f : E → GSQuestion W) (es : List E) (init : GSQuestion W) (w v : W) :
    (es.foldl (λ acc e' => acc + f e') init).sameAnswer w v =
    (init.sameAnswer w v && es.all (λ e' => (f e').sameAnswer w v)) := by
  induction es generalizing init with
  | nil => simp
  | cons e' rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [add_eq_compose, QUD.compose_sameAnswer, List.all_cons, Bool.and_assoc]

/-- A pair-list question is equivalent to a conjunction of individual questions.

∀y. ?x. R(y,x) = ∧_{y∈Y} ?x. R(y,x)

The partition induced by the pair-list question agrees pointwise with the
conjunction of per-element individual questions. -/
theorem pairList_as_conjunction {W E : Type} [DecidableEq E] [BEq W]
    (plq : PairListQuestion W E) (w v : W) :
    plq.toGSQuestion.sameAnswer w v =
    (pairListAsConjunction plq.universalDomain plq.individualQuestion).sameAnswer w v := by
  -- Both sides are decidable and agree pointwise as Props; show via Iff bridge.
  apply Bool.eq_iff_iff.mpr
  rw [QUD.sameAnswer_eq_true_iff]
  -- Helper: list-equality of two maps decomposes to all-pointwise-equal
  have map_eq_iff_all : ∀ (l : List E) (f g : E → List Bool),
      List.map f l = List.map g l ↔ ∀ y ∈ l, f y = g y := by
    intro l f g
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.cons_eq_cons, List.mem_cons, forall_eq_or_imp]
      exact and_congr_right (fun _ => ih)
  -- Helper: foldl conjunction matches all-pointwise
  have foldl_iff : ∀ (l : List E) (f : E → GSQuestion W) (init : GSQuestion W),
      (l.foldl (λ acc e' => acc + f e') init).sameAnswer w v = true ↔
      init.sameAnswer w v = true ∧ ∀ y ∈ l, (f y).sameAnswer w v = true := by
    intro l f init
    induction l generalizing init with
    | nil => simp
    | cons y rest ih =>
      rw [List.foldl_cons, ih (init + f y)]
      simp only [add_eq_compose, QUD.compose_sameAnswer_iff, List.mem_cons,
                 forall_eq_or_imp, and_assoc]
  show (plq.toGSQuestion).r w v ↔ _
  match h : plq.universalDomain with
  | [] =>
    simp only [pairListAsConjunction, GSQuestion.trivial, QUD.trivial_sameAnswer]
    show plq.toGSQuestion.r w v ↔ True
    simp only [PairListQuestion.toGSQuestion, QUD.ofDecEq_r, h, List.map_nil]
  | e :: es =>
    simp only [pairListAsConjunction, foldl_iff, PairListQuestion.individualQuestion,
               QUD.ofDecEq_sameAnswer_iff]
    show plq.toGSQuestion.r w v ↔ _
    simp only [PairListQuestion.toGSQuestion, QUD.ofDecEq_r, h, map_eq_iff_all,
               List.mem_cons, forall_eq_or_imp]

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
  let mkQuestion (d : E) : GSQuestion W :=
    QUD.ofDecEq (λ w => cq.whDomain.filter (λ x => cq.relation w d x))
  let perDisjunct := cq.disjuncts.map mkQuestion
  match perDisjunct with
  | [] => LiftedTypes.LiftedQuestion.lift GSQuestion.trivial
  | q :: qs =>
    qs.foldl (λ acc q' =>
      LiftedTypes.LiftedQuestion.disj acc (LiftedTypes.LiftedQuestion.lift q'))
      (LiftedTypes.LiftedQuestion.lift q)

/-- Under NON-choice reading, worlds match iff ALL disjunct-answers match. -/
def ChoiceQuestion.toGSQuestion_nonchoice {W E : Type*} [DecidableEq E]
    (cq : ChoiceQuestion W E) : GSQuestion W :=
  QUD.ofDecEq (λ w => cq.disjuncts.map (λ d => cq.whDomain.map (λ x => cq.relation w d x)))

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
    (eq : ExistentialQuestion W E) : GSQuestion W :=
  QUD.ofDecEq (λ w =>
    eq.whDomain.filter λ x => eq.existentialDomain.any λ y => eq.relation w y x)

/-- Wide scope: for the "relevant" y, what's the answer?

This is similar to choice reading - the answer can vary based on
which existential witness is considered.

Since this involves existential quantification (which is like disjunction),
we must use the lifted type to avoid the transitivity problem. -/
def ExistentialQuestion.wideScope {W E : Type*} [BEq W] [DecidableEq E]
    (eq : ExistentialQuestion W E) : LiftedTypes.LiftedQuestion W :=
  -- Wide scope is a disjunction over the per-witness questions
  let mkQuestion (y : E) : GSQuestion W :=
    QUD.ofDecEq (λ w => eq.whDomain.filter (λ x => eq.relation w y x))
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
→ Answer: "John admires Smith, Mary admires Jones,..."
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

/-- Convert an ExistentialQuestion to a MentionSomeInterrogative.

This connects the scope-based existential question to the G&S Section 5
formal treatment of mention-some. -/
def ExistentialQuestion.toMentionSomeInterrogative {W E : Type*}
    (eq : ExistentialQuestion W E) : MentionSomeInterrogative W E :=
  { whDomain := eq.whDomain
  , abstract := λ w x => eq.existentialDomain.any λ y => eq.relation w y x
  }

/-- Wide-scope existential implies mention-some is licensed.

@cite{groenendijk-stokhof-1984}, Section 5: When an existential takes wide scope over the wh-phrase,
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
"Each professor recommended which student?" (marked)

**Choice Licensing**:
1. Disjunction/existential c-commands wh-phrase
2. The different disjuncts/witnesses are contextually salient
3. Conditional answers are felicitous

"Whom does John or Mary love?" ✓ (if both John and Mary are salient)

**Factors**:
- Attitude verbs: "know" licenses pair-list more than "wonder"
- Definiteness: definite universals (non-plural) are harder for pair-list;
  but *plural* definites license pair-list via both cumulation-and-elaboration
  and a genuine pair-list parse (@cite{johnston-2023})
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
  /-- Is the "universal" a plural definite DP (not an overt quantifier)?
      When `true`, pair-list responses are available via cumulation-and-
      elaboration regardless of definiteness (@cite{johnston-2023}). -/
  pluralDefinite : Bool := false

/-- Predict pair-list availability from factors.

    @cite{johnston-2023} shows that plural definites license pair-list
    responses even though they are definite: the cumulation-and-elaboration
    pathway produces pair-list surface form from a cumulative answer, and
    a genuine pair-list parse may also be available. -/
def predictPairList (factors : PairListFactors) : Bool :=
  let verbOK := match factors.attitudeVerb with
    | some "know" => true
    | some "wonder" => false
    | some "ask" => false
    | _ => true  -- matrix questions
  -- Plural definites always allow pair-list (via cumulation pathway)
  let defOK := factors.pluralDefinite || !factors.universalDefinite
  let focusOK := factors.contrastiveFocus
  verbOK && (defOK || focusOK)

end Semantics.Questions.ScopeReadings
