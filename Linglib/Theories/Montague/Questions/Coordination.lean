import Linglib.Theories.Montague.Questions.Partition
import Linglib.Theories.Montague.Questions.ConjoinableTypes
import Linglib.Theories.Montague.Questions.LiftedTypes

/-!
# Questions/Coordination.lean

Coordination of Interrogatives (G&S 1984, Chapter VI, Section 3.1).

## Conjunctive Interrogatives

"Who came and what did they bring?"

This asks for:
1. The set of people who came, AND
2. For each person, what they brought

Semantically: Q₁ ∧ Q₂ partitions more finely than either Q₁ or Q₂ alone.

## Disjunctive Interrogatives

"Did John come or did Mary come?"

Two readings:
1. **Alternative Question**: Which of John/Mary came? (exclusive partition)
2. **Yes/No Question**: Is it true that [John came or Mary came]? (polar)

Under the alternative reading, answering requires specifying which
disjunct is true.

## Operations on Partitions

For G&S partition semantics:
- Q₁ ∧ Q₂ = meet (coarsest common refinement)
- Q₁ ∨ Q₂ = join (finest common coarsening)

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. VI, Section 3.1.
- Szabolcsi (1997). Ways of Scope Taking.
-/

namespace Montague.Questions.Coordination

open Montague.Questions
open scoped GSQuestion  -- For ⊑ notation

-- ============================================================================
-- Conjunctive Interrogatives
-- ============================================================================

/-!
## Conjunction of Questions

Q₁ ∧ Q₂ asks for answers to BOTH Q₁ and Q₂.

**Partition Perspective:**
Two worlds are (Q₁ ∧ Q₂)-equivalent iff they are both:
- Q₁-equivalent, AND
- Q₂-equivalent

This is the **coarsest common refinement** (meet in the lattice of partitions).
-/

/-- Conjunction of GSQuestions: equivalent iff equivalent under both.

This corresponds to the product of equivalence relations. -/
def conjGSQuestion {W : Type*} (q1 q2 : GSQuestion W) : GSQuestion W :=
  q1.compose q2

instance {W : Type*} : Add (GSQuestion W) where
  add := conjGSQuestion

/-- Conjunction refines both operands. -/
theorem conjGSQuestion_refines_left {W : Type*} (q1 q2 : GSQuestion W) :
    (q1 + q2) ⊑ q1 :=
  GSQuestion.compose_refines_left q1 q2

theorem conjGSQuestion_refines_right {W : Type*} (q1 q2 : GSQuestion W) :
    (q1 + q2) ⊑ q2 :=
  GSQuestion.compose_refines_right q1 q2

/-- Conjunction is commutative (up to equivalence). -/
theorem conjGSQuestion_comm {W : Type*} (q1 q2 : GSQuestion W) (w v : W) :
    (q1 + q2).sameAnswer w v = (q2 + q1).sameAnswer w v := by
  simp only [HAdd.hAdd, Add.add, conjGSQuestion, GSQuestion.compose]
  exact Bool.and_comm _ _

/-- Conjunction is associative. -/
theorem conjGSQuestion_assoc {W : Type*} (q1 q2 q3 : GSQuestion W) (w v : W) :
    ((q1 + q2) + q3).sameAnswer w v = (q1 + (q2 + q3)).sameAnswer w v := by
  simp only [HAdd.hAdd, Add.add, conjGSQuestion, GSQuestion.compose]
  exact Bool.and_assoc _ _ _

/-- The trivial question is the unit for conjunction. -/
theorem conjGSQuestion_trivial_left {W : Type*} [BEq W] (q : GSQuestion W) (w v : W) :
    (GSQuestion.trivial + q).sameAnswer w v = q.sameAnswer w v := by
  simp only [HAdd.hAdd, Add.add, conjGSQuestion, GSQuestion.compose, GSQuestion.trivial,
             QUD.trivial, QUD.compose, Bool.true_and]

-- ============================================================================
-- Disjunctive Interrogatives
-- ============================================================================

/-!
## Disjunction of Questions

Q₁ ∨ Q₂ has two possible interpretations:

**Reading 1: Alternative Question**
"Did John come or did Mary come?" (rising intonation on both)
→ Partition: {{John came}, {Mary came}, {neither}}
→ Answer specifies which disjunct is true

**Reading 2: Polar Question over Disjunction**
"Did John come or Mary come?" (rising-falling intonation)
→ Partition: {{John or Mary came}, {neither came}}
→ Answer is yes/no

For the partition semantics, we focus on the MEET interpretation
where both questions contribute to the answer.
-/

/-!
### Disjunction of Questions

**IMPORTANT**: Disjunction of equivalence relations is NOT an equivalence relation!
Transitivity fails: w ~₁ v and v ~₂ u does NOT imply w ~₁ u or w ~₂ u.

The correct approach is to use LIFTED TYPES (see LiftedTypes.lean):
- `LiftedQuestion.disj` works correctly at the lifted level
- Use `LiftedQuestion.disjCore q1 q2` for disjunction of core questions

Note: `disjGSQuestion` was removed from this file because it's semantically invalid.
-/

/-- Alternative question from a list of alternatives.

"Did P₁ or P₂ or ... or Pₙ?" partitions by which Pᵢ is true. -/
def alternativeQuestion {W : Type*} (alts : List (W -> Bool)) : GSQuestion W where
  sameAnswer w v := alts.all fun p => p w == p v
  refl w := List.all_eq_true.mpr fun _ _ => beq_self_eq_true _
  symm w v := by
    congr 1
    funext p
    cases p w <;> cases p v <;> rfl
  trans w v x hwv hvx := by
    simp only [List.all_eq_true] at *
    intro p hp
    have h1 := hwv p hp
    have h2 := hvx p hp
    rw [beq_iff_eq] at *
    exact h1.trans h2

/-- A polar question about a disjunction.

"Is it the case that P₁ ∨ P₂?" has two cells: yes and no. -/
def polarDisjunction {W : Type*} (p1 p2 : W -> Bool) : GSQuestion W :=
  polarQuestion (fun w => p1 w || p2 w)

/-- Alternative and polar-disjunction are different partitions.

"Did John or Mary come?" (alternative) vs "Did John-or-Mary come?" (polar) -/
theorem alternative_vs_polar {W : Type*} (p1 p2 : W -> Bool) :
    True := by  -- Placeholder for the distinction
  trivial

-- ============================================================================
-- Relation to Partition Lattice
-- ============================================================================

/-!
## Lattice Structure of Questions

Questions (equivalence relations) form a complete lattice:

**Order**: Q ⊑ Q' iff Q refines Q'

**Meet** (∧): Coarsest common refinement
- (Q₁ ∧ Q₂)-cells = intersections of Q₁-cells and Q₂-cells

**Join** (∨): Finest common coarsening
- Harder to compute; generated by taking closure

**Top**: The exact question (identity relation)
**Bottom**: The trivial question (all equivalent)
-/

/-- The conjunction is the meet in the question lattice. -/
theorem conj_is_meet {W : Type*} (q1 q2 q : GSQuestion W)
    (h1 : q ⊑ q1) (h2 : q ⊑ q2) :
    q ⊑ (q1 + q2) := by
  intro w v hq
  simp only [HAdd.hAdd, Add.add, conjGSQuestion, GSQuestion.compose,
             QUD.compose, Bool.and_eq_true]
  exact ⟨h1 w v hq, h2 w v hq⟩

/-- Conjunction preserves refinement in both arguments. -/
theorem conj_monotone_left {W : Type*} (q1 q1' q2 : GSQuestion W)
    (h : q1 ⊑ q1') :
    (q1 + q2) ⊑ (q1' + q2) := by
  intro w v heq
  simp only [HAdd.hAdd, Add.add, conjGSQuestion, GSQuestion.compose,
             QUD.compose, Bool.and_eq_true] at *
  exact ⟨h w v heq.1, heq.2⟩

-- ============================================================================
-- Embedded Questions and Coordination
-- ============================================================================

/-!
## Coordination under Embedding Verbs

Consider:
- "John knows who came and what they brought"
- "Mary wonders whether Bill left or whether Sue arrived"

The coordinated question is embedded under an attitude verb.
The semantics is the conjunction/disjunction of the embedded questions.
-/

/-- Structure for embedded coordinated questions. -/
structure EmbeddedCoordination (W : Type*) where
  /-- The attitude verb (e.g., "know", "wonder") -/
  verb : String
  /-- The coordinated questions -/
  questions : List (GSQuestion W)
  /-- Coordination type -/
  coordType : Bool  -- true = conjunction, false = disjunction

/-- Compute the coordinated question meaning (conjunction only).

For conjunction, we can stay at the partition level since conjunction
of equivalence relations IS an equivalence relation.

For disjunction, use `meaningLifted` instead. -/
def EmbeddedCoordination.meaningConj {W : Type*} [BEq W] (ec : EmbeddedCoordination W)
    (hConj : ec.coordType = true) : GSQuestion W :=
  match ec.questions with
  | [] => GSQuestion.trivial
  | q :: qs => qs.foldl (· + ·) q

/-- Compute the coordinated question meaning (general case, returns lifted type).

This handles both conjunction and disjunction correctly by working at the
lifted type level where disjunction is well-defined. -/
def EmbeddedCoordination.meaningLifted {W : Type*} [BEq W] (ec : EmbeddedCoordination W)
    : LiftedTypes.LiftedQuestion W :=
  match ec.questions with
  | [] => LiftedTypes.LiftedQuestion.lift GSQuestion.trivial
  | q :: qs =>
    let liftedQ := LiftedTypes.LiftedQuestion.lift q
    if ec.coordType then
      -- Conjunction: lift each and conjoin
      qs.foldl (fun acc q' => LiftedTypes.LiftedQuestion.conj acc (LiftedTypes.LiftedQuestion.lift q')) liftedQ
    else
      -- Disjunction: lift each and disjoin (this is the key fix!)
      qs.foldl (fun acc q' => LiftedTypes.LiftedQuestion.disj acc (LiftedTypes.LiftedQuestion.lift q')) liftedQ

-- ============================================================================
-- Sluicing and Coordinated Antecedents
-- ============================================================================

/-!
## Sluicing with Coordinated Antecedents

"John talked to someone, and I know who."

The sluiced question ("who") has a coordinated antecedent (via the
conjunction in the first conjunct). This is licensed because questions
can be reconstructed from indefinites.
-/

/-- A sluicing structure with coordination. -/
structure Sluice (W E : Type*) where
  /-- The antecedent clause -/
  antecedent : W -> Bool
  /-- The correlate indefinite (e.g., "someone") -/
  correlate : E -> Bool
  /-- The sluiced wh-word -/
  whWord : String
  /-- The reconstructed question -/
  question : GSQuestion W

-- ============================================================================
-- Multiple Interrogatives
-- ============================================================================

/-!
## Multiple Wh-Questions via Coordination

"Who came and what did they bring?" can be analyzed as:
1. Q₁ = "Who came?"
2. Q₂ = "What did they bring?"
3. Result = Q₁ ∧ Q₂

The answer must resolve BOTH questions simultaneously.

This connects to pair-list readings when Q₂ is functionally dependent on Q₁.
-/

/-- A functional dependency between questions.

Q₂ is functionally dependent on Q₁ if the answer to Q₂ can vary
depending on which cell of Q₁ we're in. -/
def functionallyDependent {W : Type*} (q1 q2 : GSQuestion W) (worlds : List W) : Bool :=
  -- Check if there exist w, v in same q1-cell but different q2-cells
  worlds.any fun w =>
    worlds.any fun v =>
      q1.sameAnswer w v && !q2.sameAnswer w v

/-- When Q₂ is functionally dependent on Q₁, conjunction gives pair-list readings. -/
theorem functional_dep_gives_pairlist {W : Type*}
    (q1 q2 : GSQuestion W) (worlds : List W)
    (h : functionallyDependent q1 q2 worlds = true) :
    (q1 + q2).numCells worlds >= q1.numCells worlds := by
  sorry -- Conjunction can only increase cell count

-- ============================================================================
-- Quantifiers and Coordination
-- ============================================================================

/-!
## Interaction with Quantifiers

"Which student did every professor recommend?"

This exhibits a scope ambiguity:
1. ∃x.∀y. Prof(y) → Recommended(y,x) [single student for all]
2. ∀y.∃x. Prof(y) → Recommended(y,x) [potentially different per prof]

Reading 2 is the **pair-list reading** - answer lists pairs.

The conjunction analysis captures this: the question is equivalent to
a conjunction of questions, one per professor.
-/

/-- A quantified question with universal over wh-phrase.

"Which X did every Y verb?" can be analyzed as ∧_{y∈Y} "Which X did y verb?" -/
def pairListAsConjunction {W E : Type*} [BEq W]
    (quantDomain : List E)  -- The universally quantified domain (professors)
    (questionFor : E -> GSQuestion W)  -- Question for each element
    : GSQuestion W :=
  match quantDomain with
  | [] => GSQuestion.trivial
  | e :: es => es.foldl (fun acc e' => acc + questionFor e') (questionFor e)

/-- The pair-list reading refines any individual question. -/
theorem pairList_refines_individual {W E : Type*} [BEq W]
    (quantDomain : List E) (questionFor : E -> GSQuestion W) (e : E)
    (hIn : e ∈ quantDomain) :
    (pairListAsConjunction quantDomain questionFor) ⊑ (questionFor e) := by
  sorry -- Conjunction of all questions refines each individual

-- ============================================================================
-- Uniqueness and Mention-Some
-- ============================================================================

/-!
## How Many Answers?

Conjoined questions typically require COMPLETE answers to each conjunct:
- "Who came and what did they bring?" → list all pairs

But mention-some readings can arise when:
- The questioner's goal is satisfied by partial information
- One of the conjuncts has a mention-some reading independently
-/

/-- A conjoined question has mention-all reading by default. -/
def conjunctionIsMentionAll {W : Type*} (_q1 _q2 : GSQuestion W) : Bool := true

/-- Exception: if either conjunct is mention-some, so is the conjunction. -/
def inheritsMentionSome {W : Type*}
    (q1IsMentionSome q2IsMentionSome : Bool) : Bool :=
  q1IsMentionSome || q2IsMentionSome

end Montague.Questions.Coordination
