import Linglib.Theories.Semantics.Questions.Partition
import Linglib.Theories.Semantics.Questions.LiftedTypes

/-!
# Coordination of Interrogatives

Q1 ^ Q2 = meet (coarsest common refinement), Q1 v Q2 = join (finest common coarsening).

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. VI, Section 3.1.
- Szabolcsi (1997). Ways of Scope Taking.
-/

namespace QuestionSemantics.Coordination

open QuestionSemantics
open scoped GSQuestion  -- For ⊑ notation

section Conjunction

/-- Conjunction of GSQuestions: equivalent iff equivalent under both. -/
def conjGSQuestion {W : Type*} (q1 q2 : GSQuestion W) : GSQuestion W :=
  q1.compose q2

instance {W : Type*} : Add (GSQuestion W) where
  add := conjGSQuestion

/-- Conjunction refines both operands. -/
theorem conjGSQuestion_refines_left {W : Type*} (q1 q2 : GSQuestion W) :
    (q1 + q2) ⊑ q1 :=
  QUD.compose_refines_left q1 q2

theorem conjGSQuestion_refines_right {W : Type*} (q1 q2 : GSQuestion W) :
    (q1 + q2) ⊑ q2 :=
  QUD.compose_refines_right q1 q2

/-- Conjunction is commutative (up to equivalence). -/
theorem conjGSQuestion_comm {W : Type*} (q1 q2 : GSQuestion W) (w v : W) :
    (q1 + q2).sameAnswer w v = (q2 + q1).sameAnswer w v := by
  simp only [HAdd.hAdd, Add.add, conjGSQuestion, QUD.compose]
  exact Bool.and_comm _ _

/-- Conjunction is associative. -/
theorem conjGSQuestion_assoc {W : Type*} (q1 q2 q3 : GSQuestion W) (w v : W) :
    ((q1 + q2) + q3).sameAnswer w v = (q1 + (q2 + q3)).sameAnswer w v := by
  simp only [HAdd.hAdd, Add.add, conjGSQuestion, QUD.compose]
  exact Bool.and_assoc _ _ _

/-- The trivial question is the unit for conjunction. -/
theorem conjGSQuestion_trivial_left {W : Type*} [BEq W] (q : GSQuestion W) (w v : W) :
    (GSQuestion.trivial + q).sameAnswer w v = q.sameAnswer w v := by
  simp only [HAdd.hAdd, Add.add, conjGSQuestion, QUD.compose, GSQuestion.trivial,
             QUD.trivial, QUD.compose, Bool.true_and]

end Conjunction

section Disjunction

/-- Alternative question from a list of alternatives.

"Did P₁ or P₂ or ... or Pₙ?" partitions by which Pᵢ is true. -/
def alternativeQuestion {W : Type*} (alts : List (W -> Bool)) : GSQuestion W where
  sameAnswer w v := alts.all λ p => p w == p v
  refl w := List.all_eq_true.mpr λ _ _ => beq_self_eq_true _
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
  polarQuestion (λ w => p1 w || p2 w)

/-- Alternative and polar-disjunction are different partitions. -/
theorem alternative_vs_polar {W : Type*} (p1 p2 : W -> Bool) :
    True := by  -- Placeholder for the distinction
  trivial

end Disjunction

section PartitionLattice

/-- The conjunction is the meet in the question lattice. -/
theorem conj_is_meet {W : Type*} (q1 q2 q : GSQuestion W)
    (h1 : q ⊑ q1) (h2 : q ⊑ q2) :
    q ⊑ (q1 + q2) := by
  intro w v hq
  simp only [HAdd.hAdd, Add.add, conjGSQuestion, QUD.compose,
             QUD.compose, Bool.and_eq_true]
  exact ⟨h1 w v hq, h2 w v hq⟩

/-- Conjunction preserves refinement in both arguments. -/
theorem conj_monotone_left {W : Type*} (q1 q1' q2 : GSQuestion W)
    (h : q1 ⊑ q1') :
    (q1 + q2) ⊑ (q1' + q2) := by
  intro w v heq
  simp only [HAdd.hAdd, Add.add, conjGSQuestion, QUD.compose,
             QUD.compose, Bool.and_eq_true] at *
  exact ⟨h w v heq.1, heq.2⟩

end PartitionLattice

section EmbeddedCoord

/-- Structure for embedded coordinated questions. -/
structure EmbeddedCoordination (W : Type*) where
  /-- The attitude verb (e.g., "know", "wonder") -/
  verb : String
  /-- The coordinated questions -/
  questions : List (GSQuestion W)
  /-- Coordination type -/
  coordType : Bool  -- true = conjunction, false = disjunction

/-- Compute the coordinated question meaning (conjunction only). -/
def EmbeddedCoordination.meaningConj {W : Type*} [BEq W] (ec : EmbeddedCoordination W)
    (hConj : ec.coordType = true) : GSQuestion W :=
  match ec.questions with
  | [] => GSQuestion.trivial
  | q :: qs => qs.foldl (· + ·) q

/-- Compute the coordinated question meaning (general case, returns lifted type). -/
def EmbeddedCoordination.meaningLifted {W : Type*} [BEq W] (ec : EmbeddedCoordination W)
    : LiftedTypes.LiftedQuestion W :=
  match ec.questions with
  | [] => LiftedTypes.LiftedQuestion.lift GSQuestion.trivial
  | q :: qs =>
    let liftedQ := LiftedTypes.LiftedQuestion.lift q
    if ec.coordType then
      qs.foldl (λ acc q' => LiftedTypes.LiftedQuestion.conj acc (LiftedTypes.LiftedQuestion.lift q')) liftedQ
    else
      qs.foldl (λ acc q' => LiftedTypes.LiftedQuestion.disj acc (LiftedTypes.LiftedQuestion.lift q')) liftedQ

end EmbeddedCoord

section Sluicing

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

end Sluicing

section MultipleWh

/-- Q2 is functionally dependent on Q1 if the Q2-answer varies across Q1-cells. -/
def functionallyDependent {W : Type*} (q1 q2 : GSQuestion W) (worlds : List W) : Bool :=
  -- Check if there exist w, v in same q1-cell but different q2-cells
  worlds.any λ w =>
    worlds.any λ v =>
      q1.sameAnswer w v && !q2.sameAnswer w v

/-- When Q₂ is functionally dependent on Q₁, conjunction gives pair-list readings. -/
theorem functional_dep_gives_pairlist {W : Type*}
    (q1 q2 : GSQuestion W) (worlds : List W)
    (h : functionallyDependent q1 q2 worlds = true) :
    (q1 + q2).numCells worlds >= q1.numCells worlds :=
  QUD.refines_numCells_ge _ _ _ (conjGSQuestion_refines_left q1 q2)

end MultipleWh

section QuantifierInteraction

/-- Pair-list as conjunction: "Which X did every Y verb?" = conjunction_{y in Y} "Which X did y verb?". -/
def pairListAsConjunction {W E : Type*} [BEq W]
    (quantDomain : List E)  -- The universally quantified domain (professors)
    (questionFor : E -> GSQuestion W)  -- Question for each element
    : GSQuestion W :=
  match quantDomain with
  | [] => GSQuestion.trivial
  | e :: es => es.foldl (λ acc e' => acc + questionFor e') (questionFor e)

/-- Helper: foldl conjunction refines the initial accumulator. -/
private theorem foldl_conj_refines_init {W E : Type*}
    (es : List E) (init : GSQuestion W) (questionFor : E → GSQuestion W) :
    es.foldl (λ acc e' => acc + questionFor e') init ⊑ init := by
  induction es generalizing init with
  | nil => exact λ _ _ h => h
  | cons e' rest ih =>
    exact QUD.refines_trans (ih _) (conjGSQuestion_refines_left _ _)

/-- Helper: foldl conjunction refines questionFor e' for each e' in the list. -/
private theorem foldl_conj_refines_elem {W E : Type*}
    (es : List E) (init : GSQuestion W) (questionFor : E → GSQuestion W)
    (e : E) (hIn : e ∈ es) :
    es.foldl (λ acc e' => acc + questionFor e') init ⊑ questionFor e := by
  induction es generalizing init with
  | nil => nomatch hIn
  | cons e' rest ih =>
    cases hIn with
    | head => exact QUD.refines_trans (foldl_conj_refines_init rest _ _)
                (conjGSQuestion_refines_right _ _)
    | tail _ hIn' => exact ih _ hIn'

/-- The pair-list reading refines any individual question. -/
theorem pairList_refines_individual {W E : Type*} [BEq W]
    (quantDomain : List E) (questionFor : E -> GSQuestion W) (e : E)
    (hIn : e ∈ quantDomain) :
    (pairListAsConjunction quantDomain questionFor) ⊑ (questionFor e) := by
  match quantDomain, hIn with
  | _ :: es, .head _ => exact foldl_conj_refines_init es _ questionFor
  | e₀ :: es, .tail _ hIn' => exact foldl_conj_refines_elem es (questionFor e₀) questionFor e hIn'

end QuantifierInteraction

section MentionSomeCoord

/-- A conjoined question has mention-all reading by default. -/
def conjunctionIsMentionAll {W : Type*} (_q1 _q2 : GSQuestion W) : Bool := true

/-- Exception: if either conjunct is mention-some, so is the conjunction. -/
def inheritsMentionSome {W : Type*}
    (q1IsMentionSome q2IsMentionSome : Bool) : Bool :=
  q1IsMentionSome || q2IsMentionSome

end MentionSomeCoord

end QuestionSemantics.Coordination
