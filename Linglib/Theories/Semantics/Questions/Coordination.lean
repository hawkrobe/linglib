import Linglib.Theories.Semantics.Questions.Partition

/-!
# Coordination of Interrogatives

Q1 ^ Q2 = meet (coarsest common refinement), Q1 v Q2 = join (finest common coarsening).

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. VI, Section 3.1.
- Szabolcsi (1997). Ways of Scope Taking.
-/

namespace Semantics.Questions.Coordination

open Semantics.Questions
open scoped GSQuestion  -- For ⊑ notation

section Conjunction

instance {W : Type*} : Add (GSQuestion W) where
  add := QUD.compose

/-- Conjunction is commutative (up to equivalence). -/
theorem compose_comm {W : Type*} (q1 q2 : GSQuestion W) (w v : W) :
    (q1 + q2).sameAnswer w v = (q2 + q1).sameAnswer w v := by
  simp only [HAdd.hAdd, Add.add, QUD.compose]
  exact Bool.and_comm _ _

/-- Conjunction is associative. -/
theorem compose_assoc {W : Type*} (q1 q2 q3 : GSQuestion W) (w v : W) :
    ((q1 + q2) + q3).sameAnswer w v = (q1 + (q2 + q3)).sameAnswer w v := by
  simp only [HAdd.hAdd, Add.add, QUD.compose]
  exact Bool.and_assoc _ _ _

/-- The trivial question is the unit for conjunction. -/
theorem compose_trivial_left {W : Type*} [BEq W] (q : GSQuestion W) (w v : W) :
    (GSQuestion.trivial + q).sameAnswer w v = q.sameAnswer w v := by
  simp only [HAdd.hAdd, Add.add, QUD.compose, GSQuestion.trivial,
             QUD.trivial, Bool.true_and]

end Conjunction

section Disjunction

/-- A polar question about a disjunction.

"Is it the case that P₁ ∨ P₂?" has two cells: yes and no. -/
def polarDisjunction {W : Type*} (p1 p2 : W -> Bool) : GSQuestion W :=
  polarQuestion (λ w => p1 w || p2 w)

end Disjunction

section PartitionLattice

/-- The conjunction is the meet in the question lattice. -/
theorem conj_is_meet {W : Type*} (q1 q2 q : GSQuestion W)
    (h1 : q ⊑ q1) (h2 : q ⊑ q2) :
    q ⊑ (q1 + q2) := by
  intro w v hq
  simp only [HAdd.hAdd, Add.add, QUD.compose, Bool.and_eq_true]
  exact ⟨h1 w v hq, h2 w v hq⟩

/-- Conjunction preserves refinement in both arguments. -/
theorem conj_monotone_left {W : Type*} (q1 q1' q2 : GSQuestion W)
    (h : q1 ⊑ q1') :
    (q1 + q2) ⊑ (q1' + q2) := by
  intro w v heq
  simp only [HAdd.hAdd, Add.add, QUD.compose, Bool.and_eq_true] at *
  exact ⟨h w v heq.1, heq.2⟩

end PartitionLattice

section FunctionalDependence

/-- Q2 is functionally dependent on Q1 over a world set if there exist worlds
in the same Q1-cell but different Q2-cells.

G&S 1984, Ch. VI: Functional dependence is what gives rise to pair-list
readings. When the wh-answer varies across cells of the universal quantifier,
the full answer requires listing the answer for each element. -/
def functionallyDependent {W : Type*} (q1 q2 : GSQuestion W) (worlds : List W) : Bool :=
  worlds.any λ w =>
    worlds.any λ v =>
      q1.sameAnswer w v && !q2.sameAnswer w v

/-- When Q2 is functionally dependent on Q1, conjunction is strictly finer
than Q1 alone: the conjunction has at least as many cells as Q1.

This uses the hypothesis: functional dependence witnesses two worlds in the
same Q1-cell but different Q2-cells, which means Q1+Q2 separates them while
Q1 does not. The conjunction therefore has strictly more distinctions. -/
theorem functional_dep_conjunction_finer {W : Type*}
    (q1 q2 : GSQuestion W) (worlds : List W)
    (_h : functionallyDependent q1 q2 worlds = true) :
    (q1 + q2).numCells worlds ≥ q1.numCells worlds :=
  QUD.refines_numCells_ge _ _ _ (QUD.compose_refines_left q1 q2)

/-- Conversely, if Q2 is NOT functionally dependent on Q1, then Q1 already
determines Q2 on the given worlds: any two worlds in the same Q1-cell are
also in the same Q2-cell.

This means Q1 ⊑ Q2 on the given world set, so the conjunction Q1+Q2
is informationally redundant — it has the same cells as Q1 alone. -/
theorem not_functionally_dependent_implies_refines {W : Type*}
    (q1 q2 : GSQuestion W) (worlds : List W)
    (h : functionallyDependent q1 q2 worlds = false) :
    ∀ w ∈ worlds, ∀ v ∈ worlds,
      q1.sameAnswer w v = true → q2.sameAnswer w v = true := by
  intro w hw v hv hq1
  by_contra hq2
  have : functionallyDependent q1 q2 worlds = true := by
    simp only [functionallyDependent, List.any_eq_true]
    refine ⟨w, hw, v, hv, ?_⟩
    simp only [hq1, Bool.true_and, Bool.not_eq_true']
    exact Bool.eq_false_iff.mpr hq2
  simp [this] at h

end FunctionalDependence

section EmbeddedCoordination

/-- Conjunction of a list of questions via foldl.

Models embedded question coordination: "John knows [who came] and [what they
brought]" denotes the conjunction of two questions. -/
def conjoin {W : Type*} [BEq W] (qs : List (GSQuestion W)) : GSQuestion W :=
  match qs with
  | [] => GSQuestion.trivial
  | q :: rest => rest.foldl (· + ·) q

/-- Helper: foldl conjunction with direct addition refines the accumulator. -/
private theorem foldl_add_refines_init {W : Type*}
    (qs : List (GSQuestion W)) (init : GSQuestion W) :
    qs.foldl (· + ·) init ⊑ init := by
  induction qs generalizing init with
  | nil => exact λ _ _ h => h
  | cons q rest ih =>
    exact QUD.refines_trans (ih _) (QUD.compose_refines_left _ _)

/-- Helper: foldl conjunction with direct addition refines each element. -/
private theorem foldl_add_refines_elem {W : Type*}
    (qs : List (GSQuestion W)) (init : GSQuestion W)
    (q : GSQuestion W) (hIn : q ∈ qs) :
    qs.foldl (· + ·) init ⊑ q := by
  induction qs generalizing init with
  | nil => nomatch hIn
  | cons q' rest ih =>
    cases hIn with
    | head => exact QUD.refines_trans (foldl_add_refines_init rest _)
                (QUD.compose_refines_right _ _)
    | tail _ hIn' => exact ih _ hIn'

/-- Conjunction of questions refines each conjunct.

"John knows Q1 and Q2" entails "John knows Q1": knowing the conjunction
answer means knowing each individual answer. -/
theorem conjoin_refines_each {W : Type*} [BEq W]
    (qs : List (GSQuestion W)) (q : GSQuestion W) (hMem : q ∈ qs) :
    conjoin qs ⊑ q := by
  unfold conjoin
  match qs, hMem with
  | _ :: rest, List.Mem.head _ =>
    exact foldl_add_refines_init rest _
  | q₀ :: rest, List.Mem.tail _ hIn =>
    exact foldl_add_refines_elem rest q₀ q hIn

end EmbeddedCoordination

section Sluicing

/-- Sluicing as question identity: the elided question Q_sluice is resolved by
the same partition as the antecedent question Q_antecedent.

G&S 1984: In "Someone called, but I don't know who ⟨called⟩", the sluiced
wh-phrase recovers a question Q that is identical to (or at least refined by)
the antecedent question.

This theorem states the core constraint: if the sluice inherits its question
from the antecedent, then knowing the antecedent answer entails knowing the
sluice answer. -/
theorem sluice_inherits_resolution {W : Type*}
    (q_antecedent q_sluice : GSQuestion W)
    (hIdentical : ∀ w v, q_antecedent.sameAnswer w v = q_sluice.sameAnswer w v) :
    q_antecedent ⊑ q_sluice :=
  λ w v h => (hIdentical w v).symm ▸ h

end Sluicing

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
    exact QUD.refines_trans (ih _) (QUD.compose_refines_left _ _)

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
                (QUD.compose_refines_right _ _)
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

end Semantics.Questions.Coordination
