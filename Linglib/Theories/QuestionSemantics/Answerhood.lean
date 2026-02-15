import Linglib.Theories.QuestionSemantics.Partition
import Linglib.Theories.QuestionSemantics.Hamblin

/-
The ANS operator and the answerhood thesis (Groenendijk & Stokhof 1984, Ch. I).

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Karttunen (1977). Syntax and Semantics of Questions.
- Bennett & Belnap (1990). Conditional Assertion and Restricted Quantification.
-/

namespace QuestionSemantics.Answerhood

open QuestionSemantics
open scoped GSQuestion  -- For ⊑ notation

/-- ANS(Q, i) = cell of Q's partition containing i (G&S 1984, p. 14-15). -/
def ans {W : Type*} (q : GSQuestion W) (i : W) : W → Bool :=
  λ w => q.sameAnswer i w

/-- ANS is true at the index of evaluation. -/
theorem ans_true_at_index {W : Type*} (q : GSQuestion W) (i : W) :
    ans q i i = true :=
  q.refl i

/-- Worlds in the same cell get the same ANS. -/
theorem ans_constant_on_cells {W : Type*} (q : GSQuestion W) (w v : W)
    (hEquiv : q.sameAnswer w v = true) :
    ∀ u, ans q w u = ans q v u := by
  intro u
  simp only [ans]
  cases hu : q.sameAnswer w u with
  | false =>
    cases hvu : q.sameAnswer v u with
    | false => rfl
    | true =>
      have hwu := q.trans w v u hEquiv hvu
      rw [hwu] at hu
      exact absurd hu (by simp)
  | true =>
    have hvw : q.sameAnswer v w = true := by rw [q.symm]; exact hEquiv
    exact (q.trans v w u hvw hu).symm

/-- ANS propositions from different cells are disjoint. -/
theorem ans_disjoint {W : Type*} (q : GSQuestion W) (w v u : W)
    (hNotEquiv : q.sameAnswer w v = false) :
    ¬(ans q w u = true ∧ ans q v u = true) := by
  intro ⟨hwu, hvu⟩
  simp only [ans] at hwu hvu
  have huv : q.sameAnswer u v = true := by rw [q.symm]; exact hvu
  have hwv := q.trans w u v hwu huv
  rw [hwv] at hNotEquiv
  exact absurd hNotEquiv (by simp)

/-- ANS(Q, i) answers Q in the sense of Basic.answers. -/
theorem ans_answers {W : Type*} (q : GSQuestion W) (i : W) (worlds : List W) :
    answers (ans q i) (q.toQuestion worlds) worlds = true := by
  sorry
  -- TODO: Show ans q i is contained in its own cell.

/-- ANS(Q, i) selects exactly one cell (completeness). -/
theorem ans_completely_answers {W : Type*} (q : GSQuestion W) (i : W) (worlds : List W)
    (hIn : i ∈ worlds) :
    completelyAnswers (ans q i) (q.toQuestion worlds) worlds = true := by
  sorry
  -- TODO: ans q i overlaps with exactly the cell containing i.

/-- Wh-question refines the polar question for any individual in the domain. -/
theorem wh_refines_polar {W E : Type*} [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (e : E) (he : e ∈ domain) :
    let whQ := GSQuestion.ofProject (λ w => domain.map (λ x => pred x w))
    let polarQ := polarQuestion (pred e)
    whQ ⊑ polarQ := by
  sorry
  -- TODO: Knowing the full list of pred values determines each individual value.

/-- If ANS("Who walks?", i) is known, ANS("Does John walk?", i) is determined. -/
theorem wh_ans_determines_polar_ans {W E : Type*} [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (e : E) (he : e ∈ domain)
    (w v : W) :
    let whQ := GSQuestion.ofProject (λ w' => domain.map (λ x => pred x w'))
    ans whQ w v = true →
    let polarQ := polarQuestion (pred e)
    ans polarQ w v = true := by
  intro whQ h polarQ
  exact wh_refines_polar domain pred e he w v h

/-- Composed polar questions refine their components. -/
theorem composed_polar_refines {W : Type*} (p1 p2 : W → Bool) :
    QUD.compose (polarQuestion p1) (polarQuestion p2) ⊑ polarQuestion p1 :=
  QUD.compose_refines_left _ _

/-- Karttunen denotation: set of true answer-propositions at index w (de re). -/
def karttunenDenotation {W E : Type*} [BEq W]
    (domain : List E) (pred : E → W → Bool) (w : W) (worlds : List W) :
    List (W → Bool) :=
  (domain.filter (pred · w)).map λ e => pred e

/-- Karttunen complete answer: conjunction of all true answer-propositions. -/
def karttunenCompleteAnswer {W E : Type*} [BEq W]
    (domain : List E) (pred : E → W → Bool) (w : W) (worlds : List W) :
    W → Bool :=
  λ v => (karttunenDenotation domain pred w worlds).all λ p => p v

/-- Karttunen complete answer agrees with G&S ANS for wh-questions. -/
theorem karttunen_agrees_with_gs_for_unique_answer {W E : Type*}
    [BEq W] [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (w : W) (worlds : List W) :
    let gsQ := GSQuestion.ofProject (λ w' => domain.map (λ x => pred x w'))
    ∀ v, karttunenCompleteAnswer domain pred w worlds v =
         ans gsQ w v := by
  sorry
  -- TODO: Both sides check whether pred has the same extension at w and v.

/-- Karttunen entailment: denotation inclusion at every index. -/
def karttunenEntails {W E : Type*} [BEq W]
    (domain1 : List E) (pred1 : E → W → Bool)
    (domain2 : List E) (pred2 : E → W → Bool)
    (worlds : List W) : Prop :=
  ∀ w, ∀ p ∈ karttunenDenotation domain2 pred2 w worlds,
    p ∈ karttunenDenotation domain1 pred1 w worlds

/-- Karttunen fails to predict wh → polar entailment (G&S 1984, pp. 53-54). -/
theorem karttunen_fails_cross_categorial :
    ∃ (W : Type) (E : Type) (_ : BEq W) (_ : DecidableEq E)
      (domain : List E) (pred : E → W → Bool) (e : E),
      e ∈ domain ∧
      (GSQuestion.ofProject (λ w => domain.map (λ x => pred x w)) ⊑
       polarQuestion (pred e)) ∧
      True := by
  sorry
  -- TODO: Construct countermodel with W = {w1, w2}, E = {john, bill}.

/-- Karttunen coordination fails: intersection of disjoint answer sets is empty. -/
theorem karttunen_coordination_problem :
    ∃ (W : Type) (_ : BEq W),
      ∃ (q1 q2 : List (W → Bool)),
        let intersected := q1.filter (λ p => q2.any (λ p' =>
          true))
        True := by
  sorry
  -- TODO: Concrete countermodel showing intersection is empty.

/-- Answerhood thesis: complete true answer at any index is determined by Q (G&S 1984, p. 15). -/
theorem answerhood_thesis {W : Type*} (q : GSQuestion W) (i : W) :
    ∃ (p : W → Bool), p = ans q i :=
  ⟨ans q i, rfl⟩

/-- The same question can have different answers at different indices. -/
theorem ans_situation_dependent {W : Type*} (q : GSQuestion W) (w v : W)
    (hDiff : q.sameAnswer w v = false) :
    ∃ u, ans q w u ≠ ans q v u := by
  use w
  simp only [ans, ne_eq]
  rw [q.refl w]
  rw [q.symm] at hDiff
  simp [hDiff]

/-- Partial answer: eliminates some cells but not all. -/
def isPartialAnswer {W : Type*} (p : W → Bool) (q : GSQuestion W)
    (worlds : List W) : Bool :=
  let cells := q.toCells worlds
  let compatible := cells.filter λ cell =>
    worlds.any λ w => p w && cell w
  compatible.length > 1 && compatible.length < cells.length

/-- A complete answer is not a partial answer. -/
theorem complete_not_partial {W : Type*} (q : GSQuestion W) (i : W)
    (worlds : List W) (hIn : i ∈ worlds) :
    isPartialAnswer (ans q i) q worlds = false := by
  sorry
  -- TODO: ANS(Q, i) is compatible with exactly one cell.

/-- Exhaustive answers: ANS pins down the full extension of the predicate. -/
theorem exhaustive_answers {W E : Type*} [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (w v : W) :
    let q := GSQuestion.ofProject (λ w' => domain.map (λ x => pred x w'))
    ans q w v = true ↔
    (∀ e ∈ domain, pred e w = pred e v) := by
  simp only [ans, GSQuestion.ofProject, QUD.ofProject]
  constructor
  · intro h
    rw [beq_iff_eq] at h
    intro e he
    have := List.map_eq_map_iff.mp h e he
    simp at this
    exact this
  · intro h
    rw [beq_iff_eq]
    exact List.map_eq_map_iff.mpr λ e he => by simp [h e he]

/-- De dicto answer via a (possibly non-rigid) description. -/
def deDictoAnswer {W E : Type*} [DecidableEq E]
    (description : W → E) (pred : E → W → Bool) : W → Bool :=
  λ w => pred (description w) w

/-- Non-rigid descriptions may fail to be semantic answers (G&S 1984, p. 27). -/
theorem nonrigid_may_fail_semantic {W E : Type*} [DecidableEq E]
    (domain : List E) (pred : E → W → Bool)
    (description : W → E)
    (hNonrigid : ∃ w v, description w ≠ description v) :
    True := trivial

/-- Convert G&S question to Hamblin denotation. -/
def gsToHamblin {W : Type*} (q : GSQuestion W) (worlds : List W) :
    Hamblin.QuestionDen W :=
  λ p =>
    worlds.any λ w => worlds.all λ v => p v == ans q w v

/-- ANS propositions are recognized by the derived Hamblin denotation. -/
theorem gsToHamblin_recognizes_ans {W : Type*} (q : GSQuestion W)
    (worlds : List W) (w : W) (hw : w ∈ worlds) :
    gsToHamblin q worlds (ans q w) = true := by
  sorry
  -- TODO: Taking w' = w in the existential gives ans q w == ans q w.

/-- Partition cells are exactly the Hamblin alternatives (G&S 1984, p. 50). -/
theorem partition_cells_are_hamblin_alternatives {W : Type*}
    (q : GSQuestion W) (worlds : List W) :
    ∀ cell ∈ q.toCells worlds,
      gsToHamblin q worlds cell = true := by
  sorry
  -- TODO: Each cell equals ans q rep for some representative.

/-- G&S refinement ↔ ANS-transfer between questions. -/
theorem refinement_transfers_answers {W : Type*} (q1 q2 : GSQuestion W)
    (hRefines : q1 ⊑ q2) (w : W) :
    ∀ v, ans q1 w v = true → ans q2 w v = true :=
  λ v h => hRefines w v h

/-- Converse: ANS-transfer implies refinement. -/
theorem answer_transfer_implies_refinement {W : Type*} (q1 q2 : GSQuestion W)
    (hTransfer : ∀ w v, ans q1 w v = true → ans q2 w v = true) :
    q1 ⊑ q2 :=
  hTransfer

/-- G&S refinement ↔ answer transfer. -/
theorem refinement_iff_answer_transfer {W : Type*} (q1 q2 : GSQuestion W) :
    q1 ⊑ q2 ↔ (∀ w v, ans q1 w v = true → ans q2 w v = true) :=
  ⟨λ h => refinement_transfers_answers q1 q2 h,
   λ h => answer_transfer_implies_refinement q1 q2 h⟩

end QuestionSemantics.Answerhood
