import Linglib.Core.Question.Partition.Constructors

/-!
# @cite{groenendijk-stokhof-1984}: Studies on the Semantics of Questions
@cite{belnap-1982}

Single-paper formalisation of the partition-semantics theorems from
@cite{groenendijk-stokhof-1984} (Ch. I), formulated over the
`GSQuestion W` substrate. The substrate primitive `ans` and its
basic algebraic properties live in
`Core/Question/Partition/Cells.lean`; this file owns the paper-anchored
theorems about refinement, exhaustivity, and de dicto answers.

## Theorems

* **wh_refines_polar** (p. ~13): a wh-question refines the polar
  question for any individual in the domain. Knowing the answer to
  *Who walks?* determines the answer to *Does John walk?*.
* **answerhood_thesis** (p. 15): the complete true answer at any
  index is determined by Q (functionally projected).
* **ans_situation_dependent**: the same question can have different
  answers at different worlds.
* **exhaustive_answers**: ANS pins down the full extension of the
  predicate.
* **nonrigid_may_fail_semantic** (p. 27): non-rigid descriptions are
  not guaranteed to give semantic (partition-based) answers.
* **refinement_iff_answer_transfer**: G&S refinement is equivalent to
  ANS-transfer between questions.
-/

namespace Phenomena.Questions.Studies.GroenendijkStokhof1984

open Semantics.Questions
open scoped GSQuestion  -- For ⊑ notation

/-! ### Wh ↔ polar refinement -/

/-- Wh-question refines the polar question for any individual in the
    domain. Core result of @cite{groenendijk-stokhof-1984}: knowing the
    answer to *Who walks?* determines the answer to *Does John walk?*
    because the full extension determines each individual's value.

    Proof: if the lists `domain.map (pred · w)` and
    `domain.map (pred · v)` are equal (same wh-answer), then
    `pred e w = pred e v` for any `e ∈ domain` (same polar answer). -/
theorem wh_refines_polar {W E : Type*} [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (e : E) (he : e ∈ domain) :
    let whQ := GSQuestion.ofProject (λ w => domain.map (λ x => pred x w))
    let polarQ := polarQuestion (pred e)
    whQ ⊑ polarQ := by
  intro whQ polarQ w v h
  have h' : domain.map (λ x => pred x w) = domain.map (λ x => pred x v) := by
    show (QUD.ofProject (λ w' => domain.map (λ x => pred x w'))).r w v
    exact QUD.r_of_sameAnswer h
  show (QUD.ofProject (pred e)).sameAnswer w v = true
  rw [QUD.ofProject_sameAnswer_iff]
  simpa using List.map_eq_map_iff.mp h' e he

/-- If `ANS("Who walks?", i)` is known, `ANS("Does John walk?", i)` is
    determined. Direct corollary of `wh_refines_polar`. -/
theorem wh_ans_determines_polar_ans {W E : Type*} [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (e : E) (he : e ∈ domain)
    (w v : W) :
    let whQ := GSQuestion.ofProject (λ w' => domain.map (λ x => pred x w'))
    QUD.ans whQ w v = true →
    let polarQ := polarQuestion (pred e)
    QUD.ans polarQ w v = true := by
  intro whQ h polarQ
  exact wh_refines_polar domain pred e he w v h

/-- Composed polar questions refine their components. -/
theorem composed_polar_refines {W : Type*} (p1 p2 : W → Bool) :
    QUD.compose (polarQuestion p1) (polarQuestion p2) ⊑ polarQuestion p1 :=
  QUD.compose_refines_left _ _

/-! ### Answerhood thesis (p. 15) -/

/-- @cite{groenendijk-stokhof-1984} p. 15: the complete true answer at
    any index is determined by Q (functionally projected). -/
theorem answerhood_thesis {W : Type*} (q : GSQuestion W) (i : W) :
    ∃ (p : W → Bool), p = QUD.ans q i :=
  ⟨QUD.ans q i, rfl⟩

/-- The same question can have different answers at different
    indices. -/
theorem ans_situation_dependent {W : Type*} (q : GSQuestion W) (w v : W)
    (hDiff : ¬ q.r w v) :
    ∃ u, QUD.ans q w u ≠ QUD.ans q v u := by
  use w
  simp only [QUD.ans, ne_eq]
  rw [q.refl w]
  have : q.sameAnswer v w = false := decide_eq_false (mt q.iseqv.symm hDiff)
  simp [this]

/-! ### Exhaustivity -/

/-- Exhaustive answers: `ANS` pins down the full extension of the
    predicate. -/
theorem exhaustive_answers {W E : Type*} [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (w v : W) :
    let q := GSQuestion.ofProject (λ w' => domain.map (λ x => pred x w'))
    QUD.ans q w v = true ↔
    (∀ e ∈ domain, pred e w = pred e v) := by
  simp only [QUD.ans, GSQuestion.ofProject, QUD.ofProject_sameAnswer_iff]
  constructor
  · intro h e he
    have := List.map_eq_map_iff.mp h e he
    simp at this
    exact this
  · intro h
    exact List.map_eq_map_iff.mpr λ e he => by simp [h e he]

/-! ### De dicto / non-rigid descriptions (p. 27) -/

/-- De dicto answer via a (possibly non-rigid) description. -/
def deDictoAnswer {W E : Type*} [DecidableEq E]
    (description : W → E) (pred : E → W → Bool) : W → Bool :=
  λ w => pred (description w) w

/-- @cite{groenendijk-stokhof-1984} p. 27: non-rigid descriptions may
    fail to be semantic answers. For any non-rigid description there
    exists a predicate and question such that the de dicto answer
    holds at one world but fails at another world in the same cell —
    witnessing that de dicto answers are not semantic
    (partition-based).

    Proof: given `description w₀ ≠ description v₀`, let
    `pred e _ := decide (e = description w₀)` and `q := QUD.trivial`.
    Then de dicto at `w₀ = true` (reflexivity) and at `v₀ = false`
    (non-rigidity).

    The original statement universally quantified `pred`, which is
    false — a constant predicate makes de dicto answers trivially
    uniform. The correct G&S claim is that non-rigid descriptions are
    *not guaranteed* to give semantic answers, i.e., there exists a
    breaking scenario for any non-rigid description. -/
theorem nonrigid_may_fail_semantic {W E : Type*} [DecidableEq E]
    (description : W → E)
    (hNonrigid : ∃ w v, description w ≠ description v) :
    ∃ (pred : E → W → Bool) (q : GSQuestion W) (w v : W),
      q.r w v ∧
      deDictoAnswer description pred w = true ∧
      deDictoAnswer description pred v = false := by
  obtain ⟨w₀, v₀, hNeq⟩ := hNonrigid
  refine ⟨λ e _ => decide (e = description w₀), QUD.trivial, w₀, v₀, ⟨⟩, ?_, ?_⟩
  · show decide (description w₀ = description w₀) = true
    exact decide_eq_true rfl
  · show decide (description v₀ = description w₀) = false
    exact decide_eq_false (Ne.symm hNeq)

/-! ### Refinement ↔ answer transfer -/

/-- G&S refinement transfers answers: `q1 ⊑ q2` implies that any
    `ans q1`-true world `v` is also `ans q2`-true. -/
theorem refinement_transfers_answers {W : Type*} (q1 q2 : GSQuestion W)
    (hRefines : q1 ⊑ q2) (w : W) :
    ∀ v, QUD.ans q1 w v = true → QUD.ans q2 w v = true :=
  λ v h => hRefines w v h

/-- Converse: ANS-transfer implies refinement. -/
theorem answer_transfer_implies_refinement {W : Type*} (q1 q2 : GSQuestion W)
    (hTransfer : ∀ w v, QUD.ans q1 w v = true → QUD.ans q2 w v = true) :
    q1 ⊑ q2 :=
  hTransfer

/-- G&S refinement ↔ answer transfer. -/
theorem refinement_iff_answer_transfer {W : Type*} (q1 q2 : GSQuestion W) :
    q1 ⊑ q2 ↔ (∀ w v, QUD.ans q1 w v = true → QUD.ans q2 w v = true) :=
  ⟨λ h => refinement_transfers_answers q1 q2 h,
   λ h => answer_transfer_implies_refinement q1 q2 h⟩

end Phenomena.Questions.Studies.GroenendijkStokhof1984
