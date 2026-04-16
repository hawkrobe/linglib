import Linglib.Theories.Semantics.Questions.Denotation.Partition

/-!
# The ANS Operator
@cite{groenendijk-stokhof-1984}

Core answer operator from @cite{groenendijk-stokhof-1984}, Ch. I:
`ANS(Q, i)` = the cell of Q's partition containing i.

This module contains the operator itself, its basic properties, and
lightweight answerhood predicates. Heavier machinery (Karttunen comparison,
Belnap distributivity, `gsToHamblin`, foldl-based completeness proofs)
lives in `Answerhood.lean`.
-/

namespace Semantics.Questions.Answerhood

open Semantics.Questions
open scoped GSQuestion  -- For ⊑ notation

/-- ANS(Q, i) = cell of Q's partition containing i (@cite{groenendijk-stokhof-1984}, p. 14-15). -/
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

/-- Wh-question refines the polar question for any individual in the domain.
    Core result of @cite{groenendijk-stokhof-1984}: knowing the answer to "Who walks?" determines
    the answer to "Does John walk?" because the full extension determines
    each individual's value.
    Proof: If the lists `domain.map (pred · w)` and `domain.map (pred · v)` are
    equal (same wh-answer), then `pred e w = pred e v` for any `e ∈ domain`
    (same polar answer). -/
theorem wh_refines_polar {W E : Type*} [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (e : E) (he : e ∈ domain) :
    let whQ := GSQuestion.ofProject (λ w => domain.map (λ x => pred x w))
    let polarQ := polarQuestion (pred e)
    whQ ⊑ polarQ := by
  -- Intro let-bindings, then unfold refinement
  intro _ _ w v h
  -- Bypass let-bindings: restate h and goal in terms of BEq
  change (pred e w == pred e v) = true
  have h' : (domain.map (λ x => pred x w) == domain.map (λ x => pred x v)) = true := h
  rw [beq_iff_eq] at h' ⊢
  -- h' : domain.map (λ x => pred x w) = domain.map (λ x => pred x v)
  -- goal : pred e w = pred e v
  simpa using List.map_eq_map_iff.mp h' e he

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

/-- Answerhood thesis: complete true answer at any index is determined by Q (@cite{groenendijk-stokhof-1984}, p. 15). -/
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

/-- @cite{belnap-1982}'s Unique Answer Fallacy: it is a fallacy to assume that each
    question has a unique complete true answer. In the G&S framework, `ans q w`
    varies with the index `w` — the same question Q yields different complete true
    answers at different worlds. -/
theorem unique_answer_fallacy {W : Type*} (q : GSQuestion W) (w v : W)
    (hDiff : q.sameAnswer w v = false) :
    ∃ u, ans q w u ≠ ans q v u :=
  ans_situation_dependent q w v hDiff

/-- Partial answer: eliminates some cells but not all. -/
def isPartialAnswer {W : Type*} (p : W → Bool) (q : GSQuestion W)
    (worlds : List W) : Bool :=
  let cells := q.toCells worlds
  let compatible := cells.filter λ cell =>
    worlds.any λ w => p w && cell w
  compatible.length > 1 && compatible.length < cells.length

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

/-- @cite{belnap-1982}'s Distributivity Principle: knowing the answer to a wh-question
    is equivalent to knowing, for each individual, whether the predicate holds.

    An agent whose epistemic state (the set of worlds they consider possible) is
    `epState` *knows the answer to Q at w* iff their state is a subset of
    `ans(Q, w)` — i.e., every world they consider possible agrees with w on the
    full extension of the predicate.

    The Distributivity Principle says this is equivalent to knowing each atomic
    fact: for every entity e in the domain, the agent knows whether `pred e` holds.
    This bridges question-embedding ("knows who walks") and propositional attitudes
    ("knows that John walks ∧ knows that Mary walks ∧ ..."). -/
theorem distributivity_principle {W E : Type*} [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (w : W)
    (epState : W → Bool) :
    let q := GSQuestion.ofProject (λ w' => domain.map (λ x => pred x w'))
    (∀ v, epState v = true → ans q w v = true) ↔
    (∀ e ∈ domain, ∀ v, epState v = true → pred e v = pred e w) := by
  simp only [exhaustive_answers]
  constructor
  · intro h e he v hv; exact (h v hv e he).symm
  · intro h v hv e he; exact (h e he v hv).symm

/-- @cite{belnap-1982}'s Distributivity Test (§2.4, p. 177): a negative criterion
    for ruling out candidate answers. For any proposition P and indirect question
    IQ, if the following is consistent:

        Sally knows that P, but Sally doesn't know IQ.

    then P is NOT an answer to IQ. The test "distributes" the *know* inside the
    question and onto its answers: if knowing P doesn't suffice to know IQ, then
    P doesn't answer IQ.

    Formalization: P fails the test for Q at w if there exists an epistemic state
    (set of worlds the agent considers possible) that is a subset of P (the agent
    knows P) but NOT a subset of ans(Q, w) (the agent doesn't know Q). -/
def failsDistributivityTest {W : Type*} (p : W → Bool) (q : GSQuestion W)
    (w : W) (worlds : List W) : Bool :=
  -- ∃ epistemic state ⊆ worlds where agent knows P but doesn't know Q
  -- Approximation: find a world v where p holds but ans(q,w) doesn't
  worlds.any λ v => p v && !ans q w v

/-- If P passes the Distributivity Test (no witnessing world exists), then knowing
    P implies knowing Q — i.e., P is at least as informative as Q w.r.t. the
    partition. This is the contrapositive of the test. -/
theorem passes_test_implies_answer {W : Type*} (p : W → Bool) (q : GSQuestion W)
    (w : W) (worlds : List W)
    (hPasses : failsDistributivityTest p q w worlds = false) :
    ∀ v ∈ worlds, p v = true → ans q w v = true := by
  intro v hv hp
  by_contra h
  have : failsDistributivityTest p q w worlds = true := by
    simp only [failsDistributivityTest]
    rw [List.any_eq_true]
    exact ⟨v, hv, by simp [hp, Bool.eq_false_iff.mpr h]⟩
  rw [this] at hPasses; exact absurd hPasses (by simp)

/-- Concrete demonstration of the Distributivity Test.

    @cite{belnap-1982}, §2.4, p. 177: "Peter knows that the person who kicked Sam
    is John, but Peter doesn't know who kicked Sam." This is inconsistent — so
    *the person who kicked Sam is John* IS an answer to *who kicked Sam*.

    Vs: "Peter knows that China is populous, but Peter doesn't know which person
    kicked Sam." This IS consistent — so *China is populous* is NOT an answer.

    We verify on `Fin 3` with identity partition (who kicked Sam → full extension):
    - "the answer is 0" passes the test (knowing the answer IS knowing the question)
    - "w.val < 2" (an irrelevant fact) fails the test -/
theorem distributivity_test_examples :
    let q : GSQuestion (Fin 3) := QUD.ofProject id
    let worlds : List (Fin 3) := [0, 1, 2]
    -- "The answer is 0" passes (knowing it entails knowing who kicked Sam)
    failsDistributivityTest (λ w => decide (w = (0 : Fin 3))) q 0 worlds = false ∧
    -- "w < 2" fails (knowing it does NOT entail knowing who kicked Sam)
    failsDistributivityTest (λ w => decide (w.val < 2)) q 0 worlds = true := by
  native_decide

/-- De dicto answer via a (possibly non-rigid) description. -/
def deDictoAnswer {W E : Type*} [DecidableEq E]
    (description : W → E) (pred : E → W → Bool) : W → Bool :=
  λ w => pred (description w) w

/-- Non-rigid descriptions may fail to be semantic answers (@cite{groenendijk-stokhof-1984}, p. 27).
    For any non-rigid description, there exists a predicate and question such that
    the de dicto answer holds at one world but fails at another world in the same
    cell — witnessing that de dicto answers are not semantic (partition-based).

    Proof: Given description(w₀) ≠ description(v₀), let pred(e,_) := (e = description(w₀))
    and q := trivial (all worlds equivalent). Then:
    - de dicto at w₀ = pred(description(w₀), w₀) = true (reflexivity)
    - de dicto at v₀ = pred(description(v₀), v₀) = false (non-rigidity)

    N.B. The original statement universally quantified `pred`, which is false —
    a constant predicate makes de dicto answers trivially uniform. The correct
    G&S claim is that non-rigid descriptions are *not guaranteed* to give
    semantic answers, i.e., there exists a breaking scenario for any non-rigid
    description. -/
theorem nonrigid_may_fail_semantic {W E : Type*} [DecidableEq E]
    (description : W → E)
    (hNonrigid : ∃ w v, description w ≠ description v) :
    ∃ (pred : E → W → Bool) (q : GSQuestion W) (w v : W),
      q.sameAnswer w v = true ∧
      deDictoAnswer description pred w = true ∧
      deDictoAnswer description pred v = false := by
  obtain ⟨w₀, v₀, hNeq⟩ := hNonrigid
  refine ⟨λ e _ => decide (e = description w₀), QUD.trivial, w₀, v₀, rfl, ?_, ?_⟩
  · show decide (description w₀ = description w₀) = true
    exact decide_eq_true rfl
  · show decide (description v₀ = description w₀) = false
    exact decide_eq_false (Ne.symm hNeq)

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

end Semantics.Questions.Answerhood
