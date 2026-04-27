import Linglib.Core.Question.Partition.Constructors
import Linglib.Phenomena.Questions.Studies.GroenendijkStokhof1984

/-!
# @cite{belnap-1982}: Approaches to the semantics of questions in natural language

Single-paper formalisation of the answerhood theorems from
@cite{belnap-1982} ("Approaches to the semantics of questions in
natural language", in *Issues in the Logic of Questions*), formulated
over the `GSQuestion W` substrate.

## Theorems

* **Unique Answer Fallacy** (§2.3): each question does **not** have a
  unique complete true answer — `ANS(Q, w)` varies with the index `w`.
  Direct restatement of @cite{groenendijk-stokhof-1984}'s
  `ans_situation_dependent` under Belnap's diagnostic name.
* **Distributivity Principle** (§2.4): knowing the answer to a
  wh-question is equivalent to knowing each atomic fact (for each
  individual, whether the predicate holds). Bridges question-embedding
  and propositional attitudes.
* **Distributivity Test** (§2.4, p. 177): a negative criterion for
  ruling out candidate answers — *Sally knows that P, but Sally
  doesn't know IQ* must be inconsistent for `P` to answer `IQ`.
-/

namespace Phenomena.Questions.Studies.Belnap1982

open Semantics.Questions
open Phenomena.Questions.Studies.GroenendijkStokhof1984

/-! ### Unique Answer Fallacy (§2.3) -/

/-- @cite{belnap-1982}'s **Unique Answer Fallacy**: it is a fallacy to
    assume that each question has a unique complete true answer. In
    the G&S framework, `ans q w` varies with the index `w` — the same
    question Q yields different complete true answers at different
    worlds. Direct restatement of `ans_situation_dependent`. -/
theorem unique_answer_fallacy {W : Type*} (q : GSQuestion W) (w v : W)
    (hDiff : ¬ q.r w v) :
    ∃ u, QUD.ans q w u ≠ QUD.ans q v u :=
  ans_situation_dependent q w v hDiff

/-! ### Distributivity Principle (§2.4) -/

/-- @cite{belnap-1982}'s **Distributivity Principle**: knowing the
    answer to a wh-question is equivalent to knowing, for each
    individual, whether the predicate holds.

    An agent whose epistemic state (the set of worlds they consider
    possible) is `epState` *knows the answer to Q at w* iff their
    state is a subset of `ans(Q, w)` — i.e., every world they consider
    possible agrees with w on the full extension of the predicate.

    The Distributivity Principle says this is equivalent to knowing
    each atomic fact: for every entity `e` in the domain, the agent
    knows whether `pred e` holds. This bridges question-embedding
    ("knows who walks") and propositional attitudes ("knows that John
    walks ∧ knows that Mary walks ∧ ..."). -/
theorem distributivity_principle {W E : Type*} [DecidableEq E]
    (domain : List E) (pred : E → W → Bool) (w : W)
    (epState : W → Bool) :
    let q := GSQuestion.ofProject (λ w' => domain.map (λ x => pred x w'))
    (∀ v, epState v = true → QUD.ans q w v = true) ↔
    (∀ e ∈ domain, ∀ v, epState v = true → pred e v = pred e w) := by
  simp only [exhaustive_answers]
  constructor
  · intro h e he v hv; exact (h v hv e he).symm
  · intro h v hv e he; exact (h e he v hv).symm

/-! ### Distributivity Test (§2.4, p. 177) -/

/-- Partial answer: eliminates some cells but not all. -/
def isPartialAnswer {W : Type*} [DecidableEq W] (p : W → Bool) (q : GSQuestion W)
    (worlds : List W) : Bool :=
  let cells := q.toCells worlds
  let compatible := cells.filter λ cell =>
    worlds.any λ w => p w && decide (w ∈ cell)
  compatible.length > 1 && compatible.length < cells.length

/-- @cite{belnap-1982}'s **Distributivity Test** (§2.4, p. 177): a
    negative criterion for ruling out candidate answers. For any
    proposition `P` and indirect question `IQ`, if the following is
    consistent:

        Sally knows that P, but Sally doesn't know IQ.

    then `P` is **not** an answer to `IQ`. The test "distributes" the
    *know* inside the question and onto its answers: if knowing `P`
    doesn't suffice to know `IQ`, then `P` doesn't answer `IQ`.

    Formalisation: `P` fails the test for `Q` at `w` if there exists
    an epistemic state (set of worlds the agent considers possible)
    that is a subset of `P` (the agent knows `P`) but **not** a subset
    of `ans(Q, w)` (the agent doesn't know `Q`). -/
def failsDistributivityTest {W : Type*} (p : W → Bool) (q : GSQuestion W)
    (w : W) (worlds : List W) : Bool :=
  worlds.any λ v => p v && !QUD.ans q w v

/-- If `P` passes the Distributivity Test (no witnessing world
    exists), then knowing `P` implies knowing `Q` — i.e., `P` is at
    least as informative as `Q` w.r.t. the partition. Contrapositive
    of the test. -/
theorem passes_test_implies_answer {W : Type*} (p : W → Bool) (q : GSQuestion W)
    (w : W) (worlds : List W)
    (hPasses : failsDistributivityTest p q w worlds = false) :
    ∀ v ∈ worlds, p v = true → QUD.ans q w v = true := by
  intro v hv hp
  by_contra h
  have : failsDistributivityTest p q w worlds = true := by
    simp only [failsDistributivityTest]
    rw [List.any_eq_true]
    exact ⟨v, hv, by simp [hp, Bool.eq_false_iff.mpr h]⟩
  rw [this] at hPasses; exact absurd hPasses (by simp)

/-- Concrete demonstration of the Distributivity Test.

    @cite{belnap-1982} §2.4, p. 177: "Peter knows that the person who
    kicked Sam is John, but Peter doesn't know who kicked Sam." This
    is inconsistent — so *the person who kicked Sam is John* IS an
    answer to *who kicked Sam*.

    Vs: "Peter knows that China is populous, but Peter doesn't know
    which person kicked Sam." This IS consistent — so *China is
    populous* is NOT an answer.

    We verify on `Fin 3` with identity partition (who kicked Sam → full
    extension):

    * "the answer is 0" passes the test (knowing it entails knowing
      who kicked Sam);
    * "w.val < 2" (an irrelevant fact) fails the test. -/
theorem distributivity_test_examples :
    let q : GSQuestion (Fin 3) := QUD.ofProject id
    let worlds : List (Fin 3) := [0, 1, 2]
    failsDistributivityTest (λ w => decide (w = (0 : Fin 3))) q 0 worlds = false ∧
    failsDistributivityTest (λ w => decide (w.val < 2)) q 0 worlds = true := by
  native_decide

end Phenomena.Questions.Studies.Belnap1982
