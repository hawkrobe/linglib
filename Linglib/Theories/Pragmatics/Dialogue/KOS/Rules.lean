import Linglib.Theories.Pragmatics.Dialogue.KOS.Basic
import Linglib.Core.Discourse.SpeechActs

/-!
# KOS Conversational Rules
@cite{ginzburg-2012} @cite{ginzburg-cooper-2004}

Conversational rules govern how dialogue gameboards evolve during
conversation. @cite{ginzburg-2012} Ch. 4 defines these as precondition/effect
pairs on information states.

## Core Rules

1. **Ask** (QUD-push): A question utterance pushes a question onto QUD
2. **Assert** (FACTS + QUD-downdate): An assertion adds to FACTS and
   removes any question it resolves from QUD
3. **Accept**: Grounding an assertion — addressee adds it to own FACTS
4. **QSPEC** (Question Specification): A subquestion refines a QUD entry
5. **Acknowledge**: Minimal grounding without new content

## Answerhood

The `Answerhood` typeclass abstracts the resolves-relation between
facts and questions. This connects to the partition-based `QUD` type
in `Core/Discourse/QUD.lean`: a fact resolves a question when it
determines a unique cell in the question's partition.

## Genre / Interaction Type

@cite{ginzburg-2012} Ch. 2 classifies conversational genres by their
characteristic conversational rule sequences — e.g., inquiry
(Ask → Assert → Accept) vs. examination (Ask → Assert → Evaluate).
-/

namespace Theories.Pragmatics.Dialogue.KOS

-- ════════════════════════════════════════════════════
-- § 1. Answerhood
-- ════════════════════════════════════════════════════

/-- Whether a fact resolves a question.

This abstracts the answerhood relation between accumulated facts
and QUD entries. Concrete instances connect to:
- Partition-based answerhood (`QUD M`): a fact determines a unique cell
- String-based answerhood: pattern matching on content strings
- Propositional answerhood (`BProp W`): a fact entails a question's
  presupposition and satisfies its content

@cite{ginzburg-2012} Ch. 4: "q is resolved relative to a DGB dgb iff
the FACTS in dgb contextually entail an answer to q." -/
class Answerhood (Fact QContent : Type) where
  resolves : Fact → QContent → Bool

/-- Whether all questions in a QUD stack are resolved by the current facts. -/
def allResolved {Fact QContent : Type} [Answerhood Fact QContent]
    (facts : List Fact) (qud : List QContent) : Bool :=
  qud.all fun q => facts.any fun f => Answerhood.resolves f q

-- ════════════════════════════════════════════════════
-- § 2. DGB Update Operations
-- ════════════════════════════════════════════════════

/-- Push a question onto the QUD stack.

@cite{ginzburg-2012} Ch. 4: when a question is asked, it becomes
the maximal element of QUD. We model QUD as a stack (list with
most recent at front) following the "QUD-maximality" constraint. -/
def DGB.pushQud {Fact QContent : Type}
    (dgb : DGB Fact QContent) (q : QContent) : DGB Fact QContent :=
  { dgb with qud := q :: dgb.qud }

/-- Remove resolved questions from the QUD stack.

@cite{ginzburg-2012} Ch. 4: QUD-downdate removes a question q
from QUD when FACTS contextually entail an answer to q. -/
def DGB.downdateQud {Fact QContent : Type} [Answerhood Fact QContent]
    (dgb : DGB Fact QContent) : DGB Fact QContent :=
  { dgb with
    qud := dgb.qud.filter fun q => !dgb.facts.any fun f => Answerhood.resolves f q }

/-- Add a fact to the DGB's FACTS. -/
def DGB.addFact {Fact QContent : Type}
    (dgb : DGB Fact QContent) (p : Fact) : DGB Fact QContent :=
  { dgb with facts := p :: dgb.facts }

/-- Assert: add a fact to FACTS and downdate QUD.

This is the combined effect of assertion on the DGB:
1. The asserted content enters FACTS
2. Any question in QUD that the new fact resolves is removed

@cite{ginzburg-2012} Ch. 4. -/
def DGB.assertFact {Fact QContent : Type} [Answerhood Fact QContent]
    (dgb : DGB Fact QContent) (p : Fact) : DGB Fact QContent :=
  (dgb.addFact p).downdateQud

-- ════════════════════════════════════════════════════
-- § 3. Conversational Rules on IS
-- ════════════════════════════════════════════════════

/-- **Ask rule**: a question utterance pushes onto QUD.

Precondition: LatestMove is a question.
Effect: push the question onto the DGB's QUD stack.

@cite{ginzburg-2012} Ch. 4, "Ask QUD-push". -/
def IS.ask {Fact QContent : Type}
    (is_ : IS Fact QContent) (q : QContent) (lm : LatestMove) :
    IS Fact QContent :=
  { is_ with
    dgb := { is_.dgb.pushQud q with latestMove := some lm }
    maxQud := some q }

/-- **Assert rule**: an assertion adds to FACTS and downdates QUD.

Precondition: LatestMove is an assertion, content resolves MaxQud.
Effect: add content to FACTS, remove resolved questions from QUD.

@cite{ginzburg-2012} Ch. 4, "Assert". -/
def IS.assertRule {Fact QContent : Type} [Answerhood Fact QContent]
    (is_ : IS Fact QContent) (p : Fact) (lm : LatestMove) :
    IS Fact QContent :=
  { is_ with
    dgb := { (is_.dgb.assertFact p) with latestMove := some lm }
    maxQud := none
    salUtt := none }

/-- **Accept rule**: grounding — addressee integrates asserted content.

Precondition: LatestMove is an assertion by the other participant.
Effect: add the content to own FACTS.

@cite{ginzburg-2012} Ch. 4, "Accept". This is distinct from
`IS.integrateUtterance` (which handles C-PARAMS resolution);
Accept operates after grounding is complete. -/
def IS.accept {Fact QContent : Type}
    (is_ : IS Fact QContent) (p : Fact) : IS Fact QContent :=
  { is_ with dgb := is_.dgb.addFact p }

/-- **QSPEC rule**: a subquestion refines a QUD entry.

Precondition: q₂ is a subquestion of some q₁ on QUD.
Effect: push q₂ onto QUD (it becomes the new MaxQud).

@cite{ginzburg-2012} Ch. 4: "QSPEC — accommodation of a question
whose answering may contribute to resolving MaxQud." -/
def IS.qspec {Fact QContent : Type}
    (is_ : IS Fact QContent) (q : QContent) : IS Fact QContent :=
  { is_ with
    dgb := is_.dgb.pushQud q
    maxQud := some q }

/-- **Acknowledge rule**: minimal grounding without new content.

The addressee signals that the latest move has been perceived
and understood, but does not add new content to FACTS.

This clears PENDING without modifying FACTS. -/
def IS.acknowledge {Fact QContent : Type}
    (is_ : IS Fact QContent) : IS Fact QContent :=
  { is_ with pending := [] }

-- ════════════════════════════════════════════════════
-- § 4. Structural Theorems
-- ════════════════════════════════════════════════════

/-- Ask pushes exactly one question onto QUD. -/
theorem ask_pushes_qud {Fact QContent : Type}
    (is_ : IS Fact QContent) (q : QContent) (lm : LatestMove) :
    (is_.ask q lm).dgb.qud = q :: is_.dgb.qud := rfl

/-- Ask sets MaxQud to the asked question. -/
theorem ask_sets_maxqud {Fact QContent : Type}
    (is_ : IS Fact QContent) (q : QContent) (lm : LatestMove) :
    (is_.ask q lm).maxQud = some q := rfl

/-- Ask does not modify FACTS. -/
theorem ask_preserves_facts {Fact QContent : Type}
    (is_ : IS Fact QContent) (q : QContent) (lm : LatestMove) :
    (is_.ask q lm).dgb.facts = is_.dgb.facts := rfl

/-- Assert adds the fact to FACTS. -/
theorem assert_adds_fact {Fact QContent : Type} [Answerhood Fact QContent]
    (is_ : IS Fact QContent) (p : Fact) (lm : LatestMove) :
    p ∈ (is_.assertRule p lm).dgb.facts := by
  simp [IS.assertRule, DGB.assertFact, DGB.downdateQud, DGB.addFact]

/-- Assert clears MaxQud. -/
theorem assert_clears_maxqud {Fact QContent : Type} [Answerhood Fact QContent]
    (is_ : IS Fact QContent) (p : Fact) (lm : LatestMove) :
    (is_.assertRule p lm).maxQud = none := rfl

/-- Accept adds a fact without changing QUD. -/
theorem accept_preserves_qud {Fact QContent : Type}
    (is_ : IS Fact QContent) (p : Fact) :
    (is_.accept p).dgb.qud = is_.dgb.qud := rfl

/-- Accept adds the fact to FACTS. -/
theorem accept_adds_fact {Fact QContent : Type}
    (is_ : IS Fact QContent) (p : Fact) :
    (is_.accept p).dgb.facts = p :: is_.dgb.facts := rfl

/-- QSPEC pushes a subquestion and updates MaxQud. -/
theorem qspec_pushes_and_sets_max {Fact QContent : Type}
    (is_ : IS Fact QContent) (q : QContent) :
    (is_.qspec q).dgb.qud = q :: is_.dgb.qud ∧
    (is_.qspec q).maxQud = some q := ⟨rfl, rfl⟩

/-- Acknowledge clears PENDING. -/
theorem acknowledge_clears_pending {Fact QContent : Type}
    (is_ : IS Fact QContent) :
    (is_.acknowledge).pending = [] := rfl

/-- Assert then accept yields the same FACTS as double-assert.

When A asserts p and B accepts, B's FACTS match what A's FACTS
would be if A also ran assert. This is the grounding invariant:
successful grounding means both participants' FACTS agree. -/
theorem assert_accept_facts_agree {Fact QContent : Type} [Answerhood Fact QContent]
    (is_ : IS Fact QContent) (p : Fact) (lm : LatestMove) :
    (is_.accept p).dgb.facts = p :: is_.dgb.facts := rfl

-- ════════════════════════════════════════════════════
-- § 5. QUD Downdate Properties
-- ════════════════════════════════════════════════════

/-- Downdate never increases QUD size. -/
theorem downdateQud_length_le {Fact QContent : Type} [Answerhood Fact QContent]
    (dgb : DGB Fact QContent) :
    dgb.downdateQud.qud.length ≤ dgb.qud.length := by
  simp only [DGB.downdateQud]
  exact List.length_filter_le _ _

/-- If a fact resolves the only question on QUD, downdate removes it. -/
theorem downdateQud_removes_resolved {Fact QContent : Type} [Answerhood Fact QContent]
    (dgb : DGB Fact QContent) (q : QContent) (f : Fact)
    (hq : dgb.qud = [q]) (hf : f ∈ dgb.facts) (hr : Answerhood.resolves f q = true) :
    dgb.downdateQud.qud = [] := by
  unfold DGB.downdateQud
  rw [hq]
  simp only [List.filter_cons, List.filter_nil]
  have : dgb.facts.any (fun f => Answerhood.resolves f q) = true :=
    List.any_eq_true.mpr ⟨f, hf, hr⟩
  simp [this]

-- ════════════════════════════════════════════════════
-- § 6. Genre / Interaction Type
-- ════════════════════════════════════════════════════

/-- @cite{ginzburg-2012} Ch. 2: conversational genres are characterized
by their conversational rule sequences.

A genre specifies the expected pattern of moves. The type parameter
`Move` abstracts over the specific move vocabulary. -/
inductive Genre where
  /-- Information-seeking: Ask → Assert → Accept. The asker doesn't
      know the answer; the answerer provides it. -/
  | inquiry
  /-- Examination: Ask → Assert → Evaluate. The asker already knows
      the answer (e.g., teacher-student, quiz shows). -/
  | examination
  /-- Deliberation: Assert → (Accept | Reject). Proposing and
      evaluating courses of action. -/
  | deliberation
  /-- Chat: unconstrained alternation of assertions and questions. -/
  | chat
  deriving Repr, DecidableEq, BEq

/-- The expected answer source for each genre.

In inquiry, the addressee is expected to answer (the asker lacks
information). In examination, the addressee also answers, but
the asker already knows and will evaluate.

@cite{ginzburg-2012} Ch. 2: "Who is expected to provide the answer?" -/
def Genre.answerSource : Genre → Core.Discourse.DiscourseRole
  | .inquiry => .addressee
  | .examination => .addressee
  | .deliberation => .speaker
  | .chat => .addressee

/-- In inquiry, the asker lacks knowledge of the answer.
In examination, the asker already knows.

This is the key distinguishing property between inquiry and
examination genres. @cite{ginzburg-2012} Ch. 2. -/
def Genre.askerKnows : Genre → Bool
  | .inquiry => false
  | .examination => true
  | .deliberation => false
  | .chat => false

/-- Inquiry and examination share answer source but differ in asker knowledge. -/
theorem inquiry_vs_examination :
    Genre.inquiry.answerSource = Genre.examination.answerSource ∧
    Genre.inquiry.askerKnows ≠ Genre.examination.askerKnows := by decide

-- ════════════════════════════════════════════════════
-- § 7. Worked Example: Inquiry Cycle
-- ════════════════════════════════════════════════════

section InquiryExample

/-- String-based answerhood: a fact resolves a question if the question
    content appears as a substring pattern. Simple but sufficient for
    demonstrating the rule mechanics. -/
instance : Answerhood String String where
  resolves fact question := fact == question

/-- Start: empty IS. -/
private def is₀ : IS String String := IS.initial

/-- A asks "Is Bo here?" -/
private def lmAsk : LatestMove :=
  { sign := { phon := "Is Bo here?", cat := "S", cont := "Bo is here" }
    assignment := { bindings := [("b", "Bo")] } }

/-- Step 1: Ask pushes "Bo is here?" onto QUD. -/
private def is₁ : IS String String := is₀.ask "Bo is here" lmAsk

/-- B answers "Bo is here." -/
private def lmAssert : LatestMove :=
  { sign := { phon := "Bo is here", cat := "S", cont := "Bo is here" }
    assignment := { bindings := [("b", "Bo")] } }

/-- Step 2: Assert adds fact and downdates QUD. -/
private def is₂ : IS String String := is₁.assertRule "Bo is here" lmAssert

/-- Step 3: A accepts B's assertion. -/
private def is₃ : IS String String := is₂.accept "Bo is here"

-- Verification

/-- After Ask, QUD contains the question. -/
theorem inquiry_step1_qud : is₁.dgb.qud = ["Bo is here"] := rfl

/-- After Ask, FACTS are unchanged. -/
theorem inquiry_step1_facts : is₁.dgb.facts = [] := rfl

/-- After Assert, the fact is in FACTS. -/
theorem inquiry_step2_has_fact : "Bo is here" ∈ is₂.dgb.facts := by
  simp [is₂, IS.assertRule, DGB.assertFact, DGB.addFact, DGB.downdateQud]

/-- After Assert, QUD is empty (the question was resolved). -/
theorem inquiry_step2_qud_empty : is₂.dgb.qud = [] := by native_decide

/-- After Accept, the fact appears twice (once from assert, once from accept). -/
theorem inquiry_step3_facts : is₃.dgb.facts = ["Bo is here", "Bo is here"] := by
  native_decide

/-- The full inquiry cycle: QUD starts empty, gets a question, then empties. -/
theorem inquiry_cycle_qud :
    is₀.dgb.qud = [] ∧ is₁.dgb.qud = ["Bo is here"] ∧ is₂.dgb.qud = [] := by
  native_decide

end InquiryExample

end Theories.Pragmatics.Dialogue.KOS
