import Linglib.Semantics.Questions.Basic

/-!
# QUD Stack: Ordered Accepted-Unanswered Questions
[roberts-2012]

Stack of accepted-but-unanswered questions. Head is the immediate QUD;
subquestions push, answers pop. `Strategy` is the rose-tree counterpart.
-/

namespace Discourse

/-- A QUD stack: ordered list of accepted, unanswered questions
    (Roberts 2012 Def 10g). -/
structure QUDStack (W : Type*) where
  questions : List (Question W)

namespace QUDStack

variable {W : Type*}

/-- Empty QUD stack (discourse initial state). -/
def empty : QUDStack W := ⟨[]⟩

/-- The immediate QUD: the most recently accepted, unanswered question. -/
def immediateQUD (s : QUDStack W) : Option (Question W) := s.questions.head?

/-- Accept a new question: push onto the stack. -/
def push (s : QUDStack W) (q : Question W) : QUDStack W := ⟨q :: s.questions⟩

/-- Answer the immediate QUD: pop from the stack. -/
def pop (s : QUDStack W) : QUDStack W := ⟨s.questions.tail⟩

/-- Current depth of the QUD stack. -/
def depth (s : QUDStack W) : Nat := s.questions.length

end QUDStack

end Discourse
