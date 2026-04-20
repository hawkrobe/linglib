import Linglib.Core.Issue.Basic

/-!
# QUD Stack: Ordered Accepted-Unanswered Questions
@cite{roberts-2012}

A `QUDStack W` models the discourse-state component of @cite{roberts-2012} §2:
the ordered list of questions that have been accepted as worth answering
but have not yet been resolved. Subquestions are pushed on top; answers
pop the immediate QUD. Strategies of inquiry (`Core/Discourse/Strategy.lean`)
are the rose-tree counterpart.

Parameterized by `Core.Issue W` — the Set-based inquisitive-content lattice.
-/

namespace Discourse

open Core

/-- A QUD stack: ordered list of accepted, unanswered questions.
    The head is the immediate QUD (most recently accepted question).

    @cite{roberts-2012} Def. 10g: "QUD_m = the set of all questions which have
    been accepted as questions (i.e., accepted as being worth answering)
    at m, but which have not yet been answered." The stack ordering
    reflects discourse subordination — subquestions pushed on top. -/
structure QUDStack (W : Type*) where
  questions : List (Issue W)

namespace QUDStack

variable {W : Type*}

/-- Empty QUD stack (discourse initial state). -/
def empty : QUDStack W := ⟨[]⟩

/-- The immediate QUD: the most recently accepted, unanswered question. -/
def immediateQUD (s : QUDStack W) : Option (Issue W) := s.questions.head?

/-- Accept a new question: push onto the stack.
    @cite{roberts-2012}: "a subquestion of QUD is pushed onto QUD." -/
def push (s : QUDStack W) (q : Issue W) : QUDStack W := ⟨q :: s.questions⟩

/-- Answer the immediate QUD: pop from the stack.
    @cite{roberts-2012}: "an answer to QUD pops QUD off the stack." -/
def pop (s : QUDStack W) : QUDStack W := ⟨s.questions.tail⟩

/-- Current depth of the QUD stack. -/
def depth (s : QUDStack W) : Nat := s.questions.length

end QUDStack

end Discourse
