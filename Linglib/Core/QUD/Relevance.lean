import Linglib.Core.QUD.Basic
import Linglib.Core.Inquisitive

/-!
# QUD Relevance: Roberts 2012 Subquestions and Move Relevance
@cite{roberts-2012} @cite{groenendijk-stokhof-1984}

Roberts' QUD theory introduces hierarchical question structure: a QUD
decomposes into subquestions, and discourse moves are relevant iff they
address the QUD or its subquestions.

The connection to `QUD.refines` (`Core/Partition.lean`):
- `QUD.refines q q'`   ≡  q's partition refines q' (knows q → knows q')
- `questionEntails Q q` ≡  every alternative of Q entails some alt of q

These are the same relation at different levels of abstraction. The formal
bridge theorem is `refinesOn_iff_questionEntails_of_partition` in
`Core/Partition.lean`.

This file lives under `Core/QUD/` because the relevance machinery is the
QUD-theoretic content layered on top of pure inquisitive primitives.
-/

namespace Discourse

/-- Decidable refinement restricted to a finite element list.

    `refinesOn q q' elements` holds iff for all `w, v ∈ elements`,
    `q.sameAnswer w v = true → q'.sameAnswer w v = true`.

    This is the `Bool`-valued analogue of `QUD.refines` (Core/Partition.lean),
    quantifying only over elements in the list rather than all of type `M`.
    For genuine partitions (see `Issue.isPartition`), this coincides with
    `questionEntails` — the formal bridge connecting the two question
    representations in the library. -/
def refinesOn {M : Type*} (q q' : QUD M) (elements : List M) : Bool :=
  elements.all fun w =>
    elements.all fun v =>
      !q.sameAnswer w v || q'.sameAnswer w v

/-- A proposition p partially answers an issue q if p settles at least one
of q's alternatives — either confirming it or ruling it out.

@cite{roberts-2012} Def. 3a: a partial answer contextually entails the
evaluation — either true or false — of at least one element of q-alt(q).

The positive-only version (`propEntails p alt`) misses negative partial
answerhood, where p rules out an alternative entirely (`propEntails p ¬alt`). -/
def partiallyAnswers {W : Type*} (p : W → Bool) (q : Issue W) (worlds : List W) : Bool :=
  q.alternatives.any fun alt =>
    propEntails p alt worlds || propEntails p (fun w => !alt w) worlds

/-- Question q₁ entails question q₂ iff every alternative of q₁ entails
some alternative of q₂.

@cite{roberts-2012} Def. 8 (following @cite{groenendijk-stokhof-1984}:16):
"One interrogative q₁ entails another q₂ iff every proposition that
answers q₁ answers q₂ as well."

At the partition level, this corresponds to `QUD.refines` (Core/Partition.lean):
if Q refines q, then knowing Q's answer determines q's answer. -/
def questionEntails {W : Type*} (q₁ q₂ : Issue W) (worlds : List W) : Bool :=
  q₁.alternatives.all fun alt₁ =>
    q₂.alternatives.any fun alt₂ => propEntails alt₁ alt₂ worlds

/-- q is a subquestion of Q iff Q entails q: answering Q yields a
complete answer to q.

@cite{roberts-2012} Def. 8–9. At the partition level, this is `QUD.refines`:
the parent question's partition is a refinement of the subquestion's. -/
def isSubquestion {W : Type*} (q parent : Issue W) (worlds : List W) : Bool :=
  questionEntails parent q worlds

/-- A discourse move (assertion or question) is relevant to the QUD if
it partially answers the QUD or a subquestion.

@cite{roberts-2012} Def. 15 / @cite{ippolito-kiss-williams-2025} assumption iii, p. 225:
"S is relevant to QUD if S is either a subquestion of QUD or an answer
to a subquestion q of QUD."

For assertions (single-alternative issues): checks whether the propositional
content partially answers the QUD or a subquestion.
For questions (multi-alternative issues): checks whether any alternative
partially answers the QUD or a subquestion — resolving the question would
inform a subquestion. -/
def moveRelevant {W : Type*} (den : Issue W) (qud : Issue W)
    (subquestions : List (Issue W)) (worlds : List W) : Bool :=
  den.alternatives.any fun alt =>
    partiallyAnswers alt qud worlds ||
    subquestions.any fun sq =>
      partiallyAnswers alt sq worlds

/-- `propEntails` is reflexive. -/
theorem propEntails_refl {W : Type*} (p : W → Bool) (worlds : List W) :
    propEntails p p worlds = true := by
  unfold propEntails
  simp [List.all_eq_true]

/-- `questionEntails` is reflexive: every question entails itself. -/
theorem questionEntails_refl {W : Type*} (q : Issue W) (worlds : List W) :
    questionEntails q q worlds = true := by
  unfold questionEntails
  simp only [List.all_eq_true, List.any_eq_true]
  intro alt hMem
  exact ⟨alt, hMem, propEntails_refl alt worlds⟩

/-- Subquestion is reflexive: every question is a subquestion of itself. -/
theorem isSubquestion_refl {W : Type*} (q : Issue W) (worlds : List W) :
    isSubquestion q q worlds = true :=
  questionEntails_refl q worlds

/-- Partial answerhood of an alternative implies move relevance.

If some alternative of a move partially answers the QUD directly,
the move is relevant (even without subquestions). -/
theorem partiallyAnswers_implies_relevant {W : Type*}
    (den : Issue W) (qud : Issue W) (worlds : List W)
    (alt : W → Bool) (hAlt : alt ∈ den.alternatives)
    (hPA : partiallyAnswers alt qud worlds = true) :
    moveRelevant den qud [] worlds = true := by
  unfold moveRelevant
  rw [List.any_eq_true]
  exact ⟨alt, hAlt, by simp [hPA]⟩

end Discourse
