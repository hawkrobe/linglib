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

-- Bool/Prop characterizations of the four core predicates.

/-- `refinesOn q q' elements = true` iff `q` distinguishes at most as much
    as `q'` does on `elements`: any pair `q` calls equivalent, `q'` does too. -/
theorem refinesOn_iff {M : Type*} (q q' : QUD M) (elements : List M) :
    refinesOn q q' elements = true ↔
    ∀ w ∈ elements, ∀ v ∈ elements,
      q.sameAnswer w v = true → q'.sameAnswer w v = true := by
  unfold refinesOn
  rw [List.all_eq_true]
  refine forall_congr' fun w => forall_congr' fun _ => ?_
  rw [List.all_eq_true]
  refine forall_congr' fun v => forall_congr' fun _ => ?_
  cases q.sameAnswer w v <;> simp

theorem partiallyAnswers_iff {W : Type*} (p : W → Bool) (q : Issue W)
    (worlds : List W) :
    partiallyAnswers p q worlds = true ↔
    ∃ alt ∈ q.alternatives,
      propEntails p alt worlds = true ∨
      propEntails p (fun w => !alt w) worlds = true := by
  simp only [partiallyAnswers, List.any_eq_true, Bool.or_eq_true]

theorem questionEntails_iff {W : Type*} (q₁ q₂ : Issue W) (worlds : List W) :
    questionEntails q₁ q₂ worlds = true ↔
    ∀ alt₁ ∈ q₁.alternatives,
      ∃ alt₂ ∈ q₂.alternatives, propEntails alt₁ alt₂ worlds = true := by
  simp only [questionEntails, List.all_eq_true, List.any_eq_true]

theorem isSubquestion_iff {W : Type*} (q parent : Issue W) (worlds : List W) :
    isSubquestion q parent worlds = true ↔
    ∀ alt ∈ parent.alternatives,
      ∃ altq ∈ q.alternatives, propEntails alt altq worlds = true :=
  questionEntails_iff parent q worlds

theorem moveRelevant_iff {W : Type*} (den qud : Issue W)
    (subquestions : List (Issue W)) (worlds : List W) :
    moveRelevant den qud subquestions worlds = true ↔
    ∃ alt ∈ den.alternatives,
      partiallyAnswers alt qud worlds = true ∨
      ∃ sq ∈ subquestions, partiallyAnswers alt sq worlds = true := by
  simp only [moveRelevant, List.any_eq_true, Bool.or_eq_true]

-- Reflexivity / transitivity.

/-- `propEntails` is transitive. -/
theorem propEntails_trans {W : Type*} (p q r : W → Bool) (worlds : List W)
    (hpq : propEntails p q worlds = true)
    (hqr : propEntails q r worlds = true) :
    propEntails p r worlds = true := by
  rw [propEntails_iff] at hpq hqr ⊢
  intro w hw hp
  exact hqr w hw (hpq w hw hp)

/-- `questionEntails` is reflexive: every question entails itself. -/
theorem questionEntails_refl {W : Type*} (q : Issue W) (worlds : List W) :
    questionEntails q q worlds = true := by
  rw [questionEntails_iff]
  intro alt hMem
  exact ⟨alt, hMem, propEntails_refl alt worlds⟩

/-- `questionEntails` is transitive. -/
theorem questionEntails_trans {W : Type*} (q₁ q₂ q₃ : Issue W) (worlds : List W)
    (h12 : questionEntails q₁ q₂ worlds = true)
    (h23 : questionEntails q₂ q₃ worlds = true) :
    questionEntails q₁ q₃ worlds = true := by
  rw [questionEntails_iff] at h12 h23 ⊢
  intro alt₁ hAlt₁
  obtain ⟨alt₂, hAlt₂, hpq⟩ := h12 alt₁ hAlt₁
  obtain ⟨alt₃, hAlt₃, hqr⟩ := h23 alt₂ hAlt₂
  exact ⟨alt₃, hAlt₃, propEntails_trans _ _ _ _ hpq hqr⟩

/-- Subquestion is reflexive: every question is a subquestion of itself. -/
theorem isSubquestion_refl {W : Type*} (q : Issue W) (worlds : List W) :
    isSubquestion q q worlds = true :=
  questionEntails_refl q worlds

/-- Subquestion is transitive: if `q` is a subquestion of `r` and `r` of `s`,
    then `q` is a subquestion of `s`. -/
theorem isSubquestion_trans {W : Type*} (q r s : Issue W) (worlds : List W)
    (hqr : isSubquestion q r worlds = true)
    (hrs : isSubquestion r s worlds = true) :
    isSubquestion q s worlds = true :=
  questionEntails_trans s r q worlds hrs hqr

-- Partial answerhood.

/-- A proposition that fully entails an alternative of `q` partially
    answers `q`. -/
theorem propEntails_alt_implies_partiallyAnswers {W : Type*}
    (p : W → Bool) (q : Issue W) (worlds : List W)
    (alt : W → Bool) (hAlt : alt ∈ q.alternatives)
    (h : propEntails p alt worlds = true) :
    partiallyAnswers p q worlds = true := by
  rw [partiallyAnswers_iff]
  exact ⟨alt, hAlt, Or.inl h⟩

/-- Partial answerhood of an alternative implies move relevance.

If some alternative of a move partially answers the QUD directly,
the move is relevant (even without subquestions). -/
theorem partiallyAnswers_implies_relevant {W : Type*}
    (den : Issue W) (qud : Issue W) (worlds : List W)
    (alt : W → Bool) (hAlt : alt ∈ den.alternatives)
    (hPA : partiallyAnswers alt qud worlds = true) :
    moveRelevant den qud [] worlds = true := by
  rw [moveRelevant_iff]
  exact ⟨alt, hAlt, Or.inl hPA⟩

end Discourse
