import Linglib.Theories.Semantics.Questions.Basic
import Linglib.Core.Partition

/-!
# Questions/Partition.lean

Groenendijk & Stokhof (1984) Partition Semantics for Questions.

## Core Ideas

A question denotes an equivalence relation on worlds:
```
⟦?x.P(x)⟧ = λw.λv. [λx.P(w)(x) = λx.P(v)(x)]
```

Two worlds are equivalent iff the predicate has the same extension in both.
This induces a **partition** of logical space.

## Architecture

`GSQuestion` is an abbreviation for `QUD`. All partition lattice operations
(refinement, coarsening, cells) are defined in `Core/Partition.lean` and apply
to any equivalence-relation partition, not just question denotations.

This module provides question-specific constructors and interpretation.

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Groenendijk & Stokhof (1997). Questions. Handbook of Logic and Language.
-/

namespace Semantics.Questions

/-- A G&S-style question is exactly a QUD: an equivalence relation on worlds.

Two worlds are equivalent iff they give the same answer to the question.
This induces a partition of the world space. -/
abbrev GSQuestion (W : Type*) := QUD W

namespace GSQuestion

variable {W : Type*}

/-- Compatibility accessor: `equiv` is the same as `sameAnswer`. -/
abbrev equiv (q : GSQuestion W) := q.sameAnswer

-- Re-export ⊑ notation so `open scoped GSQuestion` works
scoped infix:50 " ⊑ " => QUD.refines

-- Question-specific constructors

/-- The finest possible partition (identity). Each world is its own equivalence
class. This is the "maximally informative" question. -/
def exact [BEq W] [LawfulBEq W] : GSQuestion W := QUD.exact

/-- The coarsest partition (all worlds equivalent). Conveys no information.
This is the "tautological" question (always answered "yes"). -/
def trivial : GSQuestion W := QUD.trivial

/-- Build a question from a projection function.
Two worlds are equivalent iff they have the same value under projection.

Example: `ofProject (λ w => w.weather)` asks "What's the weather?" -/
def ofProject {A : Type} [BEq A] [LawfulBEq A] (f : W → A) : GSQuestion W :=
  QUD.ofProject f

/-- Build a question from a Boolean predicate (polar question).
Partitions into {yes-worlds} and {no-worlds}. -/
def ofPredicate (p : W → Bool) : GSQuestion W :=
  QUD.ofProject p

-- Question-specific bridge

/-- Convert to the general Question type (list of characteristic functions). -/
def toQuestion (q : GSQuestion W) (worlds : List W) : Question W :=
  q.toCells worlds

/-- Convert to a Core.QUD (identity since GSQuestion = QUD). -/
def toQUD (q : GSQuestion W) : QUD W := q

/-- Convert from a QUD (identity since GSQuestion = QUD). -/
def ofQUD (qud : QUD W) : GSQuestion W := qud

theorem toQUD_ofQUD_roundtrip (q : GSQuestion W) :
    ofQUD (toQUD q) = q := rfl

theorem ofQUD_toQUD_roundtrip (qud : QUD W) :
    toQUD (ofQUD qud) = qud := rfl

end GSQuestion

-- Yes/No and Wh-Questions

/-- A yes/no (polar) question: partitions into {yes-worlds} and {no-worlds}.

Example: "Is it raining?" partitions worlds into rainy and not-rainy. -/
def polarQuestion {W : Type*} (p : W → Bool) : GSQuestion W :=
  GSQuestion.ofPredicate p

/-- A polar question is equivalent to projecting onto Bool. -/
theorem polarQuestion_eq_ofProject {W : Type*} (p : W → Bool) :
    polarQuestion p = GSQuestion.ofProject p := rfl

/-- A wh-question asks for the value of some function.

Example: "Who came?" = ofProject (λ w => w.guests)
Two worlds are equivalent iff they have the same set of guests. -/
def whQuestion {W A : Type} [BEq A] [LawfulBEq A] (f : W → A) : GSQuestion W :=
  GSQuestion.ofProject f

/-- An alternative question: which of these propositions is true?

Example: "Did John or Mary come?" -/
def alternativeQuestion {W : Type*}
    (alts : List (W → Bool)) : GSQuestion W :=
  QUD.ofProject λ w => alts.map λ p => p w

-- Exhaustivity

/-- A question demands exhaustive answers if its semantics requires
knowing exactly which cell the actual world is in.

This is the default for G&S semantics — all questions are exhaustive. -/
def isExhaustive {W : Type*} (_q : GSQuestion W) : Bool := true

/-- The exhaustive interpretation of a polar question is complete:
answering requires saying "yes" or "no", not "I don't know". -/
theorem polar_exhaustive {W : Type*} (p : W → Bool) (w : W) :
    (polarQuestion p).numCells [w] <= 2 := by
  unfold polarQuestion GSQuestion.ofPredicate QUD.numCells QUD.toCells
  simp only [List.foldl_cons, List.foldl_nil, List.any_nil, Bool.false_eq_true,
    ↓reduceIte, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
  omega

-- Information Sets

/-- An information set J ⊆ I represents what the questioner knows.
J is the set of indices compatible with the questioner's factual knowledge.

G&S 1984, p. 350: "One may argue that using an information set to represent
the questioner's informational state involves idealizations. [...] We think
these idealizations are harmless." -/
abbrev InfoSet (W : Type*) := W → Bool

/-- The total information set (no factual knowledge). -/
def totalIgnorance {W : Type*} : InfoSet W := λ _ => true

/-- Check if a world is in the information set. -/
def InfoSet.contains {W : Type*} (j : InfoSet W) (w : W) : Bool := j w

/-- Intersection of a proposition with an information set. -/
def InfoSet.intersect {W : Type*} (j : InfoSet W) (p : W → Bool) : W → Bool :=
  λ w => j w && p w

-- Restricted Partition (J/Q)

/-- The restricted cells as a list of characteristic functions.

These are the cells of the partition J/Q: each cell P' is some P ∩ J
where P is a cell of I/Q and P ∩ J ≠ ∅.

Moved from PragmaticAnswerhood: this is a general partition operation
useful beyond pragmatic answerhood (e.g., for computing pragmatic
exhaustivity, or for the GSQuestion↔Issue bridge). -/
def GSQuestion.restrictedCells {W : Type*} (q : GSQuestion W) (j : InfoSet W)
    (worlds : List W) : List (W → Bool) :=
  let jWorlds := worlds.filter j
  let reps := jWorlds.foldl (λ acc w =>
    if acc.any λ r => q.equiv r w then acc else w :: acc) []
  reps.map λ rep => λ w => j w && q.equiv rep w

/-- Elements of the foldl-built representative list come from the input list. -/
theorem foldl_reps_mem {W : Type*} (equiv : W → W → Bool)
    (l : List W) :
    ∀ (init : List W) (r : W),
    r ∈ l.foldl (fun acc w =>
      if acc.any (fun r => equiv r w) then acc else w :: acc) init →
    r ∈ init ∨ r ∈ l := by
  induction l with
  | nil => intro _ _ h; exact Or.inl h
  | cons w ws ih =>
    intro init r h
    simp only [List.foldl_cons] at h
    split_ifs at h
    · rcases ih init r h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases ih (w :: init) r h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Every J-world is Q-equivalent to some representative in restrictedCells.

This is the covering property: the foldl in restrictedCells produces reps
such that every input element is equivalent to some rep. -/
theorem restrictedCells_cover {W : Type*}
    (q : GSQuestion W) (j : InfoSet W) (worlds : List W) (w : W)
    (hw : w ∈ worlds.filter j) :
    ∃ cell ∈ q.restrictedCells j worlds, cell w = true := by
  simp only [GSQuestion.restrictedCells, List.mem_map]
  suffices h : ∃ rep ∈ (worlds.filter j).foldl (fun acc w' =>
      if acc.any (fun r => q.equiv r w') then acc else w' :: acc) [],
      q.equiv rep w = true by
    obtain ⟨rep, hrep, hequiv⟩ := h
    exact ⟨fun w' => j w' && q.equiv rep w', ⟨rep, hrep, rfl⟩,
           by rw [Bool.and_eq_true]; exact ⟨(List.mem_filter.mp hw).2, hequiv⟩⟩
  set l := worlds.filter j with hl_def
  suffices gen : ∀ init : List W,
      w ∈ l ∨ init.any (fun r => q.equiv r w) = true →
      ∃ rep ∈ l.foldl (fun acc w' =>
          if acc.any (fun r => q.equiv r w') then acc else w' :: acc) init,
        q.equiv rep w = true from
    gen [] (Or.inl hw)
  induction l with
  | nil =>
    intro init h
    simp only [List.foldl_nil]
    rcases h with h | h
    · exact absurd h List.not_mem_nil
    · exact List.any_eq_true.mp h
  | cons w' rest ih =>
    intro init h
    simp only [List.foldl_cons]
    split_ifs with hcover
    · apply ih
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | hmem
        · exact Or.inr (by simp only [List.any_eq_true] at hcover ⊢; exact hcover)
        · exact Or.inl hmem
      · exact Or.inr h
    · apply ih
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | hmem
        · exact Or.inr (by simp only [List.any_cons, q.refl, Bool.true_or])
        · exact Or.inl hmem
      · exact Or.inr (by simp only [List.any_cons, h, Bool.or_true])

/-- Every cell produced by restrictedCells has a witness in `worlds`. -/
theorem restrictedCells_inhabited {W : Type*}
    (q : GSQuestion W) (j : InfoSet W) (worlds : List W) :
    ∀ cell ∈ q.restrictedCells j worlds, ∃ w ∈ worlds, cell w = true := by
  intro cell hcell
  simp only [GSQuestion.restrictedCells, List.mem_map] at hcell
  obtain ⟨rep, hrep_mem, rfl⟩ := hcell
  have hrep_jw : rep ∈ worlds.filter j := by
    rcases foldl_reps_mem q.sameAnswer (worlds.filter j) [] rep hrep_mem with h | h
    · simp at h
    · exact h
  obtain ⟨hrep_w, hj_rep⟩ := List.mem_filter.mp hrep_jw
  exact ⟨rep, hrep_w, by simp [hj_rep, q.refl]⟩

end Semantics.Questions
