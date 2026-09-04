import Linglib.Discourse.Commitment.Basic
import Linglib.Semantics.Mood.Defs

/-!
# The Table

The context structure of [farkas-bruce-2010]: the participants' discourse commitments, the
common ground, and the Table, a stack of items under discussion — each a sentence with its
denotation, the set of its complete answers, `{p}` for a declarative and `{p, ¬p}` for a polar
interrogative. Every item placed on the Table projects the common grounds that would settle it:
the projected set, which the paper notes can always be rebuilt from the common ground and the
Table, is derived here rather than stored. A default assertion commits its author and places its
sentence on the Table, projecting confirmation; a default polar question only places its sentence
on the Table, projecting an inquisitive set; confirmation commits the addressee; once every
participant is committed, the common ground increases and the settled items are popped; total
denial is the assertion of the negation, after which no projected common ground is consistent
and the conversation is in crisis, until the participants agree to disagree.

## Main definitions

* `Commitment.Table A W`, `Table.Item` — the context structure and its items.
* `Table.dc`, `Table.contextSet`, `Table.projectedSet`, `Table.IsStable`, `Table.InCrisis`.
* `Table.assert`, `Table.polarQuestion`, `Table.confirm`, `Table.increaseCG`,
  `Table.agreeToDisagree` — the moves of §§3–4.

## Main results

* `Table.assert_cg`, `Table.polarQuestion_cg` — neither initiating move changes the common
  ground; `Table.projectedSet_assert`, `Table.projectedSet_polarQuestion` — what they project.
* `Table.deny_eq_assert_compl` — total denial is the assertion of the negation (22).
* `Table.projectedSet_assert_compl` — after a denial nothing consistent is projected (21).

## References

* [D. F. Farkas and K. B. Bruce, *On Reacting to Assertions and Polar Questions*
  (2010)][farkas-bruce-2010]
-/

namespace Commitment

open Filter
open Mood (Illocutionary)

/-- An item on the Table: a sentence, by its sentential feature, with its denotation. -/
@[ext]
structure Table.Item (W : Type*) where
  mood : Illocutionary
  denotation : Set (Set W)

/-- The context structure `K` of [farkas-bruce-2010]: the Table as a stack, the participants'
discourse commitments, and the common ground. -/
@[ext]
structure Table (A W : Type*) where
  stack : List (Table.Item W)
  commitments : State A W
  cg : Filter W

namespace Table

variable {A W : Type*} (K : Table A W) (a : A) (p : Set W)

/-- The initial context: nothing on the Table, no commitments, the trivial common ground. -/
def empty : Table A W := ⟨[], ∅, ⊤⟩

instance : Inhabited (Table A W) := ⟨empty⟩

/-- A conversation is stable when its Table is empty. -/
def IsStable : Prop := K.stack = []

/-- `DC_a`: the propositions `a` has publicly committed to. -/
def dc : Set (Set W) := contents (ofCommitter K.commitments a)

/-- The worlds compatible with the common ground. -/
def contextSet : Set W := K.cg.ker

/-- `p` is decided relative to the common ground. -/
def Decided : Prop := p ∈ K.cg ∨ pᶜ ∈ K.cg

/-- `ps ∪ P`: add each proposition of `P` to each projected common ground, discarding the
inconsistent results. -/
def project (ps : Set (Filter W)) (P : Set (Set W)) : Set (Filter W) :=
  {f | ∃ cg ∈ ps, ∃ p ∈ P, f = cg ⊓ 𝓟 p ∧ f ≠ ⊥}

/-- The projected set, rebuilt from the common ground by the items on the Table, oldest first:
the common grounds that canonically settle what is at issue. -/
def projectedSet : Set (Filter W) :=
  K.stack.foldr (fun i ps => project ps i.denotation) {K.cg}

/-- A conversation is in crisis when its common ground or every projected common ground is
inconsistent. -/
def InCrisis : Prop := K.cg = ⊥ ∨ ∀ f ∈ K.projectedSet, f = ⊥

/-- Place an item on the Table. -/
def push (i : Item W) : Table A W := { K with stack := i :: K.stack }

/-- Remove the top item. -/
def pop : Table A W := { K with stack := K.stack.tail }

/-- Commit `a` to `p`. -/
def commit (source : Commitment.Source := .selfGenerated) (force : Commitment.Force := .doxastic) :
    Table A W :=
  { K with commitments := insert (Commitment.commit a p force source) K.commitments }

/-- Default assertion (9): `a` commits to `p` and places the declarative on the Table. -/
def assert : Table A W := (K.commit a p).push ⟨.declarative, {p}⟩

/-- Default polar question (12): place the interrogative on the Table. -/
def polarQuestion : Table A W := K.push ⟨.interrogative, {p, pᶜ}⟩

/-- Assertion confirmation (16): the addressee commits to the asserted proposition. -/
def confirm : Table A W := K.commit a p .otherGenerated

/-- Every participant is committed to `p`. -/
def Shared : Prop := ∀ a : A, p ∈ K.dc a

open scoped Classical in
/-- The common-ground increasing operation `M'` (17): `p` enters the common ground, leaves the
individual commitment lists, and the items it decides are popped from the top of the Table. -/
noncomputable def increaseCG : Table A W where
  stack := K.stack.dropWhile fun i => decide (∃ q ∈ i.denotation, q ∈ K.cg ⊓ 𝓟 p)
  commitments := {c ∈ K.commitments | c.content ≠ p}
  cg := K.cg ⊓ 𝓟 p

open scoped Classical in
/-- Agreeing to disagree (23): the contradictory pair leaves the Table, the commitments stay. -/
noncomputable def agreeToDisagree : Table A W :=
  { K with stack := K.stack.filter fun i => decide (i.denotation ≠ {p} ∧ i.denotation ≠ {pᶜ}) }

@[simp] theorem empty_stack : (empty : Table A W).stack = [] := rfl
@[simp] theorem empty_commitments : (empty : Table A W).commitments = ∅ := rfl
@[simp] theorem empty_cg : (empty : Table A W).cg = ⊤ := rfl
@[simp] theorem push_stack (i : Item W) : (K.push i).stack = i :: K.stack := rfl
@[simp] theorem push_commitments (i : Item W) : (K.push i).commitments = K.commitments := rfl
@[simp] theorem push_cg (i : Item W) : (K.push i).cg = K.cg := rfl
@[simp] theorem commit_stack (s f) : (K.commit a p s f).stack = K.stack := rfl
@[simp] theorem commit_cg (s f) : (K.commit a p s f).cg = K.cg := rfl
@[simp] theorem assert_stack : (K.assert a p).stack = ⟨.declarative, {p}⟩ :: K.stack := rfl
@[simp] theorem assert_cg : (K.assert a p).cg = K.cg := rfl
@[simp] theorem assert_commitments :
    (K.assert a p).commitments = insert (Commitment.commit a p) K.commitments := rfl
@[simp] theorem polarQuestion_stack :
    (K.polarQuestion p).stack = ⟨.interrogative, {p, pᶜ}⟩ :: K.stack := rfl
@[simp] theorem polarQuestion_cg : (K.polarQuestion p).cg = K.cg := rfl
@[simp] theorem polarQuestion_commitments : (K.polarQuestion p).commitments = K.commitments := rfl
@[simp] theorem increaseCG_cg : (K.increaseCG p).cg = K.cg ⊓ 𝓟 p := rfl

@[simp] theorem empty_isStable : (empty : Table A W).IsStable := rfl

@[simp] theorem dc_empty : (empty : Table A W).dc a = ∅ := by
  simp [dc, ofCommitter, contents]

@[simp] theorem dc_push (i : Item W) : (K.push i).dc = K.dc := rfl

@[simp] theorem dc_polarQuestion : (K.polarQuestion p).dc = K.dc := rfl

theorem mem_dc_commit_self (s f) : p ∈ (K.commit a p s f).dc a :=
  ⟨Commitment.commit a p f s, ⟨⟨Set.mem_insert _ _, rfl⟩, rfl⟩, rfl⟩

theorem mem_dc_commit_iff (s f) {b : A} {q : Set W} :
    q ∈ (K.commit a p s f).dc b ↔ (b = a ∧ q = p) ∨ q ∈ K.dc b := by
  simp only [dc, ofCommitter, contents, commit, Set.mem_image, Set.mem_ofPred_eq,
    Set.mem_insert_iff]
  constructor
  · rintro ⟨c, ⟨⟨rfl | hc, hb⟩, hp⟩, rfl⟩
    · exact Or.inl ⟨hb.symm, rfl⟩
    · exact Or.inr ⟨c, ⟨⟨hc, hb⟩, hp⟩, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨c, ⟨⟨hc, hb⟩, hp⟩, rfl⟩)
    · exact ⟨_, ⟨⟨Or.inl rfl, rfl⟩, rfl⟩, rfl⟩
    · exact ⟨c, ⟨⟨Or.inr hc, hb⟩, hp⟩, rfl⟩

@[simp] theorem dc_commit_self (s f) : (K.commit a p s f).dc a = insert p (K.dc a) := by
  ext q
  rw [mem_dc_commit_iff, Set.mem_insert_iff]
  exact ⟨fun h => h.elim (Or.inl ∘ And.right) Or.inr,
    fun h => h.elim (fun e => Or.inl ⟨rfl, e⟩) Or.inr⟩

@[simp] theorem dc_assert : (K.assert a p).dc a = insert p (K.dc a) := dc_commit_self K a p _ _

theorem dc_commit_of_ne (s f) {b : A} (h : b ≠ a) : (K.commit a p s f).dc b = K.dc b := by
  ext q
  rw [mem_dc_commit_iff]
  exact ⟨fun h' => h'.elim (fun e => absurd e.1 h) id, Or.inr⟩

theorem not_isStable_push (i : Item W) : ¬ (K.push i).IsStable := List.cons_ne_nil _ _

/-- The asserted proposition enters the author's commitments. -/
theorem mem_dc_assert : p ∈ (K.assert a p).dc a :=
  ⟨Commitment.commit a p, ⟨⟨Set.mem_insert _ _, rfl⟩, rfl⟩, rfl⟩

/-- A stable conversation projects only its common ground. -/
theorem projectedSet_of_isStable (h : K.IsStable) : K.projectedSet = {K.cg} := by
  rw [projectedSet, show K.stack = [] from h]
  rfl

@[simp] theorem projectedSet_push (i : Item W) :
    (K.push i).projectedSet = project K.projectedSet i.denotation := rfl

@[simp] theorem projectedSet_commit (s f) : (K.commit a p s f).projectedSet = K.projectedSet := rfl

/-- An assertion projects confirmation: its content is added to each projected common ground. -/
theorem projectedSet_assert : (K.assert a p).projectedSet = project K.projectedSet {p} := rfl

/-- A polar question projects resolution: each alternative is added to each projected common
ground. -/
theorem projectedSet_polarQuestion :
    (K.polarQuestion p).projectedSet = project K.projectedSet {p, pᶜ} := rfl

/-- Total denial (22) is the assertion of the negation. -/
theorem deny_eq_assert_compl (b : A) :
    (K.assert b pᶜ).commitments = insert (Commitment.commit b pᶜ) K.commitments := rfl

/-- After an assertion has been denied, nothing consistent is projected (21). -/
theorem projectedSet_assert_compl (b : A) : ((K.assert a p).assert b pᶜ).projectedSet = ∅ := by
  ext f
  simp only [projectedSet_assert, project, Set.mem_singleton_iff, exists_eq_left,
    Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  rintro _ ⟨cg, -, rfl, -⟩ rfl
  simp [inf_assoc, inf_principal]

/-- A denied assertion leaves the conversation in crisis. -/
theorem inCrisis_assert_compl (b : A) : ((K.assert a p).assert b pᶜ).InCrisis :=
  Or.inr fun f hf => by simp [projectedSet_assert_compl] at hf

end Table

end Commitment
