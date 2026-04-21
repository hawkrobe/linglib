import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Set.Basic

/-!
# QUD: Equivalence-Relation Partitioning of a Meaning Space
@cite{roberts-2012}

A `QUD M` partitions a meaning space `M` via an equivalence relation: two
meanings are equivalent iff they "answer the question the same way."

## Design

A `QUD M` is a `Setoid M` together with decidability of its equivalence
relation. Setoid is the single source of truth for the equivalence
structure (no separately-stored Bool field that can drift); decidability
is bundled so consumer code doesn't need to thread `[DecidableRel q.r]`
through every signature.

This file is the algebraic core: the bundle, constructors (`trivial`,
`compose`, `ofProject`, `ofDecEq`, `exact`), equivalence-class cells,
the Bool-view (`sameAnswer`), and the `ProductQUD` projections.

## Place in the Question API

`QUD M` lives inside `Core/Question/` (rather than a parallel
`Core/QUD/` directory) as the construction-side API for partition-shaped
questions. The inquisitive `Question W` (`Core/Question/Basic.lean`) is
the consumer-side type with the richer lattice and answerhood structure;
`Question.fromSetoid` (`Core/Mood/PartitionAsInquiry.lean`) is the
canonical bridge from a `Setoid` (or `QUD`) into an inquisitive
`Question`. Long-term mathlib alignment is `abbrev QUD M := Setoid M`
once the Bool-API consumer sites have migrated to `[DecidableRel s.r]`
plus `Prop`-valued outputs; the bundled `{toSetoid, decR}` shape is a
transitional form that preserves Bool ergonomics while keeping `Setoid`
as the single source of truth.
-/

/-- A QUD partitions a meaning space `M` via an equivalence relation.
Bundles a `Setoid M` with decidability of its equivalence relation —
Setoid is the source of truth, decidability is along for the ride. -/
structure QUD (M : Type*) where
  /-- The underlying setoid (equivalence relation + reflexivity/symmetry/transitivity). -/
  toSetoid : Setoid M
  /-- Decidability of the equivalence relation. -/
  decR : DecidableRel toSetoid.r := by infer_instance

namespace QUD

variable {M : Type*}

/-- Forward `r` from the underlying setoid. -/
@[reducible] def r (q : QUD M) : M → M → Prop := q.toSetoid.r

instance instDecidableRel (q : QUD M) : DecidableRel q.r := q.decR

/-- Forward `iseqv` from the underlying setoid. -/
theorem iseqv (q : QUD M) : Equivalence q.r := q.toSetoid.iseqv

-- ════════════════════════════════════════════════════
-- § 1. Bool-view (sameAnswer + Bool-valued refl/symm/trans)
-- ════════════════════════════════════════════════════

/-- Decidable equivalence as a `Bool`. -/
def sameAnswer (q : QUD M) (a b : M) : Bool := decide (q.r a b)

@[simp] theorem sameAnswer_eq_true_iff (q : QUD M) (a b : M) :
    q.sameAnswer a b = true ↔ q.r a b := decide_eq_true_iff

theorem sameAnswer_of_r {q : QUD M} {a b : M} (h : q.r a b) :
    q.sameAnswer a b = true := decide_eq_true h

theorem r_of_sameAnswer {q : QUD M} {a b : M} (h : q.sameAnswer a b = true) :
    q.r a b := of_decide_eq_true h

theorem refl (q : QUD M) (m : M) : q.sameAnswer m m = true :=
  decide_eq_true (q.iseqv.refl m)

theorem symm (q : QUD M) (a b : M) :
    q.sameAnswer a b = q.sameAnswer b a := by
  by_cases h : q.r a b
  · rw [sameAnswer_of_r h, sameAnswer_of_r (q.iseqv.symm h)]
  · have h' : ¬ q.r b a := mt q.iseqv.symm h
    show decide (q.r a b) = decide (q.r b a)
    rw [decide_eq_false h, decide_eq_false h']

theorem trans (q : QUD M) (a b c : M)
    (h1 : q.sameAnswer a b = true) (h2 : q.sameAnswer b c = true) :
    q.sameAnswer a c = true :=
  decide_eq_true (q.iseqv.trans (of_decide_eq_true h1) (of_decide_eq_true h2))

section EquivalenceProperties
variable (q : QUD M)

/-- Reflexivity is guaranteed by construction. -/
theorem isReflexive : ∀ m, q.sameAnswer m m = true := q.refl

/-- Symmetry is guaranteed by construction. -/
theorem isSymmetric : ∀ m1 m2, q.sameAnswer m1 m2 = q.sameAnswer m2 m1 := q.symm

/-- Transitivity is guaranteed by construction. -/
theorem isTransitive : ∀ m1 m2 m3,
    q.sameAnswer m1 m2 = true → q.sameAnswer m2 m3 = true → q.sameAnswer m1 m3 = true :=
  q.trans

end EquivalenceProperties

@[simp] theorem toSetoid_r (q : QUD M) (a b : M) :
    q.toSetoid.r a b ↔ q.r a b := Iff.rfl

-- ════════════════════════════════════════════════════
-- § 2. Constructors as bundles over mathlib Setoid
-- ════════════════════════════════════════════════════

/-- Trivial QUD: all meanings are equivalent. Mathlib `⊤ : Setoid M`. -/
def trivial : QUD M := ⟨⊤, λ _ _ => .isTrue ⟨⟩⟩

@[simp] theorem trivial_r (m1 m2 : M) : (trivial : QUD M).r m1 m2 := ⟨⟩

@[simp] theorem trivial_sameAnswer (m1 m2 : M) :
    (trivial : QUD M).sameAnswer m1 m2 = true := decide_eq_true ⟨⟩

/-- Compose two QUDs: equivalent iff equivalent under both. Mathlib `q1 ⊓ q2`. -/
def compose (q1 q2 : QUD M) : QUD M where
  toSetoid := q1.toSetoid ⊓ q2.toSetoid
  decR := λ a b => decidable_of_iff _ Setoid.inf_iff_and.symm

@[simp] theorem compose_r (q1 q2 : QUD M) (a b : M) :
    (compose q1 q2).r a b ↔ q1.r a b ∧ q2.r a b := Setoid.inf_iff_and

@[simp] theorem compose_sameAnswer (q1 q2 : QUD M) (m1 m2 : M) :
    (compose q1 q2).sameAnswer m1 m2 =
      (q1.sameAnswer m1 m2 && q2.sameAnswer m1 m2) := by
  by_cases h1 : q1.r m1 m2 <;> by_cases h2 : q2.r m1 m2 <;>
    simp [sameAnswer, compose_r, h1, h2]

theorem compose_sameAnswer_iff (q1 q2 : QUD M) (m1 m2 : M) :
    (compose q1 q2).sameAnswer m1 m2 = true ↔
    q1.sameAnswer m1 m2 = true ∧ q2.sameAnswer m1 m2 = true := by
  simp only [compose_sameAnswer, Bool.and_eq_true]

instance : Mul (QUD M) where
  mul := compose

@[simp] theorem mul_eq_compose (q1 q2 : QUD M) : q1 * q2 = compose q1 q2 := rfl

@[simp] theorem mul_r (q1 q2 : QUD M) (a b : M) :
    (q1 * q2).r a b ↔ q1.r a b ∧ q2.r a b := compose_r q1 q2 a b

@[simp] theorem mul_sameAnswer (q1 q2 : QUD M) (m1 m2 : M) :
    (q1 * q2).sameAnswer m1 m2 = (q1.sameAnswer m1 m2 && q2.sameAnswer m1 m2) :=
  compose_sameAnswer q1 q2 m1 m2

/-- The equivalence class (partition cell) of a meaning under a QUD. -/
def cell (q : QUD M) (m : M) : Set M := {m' : M | q.r m m'}

theorem mem_cell_iff_r (q : QUD M) (m m' : M) :
    m' ∈ q.cell m ↔ q.r m m' := Iff.rfl

theorem mem_cell_iff (q : QUD M) (m m' : M) :
    m' ∈ q.cell m ↔ q.sameAnswer m m' = true := by
  simp only [cell, Set.mem_setOf_eq, sameAnswer_eq_true_iff]

theorem cell_self (q : QUD M) (m : M) : m ∈ q.cell m := q.iseqv.refl m

theorem mem_cell_symm (q : QUD M) (m m' : M) :
    m' ∈ q.cell m ↔ m ∈ q.cell m' := by
  simp only [cell, Set.mem_setOf_eq]
  exact ⟨q.iseqv.symm, q.iseqv.symm⟩

/-- Build QUD from a projection function with `DecidableEq` codomain.
The `name` argument is documentation-only; it is discarded. -/
def ofDecEq {α : Type*} [DecidableEq α]
    (project : M → α) (name : String := "") : QUD M :=
  let _ := name
  { toSetoid := Setoid.comap project ⊥
    decR := λ a b => inferInstanceAs (Decidable (project a = project b)) }

@[simp] theorem ofDecEq_r {α : Type*} [DecidableEq α]
    (project : M → α) (name : String) (w v : M) :
    (ofDecEq project name).r w v ↔ project w = project v := Iff.rfl

@[simp] theorem ofDecEq_sameAnswer {α : Type*} [DecidableEq α]
    (project : M → α) (name : String) (w v : M) :
    (ofDecEq project name).sameAnswer w v = decide (project w = project v) := rfl

theorem ofDecEq_sameAnswer_iff {α : Type*} [DecidableEq α]
    (project : M → α) (name : String) (w v : M) :
    (ofDecEq project name).sameAnswer w v = true ↔ project w = project v := by
  simp only [ofDecEq_sameAnswer, decide_eq_true_eq]

/-- Build QUD from a projection function with `BEq`/`LawfulBEq` codomain.
The `name` argument is documentation-only; it is discarded. -/
def ofProject {A : Type*} [BEq A] [LawfulBEq A]
    (f : M → A) (name : String := "") : QUD M :=
  let _ := name
  { toSetoid := Setoid.comap f ⊥
    decR := λ a b => decidable_of_iff (f a == f b) (by simp [beq_iff_eq]) }

@[simp] theorem ofProject_r {A : Type*} [BEq A] [LawfulBEq A]
    (f : M → A) (m1 m2 : M) :
    (ofProject f).r m1 m2 ↔ f m1 = f m2 := Iff.rfl

@[simp] theorem ofProject_sameAnswer {A : Type*} [BEq A] [LawfulBEq A]
    (f : M → A) (m1 m2 : M) :
    (ofProject f).sameAnswer m1 m2 = (f m1 == f m2) := by
  rcases hb : (f m1 == f m2) with _ | _
  · have hne : ¬ (f m1 = f m2) := by
      intro heq; rw [heq, beq_self_eq_true] at hb; cases hb
    have hne' : ¬ (ofProject f).r m1 m2 := hne
    show decide ((ofProject f).r m1 m2) = false
    exact decide_eq_false hne'
  · have heq : f m1 = f m2 := LawfulBEq.eq_of_beq hb
    have heq' : (ofProject f).r m1 m2 := heq
    show decide ((ofProject f).r m1 m2) = true
    exact decide_eq_true heq'

theorem ofProject_sameAnswer_iff {A : Type*} [BEq A] [LawfulBEq A]
    (f : M → A) (m1 m2 : M) :
    (ofProject f).sameAnswer m1 m2 = true ↔ f m1 = f m2 := by
  simp only [ofProject_sameAnswer, beq_iff_eq]

theorem ofProject_cell_eq_fiber {A : Type*} [BEq A] [LawfulBEq A] (f : M → A) (m : M) :
    (ofProject f).cell m = {m' : M | f m' = f m} := by
  ext m'
  simp only [cell, Set.mem_setOf_eq, ofProject_r]
  exact eq_comm

section BEqConstructors
variable [BEq M]

/-- Identity QUD: each meaning is its own equivalence class. -/
def exact [LawfulBEq M] : QUD M := ofProject (id : M → M) "exact"

@[simp] theorem exact_r [LawfulBEq M] (m1 m2 : M) :
    (exact : QUD M).r m1 m2 ↔ m1 = m2 := Iff.rfl

@[simp] theorem exact_sameAnswer [LawfulBEq M] (m1 m2 : M) :
    (exact : QUD M).sameAnswer m1 m2 = (m1 == m2) :=
  ofProject_sameAnswer (id : M → M) m1 m2

theorem exact_sameAnswer_iff [LawfulBEq M] (m1 m2 : M) :
    (exact : QUD M).sameAnswer m1 m2 = true ↔ m1 = m2 := by
  simp only [exact_sameAnswer, beq_iff_eq]

end BEqConstructors

end QUD

namespace ProductQUD

variable {A B : Type} [BEq A] [BEq B] [LawfulBEq A] [LawfulBEq B]

/-- QUD that cares only about first component. -/
def fst : QUD (A × B) := QUD.ofProject Prod.fst "fst"

/-- QUD that cares only about second component. -/
def snd : QUD (A × B) := QUD.ofProject Prod.snd "snd"

/-- QUD that cares about both components (exact). -/
def both : QUD (A × B) := QUD.exact (M := A × B)

omit [BEq B] [LawfulBEq B] in
@[simp] theorem fst_sameAnswer (p1 p2 : A × B) :
    (fst : QUD (A × B)).sameAnswer p1 p2 = (p1.fst == p2.fst) :=
  QUD.ofProject_sameAnswer _ _ _

omit [BEq B] [LawfulBEq B] in
theorem fst_sameAnswer_iff (p1 p2 : A × B) :
    (fst : QUD (A × B)).sameAnswer p1 p2 = true ↔ p1.fst = p2.fst := by
  simp only [fst_sameAnswer, beq_iff_eq]

omit [BEq A] [LawfulBEq A] in
@[simp] theorem snd_sameAnswer (p1 p2 : A × B) :
    (snd : QUD (A × B)).sameAnswer p1 p2 = (p1.snd == p2.snd) :=
  QUD.ofProject_sameAnswer _ _ _

omit [BEq A] [LawfulBEq A] in
theorem snd_sameAnswer_iff (p1 p2 : A × B) :
    (snd : QUD (A × B)).sameAnswer p1 p2 = true ↔ p1.snd = p2.snd := by
  simp only [snd_sameAnswer, beq_iff_eq]

@[simp] theorem both_sameAnswer (p1 p2 : A × B) :
    (both : QUD (A × B)).sameAnswer p1 p2 = (p1 == p2) := QUD.exact_sameAnswer p1 p2

theorem both_sameAnswer_iff (p1 p2 : A × B) :
    (both : QUD (A × B)).sameAnswer p1 p2 = true ↔ p1 = p2 := by
  simp only [both_sameAnswer, beq_iff_eq]

end ProductQUD
