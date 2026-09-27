module

public import Linglib.Core.Order.Interval
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.Order

/-!
# Allen's interval relations

This file defines the thirteen relations of Allen's interval algebra between two nonempty
intervals on a linear order, and proves that exactly one of them holds between two proper
intervals, those with `fst < snd`. Allen introduced the algebra for temporal reasoning: the
relations *before*, *meets*, *overlaps*, *starts*, *during* and *finishes*, their inverses, and
*equal*, each defined by inequalities between the four endpoints. The names here are Allen's,
except that *before* and *after* are `precedes` and `precededBy`, so that they do not collide with
the weak `NonemptyInterval.isBefore`, and the inverses are spelled out as `metBy`, `overlappedBy`,
`startedBy`, `contains` and `finishedBy`.

A general relation of the algebra is a set of atoms, a `Finset AllenRelation`, which holds when
one of its atoms does (`holdsIn`). The relational vocabulary of `Core/Order/Interval.lean` and
mathlib's containment order on `NonemptyInterval` are such sets: `isBefore` is
`{precedes, meets}`, `i ≤ j` is `{starts, equal, finishes, during}`, and `overlaps` is the
complement of `{precedes, precededBy}`.

## Main definitions

* `AllenRelation`: the thirteen atoms, with `inverse` swapping the two intervals.
* `AllenRelation.holds`: the endpoint inequalities defining each atom.
* `NonemptyInterval.allenRel`: the atom holding between two intervals.
* `AllenRelation.holdsIn`: a set of atoms holds when one of its members does.

## Main results

* `AllenRelation.holds_iff_signature`: between proper intervals an atom holds exactly when the
  four endpoint comparisons are the atom's signature, so at most one atom holds (`holds_unique`).
* `NonemptyInterval.allenRel_holds`, `holds_iff_allenRel_eq`: `allenRel` is an atom that holds,
  and between proper intervals the only one.
* `NonemptyInterval.le_iff_holdsIn`, `overlaps_iff_holdsIn`, and the other bridges: each interval
  relation as a set of atoms.

## Implementation notes

Allen assumes that every interval is proper. Mathlib's `NonemptyInterval` admits points, between
which uniqueness fails: at a single point `meets`, `metBy` and `equal` all hold. Existence and the
bridges to the interval vocabulary hold between all intervals, and only the uniqueness results
carry the two properness hypotheses. Allen's transitivity table, the composition of two atoms as a
set of atoms, is not formalized.

## References

* [allen-1983]
-/

@[expose] public section

/-- The thirteen atoms of Allen's interval algebra, each defined by inequalities between the
endpoints of two intervals `i` and `j` (`AllenRelation.holds`). -/
inductive AllenRelation where
  /-- `i` ends strictly before `j` starts, `i.snd < j.fst`; Allen's *before*. -/
  | precedes
  /-- `i` ends exactly where `j` starts, `i.snd = j.fst`. -/
  | meets
  /-- `i` starts first and the two properly overlap, `i.fst < j.fst < i.snd < j.snd`. -/
  | overlaps
  /-- `j` is a proper final part of `i`, `i.fst < j.fst` and `i.snd = j.snd`. -/
  | finishedBy
  /-- `j` lies strictly inside `i`, `i.fst < j.fst` and `j.snd < i.snd`. -/
  | contains
  /-- `i` is a proper initial part of `j`, `i.fst = j.fst` and `i.snd < j.snd`. -/
  | starts
  /-- `i` and `j` have the same endpoints. -/
  | equal
  /-- `j` is a proper initial part of `i`, `i.fst = j.fst` and `j.snd < i.snd`. -/
  | startedBy
  /-- `i` lies strictly inside `j`, `j.fst < i.fst` and `i.snd < j.snd`. -/
  | during
  /-- `i` is a proper final part of `j`, `j.fst < i.fst` and `i.snd = j.snd`. -/
  | finishes
  /-- `j` starts first and the two properly overlap, `j.fst < i.fst < j.snd < i.snd`. -/
  | overlappedBy
  /-- `i` starts exactly where `j` ends, `i.fst = j.snd`. -/
  | metBy
  /-- `j` ends strictly before `i` starts, `j.snd < i.fst`; Allen's *after*. -/
  | precededBy
  deriving DecidableEq, Fintype, Repr

namespace AllenRelation

theorem card : Fintype.card AllenRelation = 13 := rfl

/-! ### The inverse -/

/-- The inverse of an atom, the relation holding when the two intervals are swapped. -/
def inverse : AllenRelation → AllenRelation
  | precedes     => precededBy
  | meets        => metBy
  | overlaps     => overlappedBy
  | finishedBy   => finishes
  | contains     => during
  | starts       => startedBy
  | equal        => equal
  | startedBy    => starts
  | during       => contains
  | finishes     => finishedBy
  | overlappedBy => overlaps
  | metBy        => meets
  | precededBy   => precedes

@[simp] theorem inverse_inverse (r : AllenRelation) : r.inverse.inverse = r := by cases r <;> rfl

theorem inverse_involutive : Function.Involutive inverse := inverse_inverse

/-- `equal` is the only self-inverse atom. -/
theorem inverse_eq_self_iff {r : AllenRelation} : r.inverse = r ↔ r = equal := by
  cases r <;> simp [inverse]

/-! ### The atoms as relations -/

variable {T : Type*} [LinearOrder T]

/-- The endpoint inequalities defining each atom. -/
def holds : AllenRelation → NonemptyInterval T → NonemptyInterval T → Prop
  | precedes,     i, j => i.snd < j.fst
  | meets,        i, j => i.snd = j.fst
  | overlaps,     i, j => i.fst < j.fst ∧ j.fst < i.snd ∧ i.snd < j.snd
  | finishedBy,   i, j => i.fst < j.fst ∧ i.snd = j.snd
  | contains,     i, j => i.fst < j.fst ∧ j.snd < i.snd
  | starts,       i, j => i.fst = j.fst ∧ i.snd < j.snd
  | equal,        i, j => i.fst = j.fst ∧ i.snd = j.snd
  | startedBy,    i, j => i.fst = j.fst ∧ j.snd < i.snd
  | during,       i, j => j.fst < i.fst ∧ i.snd < j.snd
  | finishes,     i, j => j.fst < i.fst ∧ i.snd = j.snd
  | overlappedBy, i, j => j.fst < i.fst ∧ i.fst < j.snd ∧ j.snd < i.snd
  | metBy,        i, j => i.fst = j.snd
  | precededBy,   i, j => j.snd < i.fst

instance (r : AllenRelation) (i j : NonemptyInterval T) : Decidable (r.holds i j) := by
  cases r <;> dsimp only [holds] <;> infer_instance

variable {i j : NonemptyInterval T}

@[simp] theorem inverse_holds (r : AllenRelation) : r.inverse.holds j i ↔ r.holds i j := by
  cases r <;> simp [holds, inverse, and_comm, and_left_comm, eq_comm]

@[simp] theorem equal_holds_iff : equal.holds i j ↔ i = j := by
  rw [NonemptyInterval.ext_iff, Prod.ext_iff]; exact Iff.rfl

/-! ### Uniqueness between proper intervals

Between proper intervals each atom fixes the comparison of every endpoint of `i` with every
endpoint of `j`, its *signature*, and distinct atoms have distinct signatures. -/

/-- The comparisons of `i.fst` with `j.fst`, `i.fst` with `j.snd`, `i.snd` with `j.fst` and
`i.snd` with `j.snd` that an atom forces between proper intervals. -/
def signature : AllenRelation → Ordering × Ordering × Ordering × Ordering
  | precedes     => (.lt, .lt, .lt, .lt)
  | meets        => (.lt, .lt, .eq, .lt)
  | overlaps     => (.lt, .lt, .gt, .lt)
  | finishedBy   => (.lt, .lt, .gt, .eq)
  | contains     => (.lt, .lt, .gt, .gt)
  | starts       => (.eq, .lt, .gt, .lt)
  | equal        => (.eq, .lt, .gt, .eq)
  | startedBy    => (.eq, .lt, .gt, .gt)
  | during       => (.gt, .lt, .gt, .lt)
  | finishes     => (.gt, .lt, .gt, .eq)
  | overlappedBy => (.gt, .lt, .gt, .gt)
  | metBy        => (.gt, .eq, .gt, .gt)
  | precededBy   => (.gt, .gt, .gt, .gt)

theorem signature_injective : Function.Injective signature := by decide

/-- Between proper intervals an atom holds exactly when the endpoint comparisons are its
signature. -/
theorem holds_iff_signature (r : AllenRelation) (hi : i.fst < i.snd) (hj : j.fst < j.snd) :
    r.holds i j ↔
      (compare i.fst j.fst, compare i.fst j.snd, compare i.snd j.fst, compare i.snd j.snd) =
        r.signature := by
  cases r <;> simp only [holds, signature, Prod.mk.injEq, compare_lt_iff_lt, compare_eq_iff_eq,
    compare_gt_iff_gt, iff_def, and_imp] <;> constructor <;> intros <;>
    (repeat' apply And.intro) <;> order

/-- Between proper intervals at most one atom holds. -/
theorem holds_unique (hi : i.fst < i.snd) (hj : j.fst < j.snd) {r s : AllenRelation}
    (hr : r.holds i j) (hs : s.holds i j) : r = s :=
  signature_injective <|
    ((holds_iff_signature r hi hj).1 hr).symm.trans ((holds_iff_signature s hi hj).1 hs)

end AllenRelation

/-! ### The atom holding between two intervals -/

namespace NonemptyInterval

open AllenRelation

variable {T : Type*} [LinearOrder T] (i j : NonemptyInterval T)

/-- The Allen atom holding between two intervals, read off their endpoint comparisons. -/
def allenRel : AllenRelation :=
  if i.snd < j.fst then .precedes
  else if i.snd = j.fst then .meets
  else if j.snd < i.fst then .precededBy
  else if i.fst = j.snd then .metBy
  else if i.fst < j.fst then
    if i.snd < j.snd then .overlaps else if i.snd = j.snd then .finishedBy else .contains
  else if i.fst = j.fst then
    if i.snd < j.snd then .starts else if i.snd = j.snd then .equal else .startedBy
  else if i.snd < j.snd then .during else if i.snd = j.snd then .finishes else .overlappedBy

/-- Some atom holds between any two intervals. -/
theorem allenRel_holds : (allenRel i j).holds i j := by
  unfold allenRel
  split_ifs <;> simp only [holds] <;> (repeat' apply And.intro) <;> order

variable {i j}

/-- Between proper intervals `allenRel` is the only atom that holds. -/
theorem holds_iff_allenRel_eq (hi : i.fst < i.snd) (hj : j.fst < j.snd) {r : AllenRelation} :
    r.holds i j ↔ allenRel i j = r :=
  ⟨fun h ↦ holds_unique hi hj (allenRel_holds i j) h, fun h ↦ h ▸ allenRel_holds i j⟩

theorem allenRel_swap (hi : i.fst < i.snd) (hj : j.fst < j.snd) :
    allenRel j i = (allenRel i j).inverse :=
  (holds_iff_allenRel_eq hj hi).1 ((inverse_holds _).2 (allenRel_holds i j))

end NonemptyInterval

/-! ### Sets of atoms

A general relation of Allen's algebra is a set of atoms, holding when one of its atoms does. -/

namespace AllenRelation

open Finset NonemptyInterval

variable {T : Type*} [LinearOrder T] {S S' : Finset AllenRelation} {i j : NonemptyInterval T}

/-- A set of atoms holds between two intervals when one of its atoms does. -/
def holdsIn (S : Finset AllenRelation) (i j : NonemptyInterval T) : Prop := ∃ r ∈ S, r.holds i j

instance (S : Finset AllenRelation) (i j : NonemptyInterval T) : Decidable (holdsIn S i j) :=
  inferInstanceAs (Decidable (∃ r ∈ S, r.holds i j))

@[simp] theorem holdsIn_empty : ¬ holdsIn ∅ i j := by simp [holdsIn]

@[simp] theorem holdsIn_singleton {r : AllenRelation} : holdsIn {r} i j ↔ r.holds i j := by
  simp [holdsIn]

@[simp] theorem holdsIn_insert {r : AllenRelation} :
    holdsIn (insert r S) i j ↔ r.holds i j ∨ holdsIn S i j := by
  simp [holdsIn, or_and_right, exists_or]

@[simp] theorem holdsIn_union : holdsIn (S ∪ S') i j ↔ holdsIn S i j ∨ holdsIn S' i j := by
  simp [holdsIn, or_and_right, exists_or]

@[simp] theorem holdsIn_univ : holdsIn univ i j := ⟨_, mem_univ _, allenRel_holds i j⟩

@[simp] theorem holdsIn_image_inverse : holdsIn (S.image inverse) j i ↔ holdsIn S i j := by
  simp [holdsIn]

theorem holdsIn_mono (h : S ⊆ S') : holdsIn S i j → holdsIn S' i j :=
  fun ⟨r, hr, h'⟩ ↦ ⟨r, h hr, h'⟩

/-- Between proper intervals a set of atoms holds exactly when it contains `allenRel`. -/
theorem holdsIn_iff_allenRel_mem (hi : i.fst < i.snd) (hj : j.fst < j.snd) :
    holdsIn S i j ↔ allenRel i j ∈ S :=
  ⟨fun ⟨_, hr, h⟩ ↦ (holds_iff_allenRel_eq hi hj).1 h ▸ hr, fun h ↦ ⟨_, h, allenRel_holds i j⟩⟩

end AllenRelation

/-! ### The interval vocabulary as sets of atoms

Each relation of `Core/Order/Interval.lean`, and mathlib's containment order, is a set of Allen
atoms; the three that are atoms themselves are so by definition. -/

namespace NonemptyInterval

open AllenRelation

variable {T : Type*} [LinearOrder T] (i j : NonemptyInterval T)

theorem precedes_iff_holds : i.precedes j ↔ AllenRelation.precedes.holds i j := Iff.rfl

theorem meets_iff_holds : i.meets j ↔ AllenRelation.meets.holds i j := Iff.rfl

theorem during_iff_holds : i.during j ↔ AllenRelation.during.holds i j := Iff.rfl

theorem isBefore_iff_holdsIn : i.isBefore j ↔ holdsIn {.precedes, .meets} i j := by
  simp [isBefore, holds, le_iff_lt_or_eq]

theorem isAfter_iff_holdsIn : i.isAfter j ↔ holdsIn {.precededBy, .metBy} i j := by
  simp [isAfter, holds, le_iff_lt_or_eq, eq_comm]

theorem le_iff_holdsIn : i ≤ j ↔ holdsIn {.starts, .equal, .finishes, .during} i j := by
  simp only [le_def, holdsIn_insert, holdsIn_singleton, holds]
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases h₁.lt_or_eq with h₁ | h₁ <;> rcases h₂.lt_or_eq with h₂ | h₂ <;> simp [*]
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> exact ⟨by order, by order⟩

theorem lt_iff_holdsIn : i < j ↔ holdsIn {.starts, .finishes, .during} i j := by
  simp only [lt_def, le_def, holdsIn_insert, holdsIn_singleton, holds]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    rcases h₁.lt_or_eq with h₁ | h₁ <;> rcases h₂.lt_or_eq with h₂ | h₂ <;> simp_all
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> exact ⟨⟨by order, by order⟩, by order⟩

theorem finalSubinterval_iff_holdsIn : i.finalSubinterval j ↔ holdsIn {.finishes, .equal} i j := by
  simp only [finalSubinterval, le_def, holdsIn_insert, holdsIn_singleton, holds]
  constructor
  · rintro ⟨⟨h₁, -⟩, h₂⟩
    rcases h₁.lt_or_eq with h₁ | h₁ <;> simp [*]
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> exact ⟨⟨by order, by order⟩, by order⟩

theorem overlaps_iff_holdsIn : i.overlaps j ↔ holdsIn {.precedes, .precededBy}ᶜ i j := by
  rw [overlaps_iff_not_precedes]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨allenRel i j, ?_, allenRel_holds i j⟩
    have h := allenRel_holds i j
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun e ↦ h₁ (by rwa [e] at h), fun e ↦ h₂ (by rwa [e] at h)⟩
  · rintro ⟨r, hr, h⟩
    have := i.fst_le_snd; have := j.fst_le_snd
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    revert h
    cases r <;> simp only [holds, precedes, not_lt, and_imp] <;> intros <;>
      first | exact absurd rfl hr.1 | exact absurd rfl hr.2 | exact ⟨by order, by order⟩

/-- Initial overlap is the union of the atoms placing `j.fst` inside `i`. -/
theorem initialOverlap_iff_holdsIn : i.initialOverlap j ↔
    holdsIn {.meets, .overlaps, .finishedBy, .contains, .starts, .equal, .startedBy} i j := by
  simp only [initialOverlap, overlaps, mem_def, holdsIn_insert, holdsIn_singleton, holds]
  have := i.fst_le_snd; have := j.fst_le_snd
  constructor
  · rintro ⟨-, h₁, h₂⟩
    rcases h₁.lt_or_eq with h₁ | h₁ <;> rcases h₂.lt_or_eq with h₂ | h₂ <;>
      rcases lt_trichotomy i.snd j.snd with h | h | h <;> simp_all
  · rintro (h | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;>
      exact ⟨⟨by order, by order⟩, by order, by order⟩

end NonemptyInterval
