module

public import Linglib.Core.Order.Compare
public import Linglib.Core.Order.Interval
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Sort
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

Composing two atoms gives the set of atoms that can hold between `i` and `k` when the first
holds between `i` and `j` and the second between `j` and `k`. Allen tabulates it as the
transitivity table of the algebra; `comp` is that table, and `holdsIn_comp` proves it sound.
On point intervals the atoms collapse to `precedes`, `equal` and `precededBy`, and the table to
the composition of comparisons `Ordering.comp` of `Core/Order/Compare.lean`
(`mem_comp_ofOrdering`).

## Main definitions

* `AllenRelation`: the thirteen atoms, with `inverse` swapping the two intervals.
* `AllenRelation.holds`: the endpoint inequalities defining each atom.
* `NonemptyInterval.allenRel`: the atom holding between two intervals.
* `AllenRelation.holdsIn`: a set of atoms holds when one of its members does.
* `AllenRelation.comp`: Allen's transitivity table.

## Main results

* `AllenRelation.holds_iff_signature`: between proper intervals an atom holds exactly when the
  four endpoint comparisons are the atom's signature, so at most one atom holds (`holds_unique`).
* `NonemptyInterval.allenRel_holds`, `holds_iff_allenRel_eq`: `allenRel` is an atom that holds,
  and between proper intervals the only one.
* `NonemptyInterval.le_iff_holdsIn`, `overlaps_iff_holdsIn`, and the other bridges: each interval
  relation as a set of atoms.
* `AllenRelation.holdsIn_comp`: between proper intervals the atom holding between `i` and `k`
  lies in the composition of the atoms holding between `i` and `j` and between `j` and `k`.

## Implementation notes

Allen assumes that every interval is proper. Mathlib's `NonemptyInterval` admits points, between
which uniqueness fails: at a single point `meets`, `metBy` and `equal` all hold. Existence and the
bridges to the interval vocabulary hold between all intervals, and only the uniqueness results
carry the properness hypotheses. The transitivity table is transcribed from Allen's figure, whose
cells `dur` and `con` abbreviate `{during, starts, finishes}` and
`{contains, startedBy, finishedBy}`; the transcription was checked against an exhaustive
enumeration of the order types of six endpoints, and the soundness proof checks every cell
again. Properness matters for composition too: with `j` a point, `meets` followed by `meets` is
`meets`, not `precedes`.

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
atoms; the two that are atoms themselves are so by definition. -/

namespace NonemptyInterval

open AllenRelation

variable {T : Type*} [LinearOrder T] (i j : NonemptyInterval T)

theorem precedes_iff_holds : i.precedes j ↔ AllenRelation.precedes.holds i j := Iff.rfl

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

/-! ### Composition

Composing two atoms gives the atoms that can hold between the outer intervals of a chain of
three proper intervals; Allen tabulates it as the transitivity table of the algebra. -/

namespace AllenRelation

open Finset NonemptyInterval

variable {T : Type*} [LinearOrder T] {i j k : NonemptyInterval T}

/-- Allen's transitivity table, the atoms that can hold between `i` and `k` when `r` holds
between `i` and `j` and `s` between `j` and `k`, all three intervals proper. -/
def comp : AllenRelation → AllenRelation → Finset AllenRelation
  | equal, s => {s}
  | r, equal => {r}
  | precedes,     precedes     => {.precedes}
  | precedes,     precededBy   => univ
  | precedes,     during       => {.precedes, .meets, .overlaps, .starts, .during}
  | precedes,     contains     => {.precedes}
  | precedes,     overlaps     => {.precedes}
  | precedes,     overlappedBy => {.precedes, .meets, .overlaps, .starts, .during}
  | precedes,     meets        => {.precedes}
  | precedes,     metBy        => {.precedes, .meets, .overlaps, .starts, .during}
  | precedes,     starts       => {.precedes}
  | precedes,     startedBy    => {.precedes}
  | precedes,     finishes     => {.precedes, .meets, .overlaps, .starts, .during}
  | precedes,     finishedBy   => {.precedes}
  | precededBy,   precedes     => univ
  | precededBy,   precededBy   => {.precededBy}
  | precededBy,   during       => {.during, .finishes, .overlappedBy, .metBy, .precededBy}
  | precededBy,   contains     => {.precededBy}
  | precededBy,   overlaps     => {.during, .finishes, .overlappedBy, .metBy, .precededBy}
  | precededBy,   overlappedBy => {.precededBy}
  | precededBy,   meets        => {.during, .finishes, .overlappedBy, .metBy, .precededBy}
  | precededBy,   metBy        => {.precededBy}
  | precededBy,   starts       => {.during, .finishes, .overlappedBy, .metBy, .precededBy}
  | precededBy,   startedBy    => {.precededBy}
  | precededBy,   finishes     => {.precededBy}
  | precededBy,   finishedBy   => {.precededBy}
  | during,       precedes     => {.precedes}
  | during,       precededBy   => {.precededBy}
  | during,       during       => {.during}
  | during,       contains     => univ
  | during,       overlaps     => {.precedes, .meets, .overlaps, .starts, .during}
  | during,       overlappedBy => {.during, .finishes, .overlappedBy, .metBy, .precededBy}
  | during,       meets        => {.precedes}
  | during,       metBy        => {.precededBy}
  | during,       starts       => {.during}
  | during,       startedBy    => {.during, .finishes, .overlappedBy, .metBy, .precededBy}
  | during,       finishes     => {.during}
  | during,       finishedBy   => {.precedes, .meets, .overlaps, .starts, .during}
  | contains,     precedes     => {.precedes, .meets, .overlaps, .finishedBy, .contains}
  | contains,     precededBy   => {.contains, .startedBy, .overlappedBy, .metBy, .precededBy}
  | contains,     during       =>
    {.overlaps, .finishedBy, .contains, .starts, .equal, .startedBy, .during, .finishes,
     .overlappedBy}
  | contains,     contains     => {.contains}
  | contains,     overlaps     => {.overlaps, .finishedBy, .contains}
  | contains,     overlappedBy => {.contains, .startedBy, .overlappedBy}
  | contains,     meets        => {.overlaps, .finishedBy, .contains}
  | contains,     metBy        => {.contains, .startedBy, .overlappedBy}
  | contains,     starts       => {.overlaps, .finishedBy, .contains}
  | contains,     startedBy    => {.contains}
  | contains,     finishes     => {.contains, .startedBy, .overlappedBy}
  | contains,     finishedBy   => {.contains}
  | overlaps,     precedes     => {.precedes}
  | overlaps,     precededBy   => {.contains, .startedBy, .overlappedBy, .metBy, .precededBy}
  | overlaps,     during       => {.overlaps, .starts, .during}
  | overlaps,     contains     => {.precedes, .meets, .overlaps, .finishedBy, .contains}
  | overlaps,     overlaps     => {.precedes, .meets, .overlaps}
  | overlaps,     overlappedBy =>
    {.overlaps, .finishedBy, .contains, .starts, .equal, .startedBy, .during, .finishes,
     .overlappedBy}
  | overlaps,     meets        => {.precedes}
  | overlaps,     metBy        => {.contains, .startedBy, .overlappedBy}
  | overlaps,     starts       => {.overlaps}
  | overlaps,     startedBy    => {.overlaps, .finishedBy, .contains}
  | overlaps,     finishes     => {.overlaps, .starts, .during}
  | overlaps,     finishedBy   => {.precedes, .meets, .overlaps}
  | overlappedBy, precedes     => {.precedes, .meets, .overlaps, .finishedBy, .contains}
  | overlappedBy, precededBy   => {.precededBy}
  | overlappedBy, during       => {.during, .finishes, .overlappedBy}
  | overlappedBy, contains     => {.contains, .startedBy, .overlappedBy, .metBy, .precededBy}
  | overlappedBy, overlaps     =>
    {.overlaps, .finishedBy, .contains, .starts, .equal, .startedBy, .during, .finishes,
     .overlappedBy}
  | overlappedBy, overlappedBy => {.overlappedBy, .metBy, .precededBy}
  | overlappedBy, meets        => {.overlaps, .finishedBy, .contains}
  | overlappedBy, metBy        => {.precededBy}
  | overlappedBy, starts       => {.during, .finishes, .overlappedBy}
  | overlappedBy, startedBy    => {.overlappedBy, .metBy, .precededBy}
  | overlappedBy, finishes     => {.overlappedBy}
  | overlappedBy, finishedBy   => {.contains, .startedBy, .overlappedBy}
  | meets,        precedes     => {.precedes}
  | meets,        precededBy   => {.contains, .startedBy, .overlappedBy, .metBy, .precededBy}
  | meets,        during       => {.overlaps, .starts, .during}
  | meets,        contains     => {.precedes}
  | meets,        overlaps     => {.precedes}
  | meets,        overlappedBy => {.overlaps, .starts, .during}
  | meets,        meets        => {.precedes}
  | meets,        metBy        => {.finishedBy, .equal, .finishes}
  | meets,        starts       => {.meets}
  | meets,        startedBy    => {.meets}
  | meets,        finishes     => {.overlaps, .starts, .during}
  | meets,        finishedBy   => {.precedes}
  | metBy,        precedes     => {.precedes, .meets, .overlaps, .finishedBy, .contains}
  | metBy,        precededBy   => {.precededBy}
  | metBy,        during       => {.during, .finishes, .overlappedBy}
  | metBy,        contains     => {.precededBy}
  | metBy,        overlaps     => {.during, .finishes, .overlappedBy}
  | metBy,        overlappedBy => {.precededBy}
  | metBy,        meets        => {.starts, .equal, .startedBy}
  | metBy,        metBy        => {.precededBy}
  | metBy,        starts       => {.during, .finishes, .overlappedBy}
  | metBy,        startedBy    => {.precededBy}
  | metBy,        finishes     => {.metBy}
  | metBy,        finishedBy   => {.metBy}
  | starts,       precedes     => {.precedes}
  | starts,       precededBy   => {.precededBy}
  | starts,       during       => {.during}
  | starts,       contains     => {.precedes, .meets, .overlaps, .finishedBy, .contains}
  | starts,       overlaps     => {.precedes, .meets, .overlaps}
  | starts,       overlappedBy => {.during, .finishes, .overlappedBy}
  | starts,       meets        => {.precedes}
  | starts,       metBy        => {.metBy}
  | starts,       starts       => {.starts}
  | starts,       startedBy    => {.starts, .equal, .startedBy}
  | starts,       finishes     => {.during}
  | starts,       finishedBy   => {.precedes, .meets, .overlaps}
  | startedBy,    precedes     => {.precedes, .meets, .overlaps, .finishedBy, .contains}
  | startedBy,    precededBy   => {.precededBy}
  | startedBy,    during       => {.during, .finishes, .overlappedBy}
  | startedBy,    contains     => {.contains}
  | startedBy,    overlaps     => {.overlaps, .finishedBy, .contains}
  | startedBy,    overlappedBy => {.overlappedBy}
  | startedBy,    meets        => {.overlaps, .finishedBy, .contains}
  | startedBy,    metBy        => {.metBy}
  | startedBy,    starts       => {.starts, .equal, .startedBy}
  | startedBy,    startedBy    => {.startedBy}
  | startedBy,    finishes     => {.overlappedBy}
  | startedBy,    finishedBy   => {.contains}
  | finishes,     precedes     => {.precedes}
  | finishes,     precededBy   => {.precededBy}
  | finishes,     during       => {.during}
  | finishes,     contains     => {.contains, .startedBy, .overlappedBy, .metBy, .precededBy}
  | finishes,     overlaps     => {.overlaps, .starts, .during}
  | finishes,     overlappedBy => {.overlappedBy, .metBy, .precededBy}
  | finishes,     meets        => {.meets}
  | finishes,     metBy        => {.precededBy}
  | finishes,     starts       => {.during}
  | finishes,     startedBy    => {.overlappedBy, .metBy, .precededBy}
  | finishes,     finishes     => {.finishes}
  | finishes,     finishedBy   => {.finishedBy, .equal, .finishes}
  | finishedBy,   precedes     => {.precedes}
  | finishedBy,   precededBy   => {.contains, .startedBy, .overlappedBy, .metBy, .precededBy}
  | finishedBy,   during       => {.overlaps, .starts, .during}
  | finishedBy,   contains     => {.contains}
  | finishedBy,   overlaps     => {.overlaps}
  | finishedBy,   overlappedBy => {.contains, .startedBy, .overlappedBy}
  | finishedBy,   meets        => {.meets}
  | finishedBy,   metBy        => {.contains, .startedBy, .overlappedBy}
  | finishedBy,   starts       => {.overlaps}
  | finishedBy,   startedBy    => {.contains}
  | finishedBy,   finishes     => {.finishedBy, .equal, .finishes}
  | finishedBy,   finishedBy   => {.finishedBy}

@[simp] theorem equal_comp (s : AllenRelation) : equal.comp s = {s} := rfl

@[simp] theorem comp_equal (r : AllenRelation) : r.comp equal = {r} := by cases r <;> rfl

/-- Inverting both atoms inverts the composition. -/
theorem image_inverse_comp (r s : AllenRelation) :
    (r.comp s).image inverse = s.inverse.comp r.inverse := by
  revert r s; decide

/-- The atom a comparison of points denotes. -/
def ofOrdering : Ordering → AllenRelation
  | .lt => precedes
  | .eq => equal
  | .gt => precededBy

theorem ofOrdering_injective : Function.Injective ofOrdering := by decide

theorem ofOrdering_compare_holds (a b : T) :
    (ofOrdering (compare a b)).holds (pure a) (pure b) := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [compare_lt_iff_lt.2 h]; exact h
  · rw [compare_eq_iff_eq.2 rfl]; exact ⟨rfl, rfl⟩
  · rw [compare_gt_iff_gt.2 h]; exact h

/-- On the atoms of point intervals the table is the composition of comparisons. -/
theorem mem_comp_ofOrdering (o o₁ o₂ : Ordering) :
    ofOrdering o ∈ (ofOrdering o₁).comp (ofOrdering o₂) ↔ o ∈ o₁.comp o₂ := by
  revert o o₁ o₂; decide














/-- `NonemptyInterval.map` along an order embedding preserves and reflects every atom. -/
@[simp] theorem holds_map {U : Type*} [LinearOrder U] (f : T ↪o U) (r : AllenRelation)
    (i j : NonemptyInterval T) :
    r.holds (i.map f.toOrderHom) (j.map f.toOrderHom) ↔ r.holds i j := by
  cases r <;> simp [holds, NonemptyInterval.map, f.lt_iff_lt, f.injective.eq_iff]

/-- `allenRel` is invariant under an order embedding. -/
@[simp] theorem _root_.NonemptyInterval.allenRel_map {U : Type*} [LinearOrder U] (f : T ↪o U)
    (i j : NonemptyInterval T) :
    allenRel (i.map f.toOrderHom) (j.map f.toOrderHom) = allenRel i j := by
  simp [allenRel, NonemptyInterval.map, f.lt_iff_lt, f.injective.eq_iff]

/-- The nonempty interval with the given proper endpoints. -/
private def mk (a b : Fin 6) (h : a < b) : NonemptyInterval (Fin 6) := ⟨(a, b), h.le⟩

/-- Soundness of the table over the six endpoints of three proper intervals, decided by the
kernel over `Fin 6`. -/
private theorem comp_aux : ∀ a b c d e g : Fin 6, ∀ hab : a < b, ∀ hcd : c < d, ∀ heg : e < g,
    allenRel (mk a b hab) (mk e g heg) ∈
      (allenRel (mk a b hab) (mk c d hcd)).comp (allenRel (mk c d hcd) (mk e g heg)) := by
  decide +kernel

/-- **Soundness of the table.** Between proper intervals, an atom holding between `i` and `j`
and one holding between `j` and `k` compose to a set containing the atom holding between `i`
and `k`. The six endpoints are ranked into `Fin 6`, where `comp_aux` decides the claim, and
`allenRel_map` carries it back. -/
theorem holdsIn_comp (hi : i.fst < i.snd) (hj : j.fst < j.snd) (hk : k.fst < k.snd)
    {r s : AllenRelation} (hr : r.holds i j) (hs : s.holds j k) : holdsIn (r.comp s) i k := by
  let S : Finset T := {i.fst, i.snd, j.fst, j.snd, k.fst, k.snd}
  let φ : S ↪o Fin 6 :=
    (S.orderIsoOfFin rfl).symm.toOrderEmbedding.trans (Fin.castLEOrderEmb Finset.card_le_six)
  let ι : S ↪o T := OrderEmbedding.subtype _
  let lift (a : NonemptyInterval T) (ha : a.fst ∈ S) (hb : a.snd ∈ S) : NonemptyInterval S :=
    ⟨(⟨a.fst, ha⟩, ⟨a.snd, hb⟩), a.fst_le_snd⟩
  have hlt (a : NonemptyInterval S) (h : (a.fst : T) < a.snd) :
      (a.map φ.toOrderHom).fst < (a.map φ.toOrderHom).snd := φ.lt_iff_lt.2 h
  have e (a b : NonemptyInterval S) :
      allenRel (a.map φ.toOrderHom) (b.map φ.toOrderHom) =
        allenRel (a.map ι.toOrderHom) (b.map ι.toOrderHom) :=
    (allenRel_map φ a b).trans (allenRel_map ι a b).symm
  set i₀ := lift i (by simp [S]) (by simp [S])
  set j₀ := lift j (by simp [S]) (by simp [S])
  set k₀ := lift k (by simp [S]) (by simp [S])
  have h : allenRel (i₀.map φ.toOrderHom) (k₀.map φ.toOrderHom) ∈
      (allenRel (i₀.map φ.toOrderHom) (j₀.map φ.toOrderHom)).comp
        (allenRel (j₀.map φ.toOrderHom) (k₀.map φ.toOrderHom)) :=
    comp_aux _ _ _ _ _ _ (hlt i₀ hi) (hlt j₀ hj) (hlt k₀ hk)
  rw [e, e, e] at h
  change allenRel i k ∈ (allenRel i j).comp (allenRel j k) at h
  rw [(holds_iff_allenRel_eq hi hj).1 hr, (holds_iff_allenRel_eq hj hk).1 hs] at h
  exact ⟨_, h, allenRel_holds i k⟩

end AllenRelation
