module

public import Linglib.Data.Examples.Anderson2006b
public import Mathlib.Data.Finset.Insert
public import Mathlib.Order.Minimal

/-!
# Anderson (2006): Modern Grammars of Case: A Retrospective

In the localist case grammar of the book's sixth chapter, a semantic relation combines three case
features: the absolutive, which is semantically empty, the source and the locative. An ergative
is a source alone, an experiencer a locative source, and every combination occurs. An absolutive
with a source among its co-arguments is a goal, the absolutive the accusative signals. In a
language with subjects, an absolutive that is not a goal becomes a source by subject formation,
and the subject is chosen by a hierarchy that ranks a simple ergative over a combined one over
any absolutive. So every subject is a source, inherent or derived.

## Main statements

* `Relation.isSubjectOf_iff_isDerivedSourceOf`: an argument with no source of its own is the
  subject exactly when subject formation makes it a source.
* `Relation.IsSubjectOf.src_mem_or_isDerivedSourceOf`: every subject is a source, inherent or
  derived.
* `rows_subject`: the hierarchy selects the subject the book records for each of its examples,
  and only that argument.

## Implementation notes

* The comma of the hierarchy reads "combined with some other relation", so a simple ergative
  outranks the experiencer and the self-mover alike. The optional comma on the absolutive is left
  out: the *with*-phrase of *The tank flooded with sewage* is a circumstantial.
* Second-order features are not stored. Whether an absolutive is a goal or a derived source is
  read off its predication; the goal or source of a locative is left in the row comments.
* A subject is any argument of maximal rank, since the hierarchy leaves equatives open.

## References

* [anderson-2006b]
-/

@[expose] public section

namespace Anderson2006b

/-- The three first-order case features. -/
inductive Feature
  | abs
  | src
  | loc
  deriving DecidableEq

/-- A semantic relation is a combination of first-order case features. -/
abbrev Relation := Finset Feature

/-- A predication lists the relations its predicator's arguments bear. -/
abbrev Predication := List Relation

namespace Relation

variable {r : Relation} {p : Predication}

/-! ### Named relations -/

/-- The absolutive, the semantically empty relation. -/
abbrev absolutive : Relation := {.abs}

/-- The ergative, a source that is not locative. -/
abbrev ergative : Relation := {.src}

/-- The simple locative. -/
abbrev locative : Relation := {.loc}

/-- The experiencer, a locative source. -/
abbrev experiencer : Relation := {.src, .loc}

/-- The contactive, an absolutive locative. -/
abbrev contactive : Relation := {.abs, .loc}

/-- A relation is a patient when it combines the locative with the absolutive or the source. -/
def IsPatient (r : Relation) : Prop := .loc ∈ r ∧ (.abs ∈ r ∨ .src ∈ r)

instance : DecidablePred IsPatient := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem isPatient_experiencer : IsPatient experiencer := by decide

theorem isPatient_contactive : IsPatient contactive := by decide

/-! ### Goals and derived sources -/

/-- An absolutive with no source of its own is a goal of a predication when a co-argument bears a
source. -/
def IsGoalOf (r : Relation) (p : Predication) : Prop :=
  .abs ∈ r ∧ .src ∉ r ∧ ∃ s ∈ p, .src ∈ s

instance : Decidable (r.IsGoalOf p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Subject formation makes an absolutive a source when it bears none of its own and is not a
goal. -/
def IsDerivedSourceOf (r : Relation) (p : Predication) : Prop :=
  .abs ∈ r ∧ .src ∉ r ∧ ¬ r.IsGoalOf p

instance : Decidable (r.IsDerivedSourceOf p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem isDerivedSourceOf_iff :
    r.IsDerivedSourceOf p ↔ .abs ∈ r ∧ .src ∉ r ∧ ∀ s ∈ p, .src ∉ s := by
  simp +contextual [IsDerivedSourceOf, IsGoalOf]

/-! ### Subject selection -/

/-- The rank of a relation on the subject selection hierarchy. A simple ergative outranks a
combined one, which outranks any absolutive, and a relation with neither feature is off the
hierarchy. -/
def subjectRank (r : Relation) : ℕ :=
  if .src ∈ r then (if r = ergative then 3 else 2) else if .abs ∈ r then 1 else 0

theorem subjectRank_pos_iff : 0 < r.subjectRank ↔ .src ∈ r ∨ .abs ∈ r := by
  unfold subjectRank; split_ifs <;> simp_all

theorem two_le_subjectRank_iff : 2 ≤ r.subjectRank ↔ .src ∈ r := by
  unfold subjectRank; split_ifs <;> simp_all

theorem subjectRank_lt_ergative (h : r ≠ ergative) : r.subjectRank < ergative.subjectRank := by
  unfold subjectRank; split_ifs <;> simp_all

/-- A subject of a predication is an argument of maximal rank on the hierarchy. -/
def IsSubjectOf (r : Relation) (p : Predication) : Prop :=
  MaximalFor (fun s ↦ s ∈ p ∧ 0 < s.subjectRank) subjectRank r

theorem isSubjectOf_iff :
    r.IsSubjectOf p ↔ r ∈ p ∧ 0 < r.subjectRank ∧ ∀ s ∈ p, s.subjectRank ≤ r.subjectRank := by
  rw [IsSubjectOf, maximalFor_iff_forall_gt]
  grind

instance : Decidable (r.IsSubjectOf p) := decidable_of_iff' _ isSubjectOf_iff

/-- An argument with no source of its own is the subject exactly when subject formation makes it
a source. -/
theorem isSubjectOf_iff_isDerivedSourceOf (hr : r ∈ p) (hsrc : .src ∉ r) :
    r.IsSubjectOf p ↔ r.IsDerivedSourceOf p := by
  rw [isSubjectOf_iff, isDerivedSourceOf_iff]
  grind [subjectRank_pos_iff, two_le_subjectRank_iff]

/-- Every subject is a source that is not spatial, inherent or derived by subject formation. -/
theorem IsSubjectOf.src_mem_or_isDerivedSourceOf (h : r.IsSubjectOf p) :
    .src ∈ r ∨ r.IsDerivedSourceOf p :=
  or_iff_not_imp_left.2 fun hsrc ↦
    (isSubjectOf_iff_isDerivedSourceOf (isSubjectOf_iff.1 h).1 hsrc).1 h

/-- A subject is never a goal. -/
theorem IsSubjectOf.not_isGoalOf (h : r.IsSubjectOf p) : ¬ r.IsGoalOf p := fun hg ↦
  h.src_mem_or_isDerivedSourceOf.elim hg.2.1 fun hd ↦ hd.2.2 hg

/-! ### The book's examples -/

/-- The labels the example rows give the relations. -/
def labels : List (String × Relation) :=
  [("abs", absolutive), ("erg", ergative), ("loc", locative), ("abs,erg", {.abs, .src}),
    ("erg,loc", experiencer), ("abs,loc", contactive), ("abs,erg,loc", {.abs, .src, .loc})]

end Relation

/-- The predication a row records, if every argument label names a relation. Adjuncts are not
arguments. -/
def Predication.ofRow? (e : Datum) : Option Predication :=
  (e.features "arg").mapM (List.lookup · Relation.labels)

/-- The hierarchy selects the subject the book records for each of its examples, and only that
argument. -/
theorem rows_subject :
    ∀ e ∈ Examples.all, ∃ p ∈ Predication.ofRow? e, ∃ r ∈ e.parse? "subject" Relation.labels,
      r.IsSubjectOf p ∧ ∀ s ∈ p, s.IsSubjectOf p → s = r := by
  decide +kernel

/-- The subject of *Bill fell to the ground* is a source only by subject formation. -/
theorem fell_subject_derived :
    ∃ p ∈ Predication.ofRow? Examples.ex_39b, ∃ r ∈ p, r.IsSubjectOf p ∧ r.IsDerivedSourceOf p := by
  decide +kernel

/-- The object of *Bill read the book* is a goal, so the accusative signals it. -/
theorem read_object_goal :
    ∃ p ∈ Predication.ofRow? Examples.ex_39a, ∃ r ∈ p, r.IsGoalOf p := by
  decide +kernel

/-- The subject of *Phil suffered (from asthma)* is at once an experiencer and a contactive, so
all three first-order features combine on one argument. -/
theorem suffered_subject :
    ∃ p ∈ Predication.ofRow? Examples.ex_34, ∃ r ∈ p, r.IsSubjectOf p ∧
      Relation.experiencer ⊆ r ∧ Relation.contactive ⊆ r := by
  decide +kernel

end Anderson2006b
