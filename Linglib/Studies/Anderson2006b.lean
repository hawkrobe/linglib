module

public import Linglib.Data.Examples.Anderson2006b
public import Mathlib.Data.Finset.Insert

/-!
# Anderson (2006): Modern grammars of case, chapter 6

This file formalizes the localist case grammar of chapter 6 of [anderson-2006b]. A semantic
relation is a bundle of the three first-order case features of (11), absolutive, source and
locative, and every bundle occurs: the ergative is a non-locational source, the experiencer a
locative source (39h), the contactive patient an absolutive locative (22), and the subject of
*suffer* bears all three (34). Goal specification (12b) marks an absolutive co-dependent with an
ergative as a goal, the subject selection hierarchy (38)′ ranks a simple ergative above a
combined one above any absolutive, and subject formation (40) adds the ergative feature to the
selected argument, so that a subject is always a non-spatial source, inherent or derived.

We prove that a subject is never a goal absolutive, so (40) applies exactly where (12b) fails,
and that the hierarchy selects the recorded subject of each of the book's examples.

## Implementation notes

* The comma of (38) is read as (17) glosses it, "combined with some other relation", so a simple
  ergative outranks the experiencer and the self-mover alike, as `A > D` in (4.17)′. The
  hierarchy is (38)′, without the optional comma: the *with*-phrase of (4.8b) is a
  circumstantial outside subject selection, as the chapter's own analysis has it.
* Second-order features are not stored. The goal of an absolutive (12b) is derived from its
  predication; the goal or source of a locative (12a) is left in the row comments.
* A subject is any rank-maximal eligible argument: the hierarchy leaves equatives
  indeterminate (4.13).

## References

* [anderson-2006b]
-/

@[expose] public section

namespace Anderson2006b

open Data.Examples

/-- The three first-order case features (11). -/
inductive Feature
  | abs
  | src
  | loc
  deriving DecidableEq

/-- A semantic relation is a bundle of first-order case features. -/
abbrev Relation := Finset Feature

/-- A predication is the list of relations borne by a predicator's arguments. -/
abbrev Predication := List Relation

namespace Relation

variable {r s : Relation} {p : Predication}

/-! ### Named relations -/

/-- The absolutive is the semantically empty relation. -/
abbrev absolutive : Relation := {.abs}

/-- The ergative is a non-locational source. -/
abbrev ergative : Relation := {.src}

/-- The simple locative. -/
abbrev locative : Relation := {.loc}

/-- The experiencer is a locative source (39h). -/
abbrev experiencer : Relation := {.src, .loc}

/-- The contactive is an absolutive locative (22). -/
abbrev contactive : Relation := {.abs, .loc}

/-- A relation is a patient when it combines the locative with a non-locative feature (33). -/
def IsPatient (r : Relation) : Prop := .loc ∈ r ∧ (.abs ∈ r ∨ .src ∈ r)

instance : DecidablePred IsPatient := λ _ => by unfold IsPatient; infer_instance

theorem isPatient_experiencer : IsPatient experiencer := by decide

theorem isPatient_contactive : IsPatient contactive := by decide

/-! ### Subject selection -/

/-- The rank of a relation on the subject selection hierarchy (38)′. A simple ergative outranks
a combined one, which outranks any absolutive, and a purely spatial argument is ineligible. -/
def subjectRank (r : Relation) : ℕ :=
  if .src ∈ r then (if r = ergative then 3 else 2) else if .abs ∈ r then 1 else 0

theorem subjectRank_pos_iff : 0 < r.subjectRank ↔ .src ∈ r ∨ .abs ∈ r := by
  unfold subjectRank; split_ifs <;> simp_all

theorem two_le_subjectRank_iff : 2 ≤ r.subjectRank ↔ .src ∈ r := by
  unfold subjectRank; split_ifs <;> simp_all

theorem subjectRank_lt_ergative (h : r ≠ ergative) : r.subjectRank < ergative.subjectRank := by
  unfold subjectRank; split_ifs <;> simp_all

/-- A relation is a subject of a predication when it is an eligible argument no argument
outranks; the hierarchy leaves ties indeterminate (4.13). -/
def IsSubjectOf (r : Relation) (p : Predication) : Prop :=
  r ∈ p ∧ 0 < r.subjectRank ∧ ∀ s ∈ p, s.subjectRank ≤ r.subjectRank

instance : Decidable (r.IsSubjectOf p) := by unfold IsSubjectOf; infer_instance

/-- An absolutive is a goal of a predication when a co-argument is an ergative (12b); the
accusative signals such an argument (13). -/
def IsGoalOf (r : Relation) (p : Predication) : Prop :=
  .abs ∈ r ∧ .src ∉ r ∧ ∃ s ∈ p, .src ∈ s

instance : Decidable (r.IsGoalOf p) := by unfold IsGoalOf; infer_instance

/-- A subject without an inherent source has no ergative co-argument. -/
theorem IsSubjectOf.src_notMem_of_src_notMem (h : r.IsSubjectOf p) (hr : .src ∉ r) :
    ∀ s ∈ p, .src ∉ s := λ s hs hsrc => by
    have := h.2.2 s hs
    have := two_le_subjectRank_iff.2 hsrc
    have := mt two_le_subjectRank_iff.1 hr
    omega

/-- A subject is never a goal absolutive, so subject formation (40) applies exactly where goal
specification (12b) fails. -/
theorem IsSubjectOf.not_isGoalOf (h : r.IsSubjectOf p) : ¬ r.IsGoalOf p :=
  λ ⟨_, hr, s, hs, hsrc⟩ => h.src_notMem_of_src_notMem hr s hs hsrc

/-! ### Subject formation -/

/-- Subject formation (40) marks the selected argument as a source. -/
def subjectFormation (r : Relation) : Relation := insert .src r

theorem src_mem_subjectFormation (r : Relation) : .src ∈ r.subjectFormation :=
  Finset.mem_insert_self _ _

/-- An inherent source is untouched by (40), which leaves as residue what the ergative
subjects have in common. -/
theorem subjectFormation_eq_self (h : .src ∈ r) : r.subjectFormation = r :=
  Finset.insert_eq_of_mem h

/-! ### The book's examples -/

/-- The relation strings of the example rows. -/
def ofString : List (String × Relation) :=
  [("abs", absolutive), ("erg", ergative), ("loc", locative), ("abs,erg", {.abs, .src}),
    ("erg,loc", experiencer), ("abs,loc", contactive), ("abs,erg,loc", {.abs, .src, .loc})]

end Relation

/-- The predication a row records, adjuncts excluded. -/
def Predication.ofRow (e : LinguisticExample) : Predication :=
  e.paperFeatures.filterMap λ kv =>
    if kv.1 = "arg" then List.lookup kv.2 Relation.ofString else none

/-- The hierarchy selects the recorded subject of each of the book's examples, and no other
argument ties with it. -/
theorem rows_subject :
    ∀ e ∈ Examples.all, ∃ r ∈ Predication.ofRow e,
      e.parse? "subject" Relation.ofString = some r ∧ r.IsSubjectOf (Predication.ofRow e) ∧
        ∀ s ∈ Predication.ofRow e, s ≠ r → s.subjectRank < r.subjectRank := by
  decide +kernel

/-- The subject of (39b) is not inherently ergative; it is assimilated to the others only by
(40). -/
theorem fell_subject_derived :
    ∃ r ∈ Predication.ofRow Examples.ex_39b,
      r.IsSubjectOf (Predication.ofRow Examples.ex_39b) ∧ .src ∉ r := by
  decide +kernel

/-- The subject of (34) is at once an experiencer and a contactive, so all three first-order
features combine on one argument. -/
theorem suffered_subject :
    ∃ r ∈ Predication.ofRow Examples.ex_34, r.IsSubjectOf (Predication.ofRow Examples.ex_34) ∧
      Relation.experiencer ⊆ r ∧ Relation.contactive ⊆ r := by
  decide +kernel

end Anderson2006b
