import Linglib.Semantics.ArgumentStructure.Linking
import Linglib.Data.Examples.Anderson2006b
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.DeriveFintype

/-!
# Anderson 2006: localist case grammar

Every semantic relation an argument bears is a bundle of the three first-order case features of
chapter 6 — absolutive, the semantically empty relation; source, whose non-locational form is the
ergative; and locative, which may carry source or goal as a second-order feature — and all eight
combinations occur: the Experiencer is a locative source, the contactive patient an absolutive
locative, and *suffer*'s subject bears all three. Subject selection ranks ergative above ergative
absolutive above absolutive, so only a non-spatial source or an absolutive can be subject, and
subject formation then marks a selected absolutive as ergative — the neutralization behind
subjecthood.

## Main definitions

* `Relation`: a bundle of first-order `Feature`s (the second-order {goal} and {src} are not
  represented); `subjectRank` the hierarchy (38)′, `subject` the selected argument of a
  `Predication`, `subjectFormation` rule (40).
* `andersonLinking`: the hierarchy as a `LinkingTheory`, via `Relation.toRole`.

## References

* [anderson-2006b]
-/

namespace Anderson2006b

open ArgumentStructure Data.Examples

/-! ### Case features and relations -/

/-- The three first-order case features (11). -/
inductive Feature
  | abs
  | src
  | loc
  deriving DecidableEq, Fintype

/-- A semantic relation is a bundle of first-order features; the eight combinations all
occur (§6.2). -/
abbrev Relation := Finset Feature

namespace Relation

/-- The semantically empty relation. -/
abbrev absolutive : Relation := {.abs}

/-- Non-locational source. -/
abbrev ergative : Relation := {.src}

abbrev locative : Relation := {.loc}

/-- The self-mover of (39c). -/
abbrev ergAbs : Relation := {.abs, .src}

/-- The Experiencer, a locative source (39h). -/
abbrev experiencer : Relation := {.src, .loc}

/-- The contactive patient (22). -/
abbrev contactive : Relation := {.abs, .loc}

/-- The hom onto the project's role labels: a locative source is an experiencer, any other
source an agent, a sourceless absolutive a patient. -/
def toRole (r : Relation) : Option ThetaRole :=
  if .src ∈ r then (if .loc ∈ r then some .experiencer else some .agent)
  else if .abs ∈ r then some .patient else none

end Relation

/-! ### Subject selection and subject formation -/

/-- The subject selection hierarchy (38)′: ergative > ergative absolutive > absolutive; a
purely spatial argument is ineligible, and the locative feature is irrelevant. -/
def subjectRank (r : Relation) : ℕ :=
  if .src ∈ r then (if .abs ∈ r then 2 else 3) else if .abs ∈ r then 1 else 0

theorem subjectRank_ergative_gt_ergAbs : subjectRank .ergAbs < subjectRank .ergative := by
  decide

theorem subjectRank_ergAbs_gt_absolutive :
    subjectRank .absolutive < subjectRank .ergAbs := by decide

theorem subjectRank_insert_loc (r : Relation) : subjectRank (insert .loc r) = subjectRank r := by
  simp [subjectRank]

/-- The Experiencer and the ergative differ in content but not in rank. -/
theorem experiencer_ne_ergative :
    Relation.experiencer ≠ Relation.ergative ∧
      subjectRank .experiencer = subjectRank .ergative := by decide

/-- The relations of a predication's arguments. -/
abbrev Predication := List Relation

/-- The selected subject: the highest-ranked argument. -/
def subject (p : Predication) : Option Relation := p.argmax subjectRank

/-- Subject formation (40): the selected argument acquires the ergative feature. -/
def subjectFormation (r : Relation) : Relation := insert .src r

/-- Subject marks a non-spatial source, inherent or derived by (40). -/
theorem src_mem_subjectFormation (r : Relation) : .src ∈ subjectFormation r :=
  Finset.mem_insert_self _ _

/-- An inherent source is untouched by (40): the neutralization leaves the residue the
ergative subjects have in common. -/
theorem subjectFormation_eq_self {r : Relation} (h : .src ∈ r) : subjectFormation r = r :=
  Finset.insert_eq_of_mem h

/-! ### The derivations of (39) -/

def read : Predication := [.ergative, .absolutive]

def fell : Predication := [.absolutive, .locative]

def flew : Predication := [.ergAbs, .locative]

def knew : Predication := [.experiencer, .absolutive]

def suffered : Predication := [{.abs, .src, .loc}, .locative]

theorem subjects_39 :
    subject read = some .ergative ∧ subject fell = some .absolutive ∧
      subject flew = some .ergAbs ∧ subject knew = some .experiencer ∧
      subject suffered = some {.abs, .src, .loc} := by decide

/-- (39b) is the odd one out: its subject is not inherently ergative and is assimilated to the
others only by (40). -/
theorem fell_subject_not_src :
    ∀ r ∈ (subject fell).toList, .src ∉ r ∧ .src ∈ subjectFormation r := by decide

/-! ### The book's examples -/

/-- The relation strings of the example rows. -/
def Relation.ofString? : String → Option Relation
  | "abs" => some .absolutive
  | "erg" => some .ergative
  | "loc" => some .locative
  | "abs,erg" => some .ergAbs
  | "erg,loc" => some .experiencer
  | "abs,loc" => some .contactive
  | "abs,erg,loc" => some {.abs, .src, .loc}
  | _ => none

/-- The predication a row records. -/
def predicationOfRow (r : LinguisticExample) : Predication :=
  r.paperFeatures.filterMap fun kv => if kv.1 = "arg" then Relation.ofString? kv.2 else none

/-- Across the book's examples, the subject is the argument the hierarchy (38)′ selects — except
(4.8b), whose complex absolutive outranks the simple one only under (38)'s optional comma. -/
theorem rows_subject_selection :
    ∀ r ∈ Examples.all, r.id ≠ "andersonjm2006_4_8b" →
      subject (predicationOfRow r) = (r.feature? "subject").bind Relation.ofString? := by
  decide +kernel

/-! ### As a linking theory -/

open Linking in
/-- Anderson's subject selection as a linking theory over predications: the subject's role is
the label of the selected relation; the theory is silent on other functions. -/
def andersonLinking : LinkingTheory Predication Unit where
  compatible _ := [()]
  predict p _ pos := match pos with
    | .subject => (subject p).bind Relation.toRole
    | _ => none

theorem andersonLinking_subjects :
    andersonLinking.predict read () .subject = some .agent ∧
      andersonLinking.predict fell () .subject = some .patient ∧
      andersonLinking.predict knew () .subject = some .experiencer := by decide

end Anderson2006b
