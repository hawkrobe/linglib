module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.UD.Features

/-!
# Clause chaining

A clause chain is a sequence of medial clauses, dependent and morphologically reduced, closed
by one final clause that supplies tense, mood and often agreement for the whole chain; it is
the prototypical cosubordinate combination of clauses, dependent but not embedded
([foley-r-d-van-valin-1984]; [longacre-2007]). This file provides the vocabulary in which a
language's inventory of medial forms is described and the notions a typology of chaining reads
off it ([sarvasy-aikhenvald-2025]; [de-vries-2025]). A fragment's carrier of medial forms is
an instance of `MedialForm`, which records for each form the switch-reference value it marks,
the interclausal relations it encodes and whether it indexes the subject of its clause; the
switch-reference and agreement properties of the language are definitions over the instance.
How far medial verbs retain an inflectional category is a `CategoryRetention`, and a language's
profile over the five categories is a point of the product order `MedialMorphProfile`, whose
top is the profile of a finite verb.

## Main definitions

* `CategoryRetention` — the scale `absent < restricted < full` on which a medial verb retains
  a category, a bounded linear order; `CategoryRetention.ofPred` reads a category's retention
  off which of a language's medial forms admit it, fully when all do, restrictedly when some
  do, not at all when none does
* `InflectionalCategory`, `MedialMorphProfile` — the five categories and a profile over them,
  ordered pointwise; `MedialMorphProfile.udVerbForm` is the finite verb form at the top of the
  order and the converb everywhere else
* `SwitchReference`, `InterclauseRelation`, `BridgingType` — the same-subject or
  different-subject value a form marks, the relations a form can encode, of which
  `InterclauseRelation.Temporal` are the two temporal ones, and the two bridging
  constructions across chains
* `MedialForm` — the class of a language's medial forms, with `MedialForm.HasSR`,
  `MedialForm.SRObligatory` and `MedialForm.SSUnmarked` for its switch-reference system,
  `MedialForm.agreement` for the retention of subject agreement and
  `MedialForm.relationsMarked` for the relations some form encodes

## References

* [sarvasy-aikhenvald-2025]
* [de-vries-2025]
* [foley-r-d-van-valin-1984]
* [longacre-2007]
-/

@[expose] public section

namespace Clause.Chaining

/-! ### Retention of inflectional categories -/

/-- How much of an inflectional category a medial verb retains relative to an independent
verb: none, the value coming from the final verb; fewer values than an independent verb; or
the same range of values. -/
inductive CategoryRetention where
  /-- Unmarked on medial verbs; the value is inherited from the final verb. -/
  | absent
  /-- Fewer values than independent verbs, such as relative tense or a binary realis/irrealis
  split. -/
  | restricted
  /-- The same range of values as independent verbs. -/
  | full
  deriving DecidableEq, Repr, Fintype

namespace CategoryRetention

/-- Position on the retention scale. -/
def rank : CategoryRetention → ℕ
  | absent => 0
  | restricted => 1
  | full => 2

/-- The retention scale `absent < restricted < full`. -/
instance : LinearOrder CategoryRetention := .lift' rank (by decide)

instance : BoundedOrder CategoryRetention where
  top := full
  le_top := by decide
  bot := absent
  bot_le := by decide

@[simp] theorem top_eq_full : (⊤ : CategoryRetention) = full := rfl

@[simp] theorem bot_eq_absent : (⊥ : CategoryRetention) = absent := rfl

variable {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]

/-- How far a language's medial forms retain a category, given which of them admit it, fully
when every form does, restrictedly when some do, and not at all when none does. -/
def ofPred : CategoryRetention :=
  if ∀ i, p i then full else if ∃ i, p i then restricted else absent

theorem ofPred_eq_full_iff : ofPred p = full ↔ ∀ i, p i := by
  unfold ofPred; split_ifs <;> simp_all

theorem ofPred_eq_restricted_iff : ofPred p = restricted ↔ (∃ i, p i) ∧ ∃ i, ¬ p i := by
  unfold ofPred; split_ifs <;> simp_all

theorem ofPred_eq_absent_iff [Nonempty ι] : ofPred p = absent ↔ ∀ i, ¬ p i := by
  unfold ofPred; split_ifs <;> simp_all

end CategoryRetention

/-- The inflectional categories along which a medial verb is reduced. -/
inductive InflectionalCategory where
  /-- Tense. -/
  | tense
  /-- Subject agreement. -/
  | agreement
  /-- Mood. -/
  | mood
  /-- Independent negation of the medial clause. -/
  | polarity
  /-- Aspect. -/
  | aspect
  deriving DecidableEq, Repr, Fintype

/-- A medial verb's retention of each inflectional category, ordered pointwise; the top is the
profile of an independent verb and the bottom a bare converb. -/
abbrev MedialMorphProfile := InflectionalCategory → CategoryRetention

namespace MedialMorphProfile

/-- The UD verb form of a medial verb with a profile, finite when every category is fully
retained and a converb otherwise. -/
def udVerbForm (p : MedialMorphProfile) : UD.VerbForm := if p = ⊤ then .Fin else .Conv

theorem udVerbForm_eq_fin_iff (p : MedialMorphProfile) : p.udVerbForm = .Fin ↔ p = ⊤ := by
  unfold udVerbForm; split_ifs <;> simp_all

end MedialMorphProfile

/-! ### Switch-reference, relations and bridging -/

/-- The switch-reference value a medial form marks: the subject of its clause is the same as
that of the reference clause, or different. -/
inductive SwitchReference where
  /-- Same subject. -/
  | ss
  /-- Different subject. -/
  | ds
  deriving DecidableEq, Repr, Fintype

/-- A semantic relation between a medial clause and the next clause that a medial form can
encode ([sarvasy-aikhenvald-2025]; [longacre-2007]). -/
inductive InterclauseRelation where
  /-- The medial event precedes the next event, in iconic order. -/
  | sequential
  /-- The medial event overlaps the next event. -/
  | simultaneous
  /-- The medial event is the reason for the next event. -/
  | causal
  /-- The medial event is a condition on the next event. -/
  | conditional
  /-- The medial event holds despite the next event. -/
  | concessive
  /-- The medial event specifies how the next event occurs. -/
  | manner
  /-- The events contrast. -/
  | contrastive
  /-- The medial event is added without temporal or causal import. -/
  | additive
  /-- The medial event is the purpose of the next event. -/
  | purpose
  deriving DecidableEq, Repr, Fintype

/-- The temporal relations, sequence and simultaneity. -/
def InterclauseRelation.Temporal (r : InterclauseRelation) : Prop :=
  r = .sequential ∨ r = .simultaneous

instance : DecidablePred InterclauseRelation.Temporal :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The bridging constructions spanning chain boundaries in oral narrative. -/
inductive BridgingType where
  /-- Recapitulative (tail-head) linkage: the first medial clause of a new chain repeats the
  final clause of the preceding one. -/
  | recapitulative
  /-- Summary linkage: a generic verb such as 'do' or 'be' summarizes the preceding chain. -/
  | summary
  deriving DecidableEq, Repr, Fintype

/-! ### A language's medial forms -/

/-- A language's medial forms, each with the switch-reference value it marks, the
interclausal relations it encodes, and whether it indexes the subject of its clause. -/
class MedialForm (M : Type*) where
  /-- The switch-reference value a form marks, `none` for a form neutral to it. -/
  sr : M → Option SwitchReference
  /-- The interclausal relations a form encodes. -/
  relations : M → Finset InterclauseRelation
  /-- The form carries subject cross-referencing. -/
  IndexesSubject : M → Prop
  [decidableIndexesSubject : DecidablePred IndexesSubject]

namespace MedialForm

attribute [instance_reducible] decidableIndexesSubject
attribute [instance] decidableIndexesSubject

section

variable (M : Type*) [MedialForm M]

/-- Some medial form marks switch-reference. -/
def HasSR : Prop := ∃ m : M, sr m ≠ none

/-- Every medial form marks switch-reference. -/
def SRObligatory : Prop := ∀ m : M, sr m ≠ none

/-- The same-subject forms leave the subject unindexed and the different-subject forms index
it, the dominant markedness pattern of switch-reference. -/
def SSUnmarked : Prop :=
  (∀ m : M, sr m = some .ss → ¬ IndexesSubject m) ∧ ∀ m : M, sr m = some .ds → IndexesSubject m

end

section

variable (M : Type*) [MedialForm M] [Fintype M]

instance : Decidable (HasSR M) := inferInstanceAs (Decidable (∃ m : M, sr m ≠ none))

instance : Decidable (SRObligatory M) := inferInstanceAs (Decidable (∀ m : M, sr m ≠ none))

instance : Decidable (SSUnmarked M) := inferInstanceAs (Decidable (_ ∧ _))

/-- How far the medial verbs retain subject agreement. -/
def agreement : CategoryRetention := .ofPred (IndexesSubject (M := M))

/-- The relations some medial form encodes. -/
def relationsMarked : Finset InterclauseRelation := (Finset.univ : Finset M).biUnion relations

end

theorem SRObligatory.hasSR {M : Type*} [MedialForm M] [Nonempty M] (h : SRObligatory M) :
    HasSR M :=
  ⟨Classical.arbitrary M, h _⟩

@[simp] theorem mem_relationsMarked {M : Type*} [MedialForm M] [Fintype M]
    {r : InterclauseRelation} : r ∈ relationsMarked M ↔ ∃ m : M, r ∈ relations m := by
  simp [relationsMarked]

theorem agreement_eq_absent_iff {M : Type*} [MedialForm M] [Fintype M] [Nonempty M] :
    agreement M = .absent ↔ ∀ m : M, ¬ IndexesSubject m :=
  CategoryRetention.ofPred_eq_absent_iff _

theorem agreement_eq_full_iff {M : Type*} [MedialForm M] [Fintype M] :
    agreement M = .full ↔ ∀ m : M, IndexesSubject m :=
  CategoryRetention.ofPred_eq_full_iff _

end MedialForm

end Clause.Chaining
