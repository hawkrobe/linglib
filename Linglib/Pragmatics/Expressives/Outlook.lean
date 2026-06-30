import Linglib.Semantics.Presupposition.Basic
import Linglib.Pragmatics.Expressives.Basic

/-!
# Outlook-indexed two-dimensional meaning
[coppock-2018] [potts-2005] [harris-potts-2009]

[coppock-2018]'s *outlook*-relative enrichment of the two-dimensional meaning of
[potts-2005]. A `TwoDimProp` fixes a single perspective; an `Outlook` is a family of
two-dimensional meanings indexed by an *outlook* `O` (a circumstance of evaluation that
settles matters of opinion, not just fact), together with a presupposed counterstance.

The point of the index is perspective shift ([harris-potts-2009]): the use-conditional tier
is evaluated at the speaker's outlook by default, but an attitude verb may supply the
holder's outlook instead. A pure expressive is the **constant** family (`ofTwoDimProp`),
so it cannot shift; `IsRigid` is exactly that constancy, and the perspective-shift diagnostic
is then a theorem about the structure rather than a stipulated flag.

## Main definitions

* `Outlook` — prejacent + counterstance + outlook-relative `evaluation`.
* `Outlook.toPartialProp`, `Outlook.toTwoDimProp` — the presuppositional and (perspective-fixed)
  two-dimensional projections.
* `Outlook.IsRigid` — the evaluation ignores the outlook (the pure-expressive corner).
* `Outlook.ofTwoDimProp` — a `TwoDimProp` as the constant (speaker-rigid) outlook family.

## Main results

* `rigid_noShift` — a rigid outlook's CI is invariant under a change of outlook.
* `ofTwoDimProp_isRigid` — every embedded `TwoDimProp` is rigid.
* `not_isRigid_of_evaluation_ne` — distinct evaluations witness perspective shift.

## References

[coppock-2018] [potts-2005] [harris-potts-2009]
-/

namespace Pragmatics.Expressives

open Semantics.Presupposition (PartialProp)

variable {W O : Type*}

/-- An outlook-indexed two-dimensional meaning ([coppock-2018]). At-issue content is shared
across outlooks (only the use-conditional tier shifts), so the prejacent is stored once and
the CI tier is a function of the outlook. -/
structure Outlook (W O : Type*) where
  /-- At-issue content, outlook-independent. -/
  prejacent : W → Prop
  /-- Presupposed salient counterstance. -/
  counterstance : W → Prop
  /-- Use-conditional tier, relative to an outlook. -/
  evaluation : O → W → Prop

namespace Outlook

/-- Presuppositional projection: the counterstance is the presupposition, the prejacent the
assertion. Outlook-independent. -/
def toPartialProp (m : Outlook W O) : PartialProp W := ⟨m.counterstance, m.prejacent⟩

/-- Two-dimensional projection at an outlook `o`: an ordinary `TwoDimProp` recovered by
fixing the perspective. -/
def toTwoDimProp (m : Outlook W O) (o : O) : TwoDimProp W := ⟨m.prejacent, m.evaluation o⟩

/-- The CI content attributed when the judge has outlook `o`. -/
def ciFrom (m : Outlook W O) (o : O) : W → Prop := m.evaluation o

@[simp] theorem toPartialProp_presup (m : Outlook W O) :
    m.toPartialProp.presup = m.counterstance := rfl
@[simp] theorem toPartialProp_assertion (m : Outlook W O) :
    m.toPartialProp.assertion = m.prejacent := rfl
@[simp] theorem toTwoDimProp_atIssue (m : Outlook W O) (o : O) :
    (m.toTwoDimProp o).atIssue = m.prejacent := rfl
@[simp] theorem toTwoDimProp_ci (m : Outlook W O) (o : O) :
    (m.toTwoDimProp o).ci = m.evaluation o := rfl
@[simp] theorem ciFrom_eq (m : Outlook W O) (o : O) : m.ciFrom o = m.evaluation o := rfl

/-- The counterstance (presupposition) projects through negation — via `PartialProp.neg`. -/
theorem counterstance_projects_through_neg (m : Outlook W O) :
    (PartialProp.neg m.toPartialProp).presup = m.counterstance := rfl

/-- The CI tier projects through negation at a fixed outlook — via `TwoDimProp.neg`. -/
theorem ci_projects_through_neg (m : Outlook W O) (o : O) :
    (TwoDimProp.neg (m.toTwoDimProp o)).ci = m.evaluation o := rfl

/-! ### Rigidity: the pure-expressive corner -/

/-- An outlook is **rigid** when its CI ignores the outlook — the perspective-insensitive
(pure-expressive) case. Perspective shift is exactly the failure of this. This is the
canonical rigidity predicate of `Semantics.Intensional.Rigidity` (`Intension.IsRigid`)
applied to `evaluation`: constancy of the CI tier across the outlook index. -/
def IsRigid (m : Outlook W O) : Prop := ∀ o₁ o₂, m.evaluation o₁ = m.evaluation o₂

/-- A rigid outlook's CI is invariant under a change of outlook: no perspective shift. -/
theorem rigid_noShift {m : Outlook W O} (h : m.IsRigid) (o₁ o₂ : O) :
    m.ciFrom o₁ = m.ciFrom o₂ := h o₁ o₂

/-- Distinct evaluations witness perspective shift: the outlook is not rigid. -/
theorem not_isRigid_of_evaluation_ne {m : Outlook W O} {o₁ o₂ : O}
    (h : m.evaluation o₁ ≠ m.evaluation o₂) : ¬ m.IsRigid :=
  fun hr => h (hr o₁ o₂)

/-- A `TwoDimProp` (a pure expressive — a single, speaker-rigid CI) as the constant outlook
family: its evaluation ignores the outlook, and it carries the trivial counterstance. -/
def ofTwoDimProp (t : TwoDimProp W) : Outlook W O where
  prejacent := t.atIssue
  counterstance := fun _ => True
  evaluation := fun _ => t.ci

@[simp] theorem ofTwoDimProp_toTwoDimProp (t : TwoDimProp W) (o : O) :
    (ofTwoDimProp t).toTwoDimProp o = t := rfl

/-- Every embedded `TwoDimProp` is rigid — pure expressives do not perspective-shift, by
construction. -/
theorem ofTwoDimProp_isRigid (t : TwoDimProp W) : (ofTwoDimProp (O := O) t).IsRigid :=
  fun _ _ => rfl

end Outlook

end Pragmatics.Expressives
