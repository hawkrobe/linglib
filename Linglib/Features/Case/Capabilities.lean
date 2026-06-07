import Linglib.Core.Order.Flat
import Linglib.Features.Case.Basic

/-!
# Case — carrier capabilities
[blake-1994] [corbett-2006]

The typeclass mixin for carriers that bear grammatical case — the case
analogue of `HasPerson` (`Features/Person/Capabilities.lean`). `caseOf`
extracts the carrier's analytical case value; `Compatible` is the
concord-checking relation. Carriers that store UD realization
(`UD.MorphFeatures`) lift through `Case.fromUD`.
-/

set_option autoImplicit false

/-- A carrier of grammatical case. `none` = the carrier does not mark
    case. -/
class HasCase (α : Type*) where
  /-- The analytical case value, if marked. -/
  caseOf : α → Option Case

export HasCase (caseOf)

instance : HasCase UD.MorphFeatures :=
  ⟨fun mf => mf.case_.map Case.fromUD⟩

instance : HasCase Case := ⟨some⟩

namespace HasCase

variable {α β : Type*} [HasCase α] [HasCase β]

/-- Two carriers are case-compatible: the slot values are compatible in
    the flat information order (`Compat`) — if both mark case, the values
    agree; unmarked carriers are wildcards. The concord-checking
    relation. -/
def Compatible (a : α) (b : β) : Prop :=
  Compat (α := Flat Case) (caseOf a) (caseOf b)

instance (a : α) (b : β) : Decidable (Compatible a b) := by
  unfold Compatible
  infer_instance

theorem compatible_comm {a : α} {b : β} (h : Compatible a b) :
    Compatible b a :=
  h.symm

theorem compatible_of_none {a : α} (h : caseOf a = none) (b : β) :
    Compatible a b := by
  unfold Compatible
  rw [h]
  exact bot_compat _

end HasCase

/-- φ-compatibility entails case compatibility: the `HasCase` mixin
    never diverges from the unification-based agreement engine
    (`UD.MorphFeatures.compatible`) — the case analogue of
    `UD.MorphFeatures.compatible_hasPerson`. -/
theorem UD.MorphFeatures.compatible_hasCase {f1 f2 : UD.MorphFeatures}
    (h : f1.compatible f2 = true) :
    HasCase.Compatible f1 f2 := by
  unfold HasCase.Compatible
  rw [Flat.compat_iff]
  intro ca ha cb hb
  have hc : (f1.case_.isNone || f2.case_.isNone || f1.case_ == f2.case_)
      = true := by
    unfold UD.MorphFeatures.compatible at h
    simp only [Bool.and_eq_true] at h
    tauto
  simp only [HasCase.caseOf] at ha hb
  rcases h1 : f1.case_ with _ | u1
  · rw [h1] at ha
    exact absurd ha (by simp)
  · rcases h2 : f2.case_ with _ | u2
    · rw [h2] at hb
      exact absurd hb (by simp)
    · rw [h1] at ha
      rw [h2] at hb
      rw [h1, h2] at hc
      simp only [Option.isNone_some, Bool.false_or, beq_iff_eq,
        Option.some.injEq] at hc
      simp only [Option.map_some] at ha hb
      subst hc
      exact (Option.some.inj ha).symm.trans (Option.some.inj hb)
