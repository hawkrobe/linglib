import Linglib.Semantics.Reference.Context.Tower

/-!
# Discourse Roles

The two fundamental discourse participants — speaker and addressee — and
the function that resolves them through a `ContextTower` to concrete
entities.

This file exists separately from `Discourse/SpeechAct.lean`
to break a would-be cycle between `Semantics/Mood/Defs.lean` (which
needs `DiscourseRole` for `Illocutionary.authority`) and the act-side material in
`SpeechAct.lean` (which extends `Illocutionary` with Searle
classes and direction of fit).
-/

/-- The two fundamental discourse participants. `.addressee` matches
    `KContext.addressee` (not `.listener` as in `DynamicSemantics`). -/
inductive DiscourseRole where
  | speaker
  | addressee
  deriving DecidableEq, Repr, Inhabited

namespace DiscourseRole

open Semantics.Context

variable {W E P T : Type*} (tower : ContextTower (KContext W E P T))

/-- Resolve a discourse role to a concrete entity via a `ContextTower`,
    reading from the origin (speech-act context).
    `.speaker → tower.origin.agent`, `.addressee → tower.origin.addressee`. -/
def resolve : DiscourseRole → E
  | .speaker   => tower.origin.agent
  | .addressee => tower.origin.addressee

theorem resolve_speaker : resolve tower .speaker = tower.origin.agent := rfl

theorem resolve_addressee : resolve tower .addressee = tower.origin.addressee := rfl

/-- Discourse role resolution is invariant under tower push: discourse
    roles reflect speech-act participants (from origin), not embedded ones. -/
theorem resolve_push (σ : ContextShift (KContext W E P T)) (r : DiscourseRole) :
    resolve (tower.push σ) r = resolve tower r := by
  cases r <;> simp only [resolve, ContextTower.push_origin]

end DiscourseRole
