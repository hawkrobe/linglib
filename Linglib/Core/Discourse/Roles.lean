import Linglib.Core.Context.Tower

/-!
# Discourse Roles

The two fundamental discourse participants — speaker and addressee — and
the function that resolves them through a `ContextTower` to concrete
entities.

This file exists separately from `Core/Discourse/IllocutionaryForce.lean`
to break a would-be cycle between `Core/Mood/IllocutionaryMood.lean` (which
needs `DiscourseRole` for `moodAuthority`) and the act-side material in
`IllocutionaryForce.lean` (which extends `IllocutionaryMood` with Searle
classes and direction of fit).
-/

namespace Core.Discourse

open Core.Context

/-- The two fundamental discourse participants. `.addressee` matches
    `KContext.addressee` (not `.listener` as in `Semantics.Dynamic`). -/
inductive DiscourseRole where
  | speaker
  | addressee
  deriving DecidableEq, Repr, Inhabited

/-- Resolve a discourse role to a concrete entity via a `ContextTower`,
    reading from the origin (speech-act context).
    `.speaker → tower.origin.agent`, `.addressee → tower.origin.addressee`. -/
def resolveRole {W E P T : Type*}
    (tower : ContextTower (KContext W E P T)) :
    DiscourseRole → E
  | .speaker   => tower.origin.agent
  | .addressee => tower.origin.addressee

theorem resolve_speaker_is_agent {W E P T : Type*}
    (tower : ContextTower (KContext W E P T)) :
    resolveRole tower .speaker = tower.origin.agent := rfl

theorem resolve_addressee_is_addressee {W E P T : Type*}
    (tower : ContextTower (KContext W E P T)) :
    resolveRole tower .addressee = tower.origin.addressee := rfl

/-- Discourse role resolution is invariant under tower push: discourse
    roles reflect speech-act participants (from origin), not embedded ones. -/
theorem resolveRole_shift_invariant {W E P T : Type*}
    (tower : ContextTower (KContext W E P T))
    (σ : ContextShift (KContext W E P T)) (r : DiscourseRole) :
    resolveRole (tower.push σ) r = resolveRole tower r := by
  cases r <;> simp only [resolveRole, ContextTower.push_origin]

end Core.Discourse
