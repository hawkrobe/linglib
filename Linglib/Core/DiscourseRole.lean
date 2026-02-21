import Linglib.Core.Context.Tower

/-!
# Discourse Roles

Framework-agnostic discourse participant roles (speaker, addressee) and their
connection to illocutionary mood. Lakoff (1970) observes that tense selection
depends on which participant holds epistemic authority -- declaratives attribute
knowledge to the speaker, interrogatives to the addressee. This module provides
the infrastructure; `Tense/Perspective.lean` builds Lakoff's constraints on top.

Existing framework-specific types (`PRole` in Minimalism/SpeechActs, `Participant`
in Semantics.Dynamic/State) encode configurational or update-theoretic commitments.
`DiscourseRole` is the agnostic version: just speaker vs addressee, resolved
against a Kaplanian context via `ContextTower` (from the origin, since discourse
roles reflect the actual speech-act participants).

## References

- Lakoff, R. (1970). Tense and its relation to participants. *Language* 46(4).
- Kaplan, D. (1989). Demonstratives.
- Speas, M. & Tenny, C. (2003). Configurational properties of point of view roles.
-/

namespace Core.Discourse

open Core.Context

/-- The two fundamental discourse participants. `.addressee` matches
    `KContext.addressee` (not `.listener` as in Semantics.Dynamic). -/
inductive DiscourseRole where
  | speaker
  | addressee
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Illocutionary mood -- the speech-act force of an utterance.

Distinct from `GramMood` (indicative/subjunctive morphology) and the
Minimalist `SAPMood` (configurational). This classifies the pragmatic
act performed. -/
inductive IllocutionaryMood where
  | declarative
  | interrogative
  | imperative
  | promissive
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Which participant holds epistemic authority for a given illocutionary mood.

Lakoff (1970): in declaratives, imperatives, and promissives the speaker is the
seat of knowledge; in interrogatives the addressee is. -/
def epistemicAuthority : IllocutionaryMood → DiscourseRole
  | .declarative   => .speaker
  | .interrogative  => .addressee
  | .imperative     => .speaker
  | .promissive     => .speaker

/-- Resolve a discourse role to a concrete entity via a ContextTower,
    reading from the origin (speech-act context).
    `.speaker -> tower.origin.agent`, `.addressee -> tower.origin.addressee`. -/
def resolveRole {W E P T : Type*}
    (tower : ContextTower (KContext W E P T)) :
    DiscourseRole → E
  | .speaker   => tower.origin.agent
  | .addressee => tower.origin.addressee

-- ════════════════════════════════════════════════════════════════
-- § Verification
-- ════════════════════════════════════════════════════════════════

theorem epistemic_authority_declarative :
    epistemicAuthority .declarative = .speaker := rfl

theorem epistemic_authority_interrogative :
    epistemicAuthority .interrogative = .addressee := rfl

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
