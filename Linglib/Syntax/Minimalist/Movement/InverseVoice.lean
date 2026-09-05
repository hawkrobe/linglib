import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# The inverse-voice family

[storment-2026] groups passive, dative shift, quotative inversion, locative inversion, middles,
causatives and antipassives as inverse-voice constructions: information-structurally marked
configurations mapping a thematic argument onto an A-position it could not reach in the
unmarked configuration. The shared mechanism is smuggling to Spec-VoiceP, which requires a
Voice head that is not a phase head, so that its complement can move, together with the
transitivity constraint that the moved constituent contain at most one Case-needing DP. The
family invariant and the canonical instances documented by the paper live here; the passive
instance follows [collins-2005], whose *by* heads Voice.

## References

* [J. Storment, *Quotative Inversion as Smuggling* (2026)][storment-2026]
* [C. Collins, *A Smuggling Approach to the Passive in English* (2005)][collins-2005]
-/

namespace Minimalist

/-- The constructions [storment-2026] unifies as inverse voice. -/
inductive InverseVoiceKind where
  | passive
  | dativeShift
  | quotativeInversion
  | locativeInversion
  | middle
  | causative
  | antipassive
  deriving DecidableEq, Repr

/-- An inverse-voice construction: its kind, the Voice head it projects, and whether the
constituent moving to Spec-VoiceP contains at most one Case-needing DP, the transitivity
constraint of [storment-2026]. -/
structure InverseVoiceConstruction where
  /-- The construction. -/
  kind : InverseVoiceKind
  /-- The Voice head projected. -/
  voice : Voice.Head
  /-- The moved constituent contains at most one Case-needing DP. -/
  satisfiesTransitivityConstraint : Bool
  deriving DecidableEq, Repr

namespace InverseVoiceConstruction

variable (c : InverseVoiceConstruction)

/-- The family invariant: the Voice head is not a phase head, so its complement can move. -/
def VoiceWellFormed : Prop := ¬ c.voice.IsPhasal

instance : Decidable c.VoiceWellFormed := inferInstanceAs (Decidable (¬ _))

/-- The construction is licensed: well-formed Voice and the transitivity constraint. -/
def Licensed : Prop := c.VoiceWellFormed ∧ c.satisfiesTransitivityConstraint = true

instance : Decidable c.Licensed := inferInstanceAs (Decidable (_ ∧ _))

/-- Agentive Voice, a phase head, never heads an inverse-voice construction. -/
theorem not_voiceWellFormed_of_agentive (h : c.voice = Voice.agentive) :
    ¬ c.VoiceWellFormed := by
  rw [VoiceWellFormed, h]; decide

/-- Failing the transitivity constraint blocks licensing whatever the Voice head. -/
theorem not_licensed_of_transitivity (h : c.satisfiesTransitivityConstraint = false) :
    ¬ c.Licensed := λ hl => by simp [Licensed, h] at hl

end InverseVoiceConstruction

/-! ### The canonical instances -/

/-- Quotative inversion: anticausative Voice, and the VP containing the quotative operator
moves. -/
def qiCanonical : InverseVoiceConstruction where
  kind := .quotativeInversion
  voice := Voice.anticausative
  satisfiesTransitivityConstraint := true

/-- Locative inversion: the same Voice head as quotative inversion ([storment-2026] §6). -/
def liCanonical : InverseVoiceConstruction where
  kind := .locativeInversion
  voice := Voice.anticausative
  satisfiesTransitivityConstraint := true

/-- The passive: Voice headed by *by* ([collins-2005]), distinct from the anticausative Voice
of unaccusatives, and PartP containing the object moves. -/
def passiveCanonical : InverseVoiceConstruction where
  kind := .passive
  voice := Voice.passive
  satisfiesTransitivityConstraint := true

/-- The three canonical constructions are licensed; quotative and locative inversion share a
Voice head, the passive has its own, and all three Voice heads are non-phasal, the invariant
being the mechanism rather than the head. -/
theorem inverse_voice_canonical :
    qiCanonical.Licensed ∧ liCanonical.Licensed ∧ passiveCanonical.Licensed ∧
      qiCanonical.voice = liCanonical.voice ∧ qiCanonical.voice ≠ passiveCanonical.voice := by
  decide

end Minimalist
