import Linglib.Theories.Syntax.Minimalism.Movement.Smuggling

/-!
# Inverse Voice Construction Family
@cite{collins-2005} @cite{storment-2025} @cite{storment-2026}

A family abstraction over voice phenomena unified by smuggling
(@cite{storment-2026}, §4.3 + §6 + §7): passive, dative shift,
quotative inversion (QI), locative inversion (LI), middles, causatives,
antipassives. Each is "an information-structurally marked configuration
in which a given thematic argument is mapped onto an A-position that
would not be accessible to the same argument in a standard unmarked
configuration" (@cite{storment-2026}, eq. 121).

The unifying syntactic mechanism: a non-phase Voice head permits
smuggling of a constituent containing the thematic argument to
Spec,VoiceP, making it accessible to T⁰ for Case licensing.

This file abstracts the family invariant and provides instances for
the constructions documented in @cite{storment-2026}. Specific paper
analyses (Collins 2005 for passive; Storment 2026 for QI/LI) live in
their respective Studies files; this file is the shared substrate.
-/

namespace Minimalism

/-- Tag identifying which inverse-voice construction is at issue.
    Storment §4.3 lists these as the unified family. -/
inductive InverseVoiceKind where
  | passive            -- @cite{collins-2005}
  | dativeShift        -- Collins 2021/2024
  | quotativeInversion -- @cite{storment-2026}
  | locativeInversion  -- @cite{storment-2026}, §6
  | middle             -- Gotah 2024
  | causative          -- Belletti 2017
  | antipassive
  deriving DecidableEq, Repr

/-- An inverse-voice construction is parameterized by its kind, the
    Voice head it projects, and a flag indicating whether the moved
    constituent's licensing succeeds (depends on having a single DP
    inside the smuggled constituent — Storment §5 transitivity
    constraint). -/
structure InverseVoiceConstruction where
  kind : InverseVoiceKind
  voice : VoiceHead
  /-- True iff the constituent that smuggles to Spec,VoiceP contains
      at most one Case-needing DP (Storment §5 transitivity constraint).
      When false, the derivation crashes on Case licensing. -/
  satisfiesTransitivityConstraint : Bool
  deriving Repr

/-- The family invariant: every inverse-voice construction projects a
    Voice head that permits smuggling. Used as the well-formedness
    predicate. -/
def InverseVoiceConstruction.voiceWellFormed (c : InverseVoiceConstruction) : Bool :=
  c.voice.permitsSmuggling

/-- A construction is licensed iff its Voice permits smuggling AND
    the transitivity constraint is satisfied. The two conditions are
    independent, mirroring Storment's analysis in §4 and §5. -/
def InverseVoiceConstruction.licensed (c : InverseVoiceConstruction) : Bool :=
  c.voiceWellFormed && c.satisfiesTransitivityConstraint

theorem InverseVoiceConstruction.licensed_iff (c : InverseVoiceConstruction) :
    c.licensed = true ↔
      c.voice.permitsSmuggling = true ∧ c.satisfiesTransitivityConstraint = true := by
  unfold InverseVoiceConstruction.licensed InverseVoiceConstruction.voiceWellFormed
  simp only [Bool.and_eq_true]

/-- An agentive Voice can never appear in an inverse-voice construction:
    the family invariant fails. -/
theorem InverseVoiceConstruction.agentive_voice_not_wellformed
    (c : InverseVoiceConstruction) (h : c.voice = voiceAgent) :
    c.voiceWellFormed = false := by
  unfold InverseVoiceConstruction.voiceWellFormed
  rw [h]; exact agentive_blocks_smuggling

/-- Transitivity-constraint failure alone blocks licensing even with
    a smuggling-compatible Voice. -/
theorem InverseVoiceConstruction.transitivity_failure_blocks
    (c : InverseVoiceConstruction) (h : c.satisfiesTransitivityConstraint = false) :
    c.licensed = false := by
  unfold InverseVoiceConstruction.licensed; simp [h]

/-! ## Instances

Currently only QI and LI have study-file consumers (`Storment2026.lean`
attests the QI ∥ LI shared-mechanism claim). Passive (Collins 2005),
middle (Gotah 2024), dative shift (Collins 2021/2024), and causatives
(Belletti 2017) are accommodated by the family abstraction but await
their own study files before adding canonical instances here — adding
them now would be premature architecture. -/

/-- Quotative inversion in its canonical form: anticausative Voice
    permits smuggling of the VP containing the quotative operator. -/
def qiCanonical : InverseVoiceConstruction where
  kind := .quotativeInversion
  voice := voiceAnticausative
  satisfiesTransitivityConstraint := true

/-- Locative inversion in its canonical form: same Voice mechanism as
    QI per @cite{storment-2026}, §6. -/
def liCanonical : InverseVoiceConstruction where
  kind := .locativeInversion
  voice := voiceAnticausative
  satisfiesTransitivityConstraint := true

/-- QI and LI are both licensed and share a Voice head — the §6 claim
    that they are unified by smuggling reduces to two equalities. -/
theorem qi_li_unified :
    qiCanonical.licensed = true ∧
    liCanonical.licensed = true ∧
    qiCanonical.voice = liCanonical.voice :=
  ⟨rfl, rfl, rfl⟩

end Minimalism
