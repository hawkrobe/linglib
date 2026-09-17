import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic

/-!
# Valency alternations

A valency alternation relates two argument frames of one predicate,
the initial and the derived construction, by a correspondence between
their slots: which slot of the derived frame each participant of the
initial frame occupies. Everything [creissels-2024] reads off an
alternation is derived from the pair: the fate of an initial core term
(`ValencyAlternation.fate`), the participant the derived construction
introduces (`newParticipant`), whether the alternation nucleativizes or
denucleativizes, and so whether it increases or decreases valency. The
main types of §8.3 are constants: `causativization`,
`decausativization`, `passivization`, `antipassivization`, the
applicativizations and the rest. Whether an alternation is coded by
verbal morphology, and so a *voice* alternation rather than
flexivalency, is its `marking`.

## Main definitions

* `Voice.TermRole` — the transitivity-related roles S, A, P and X
* `Voice.ParticipantFate` — what an alternation does to an initial core
  term
* `Voice.AlternationMarking` — coded or uncoded
* `Voice.ValencyAlternation` — the initial and derived frames with their
  slot correspondence
* `ValencyAlternation.image`, `fate`, `fateOfRole`, `introduced`,
  `newParticipant` — the derived participant bookkeeping
* `ValencyAlternation.Nucleativizes`, `Denucleativizes`,
  `IsValencyIncreasing`, `IsValencyDecreasing`, `Cumulates` — the
  derived classification
* `Voice.causativization`, …, `Voice.portativeDerivation` — the types of
  [creissels-2024] §8.3
* `Voice.Alignment`, `Voice.AmbitransitivityType` — alignment and
  uncoded transitivity alternation

## Main results

* `Voice.passivization_vs_decausativization` — passivization keeps the
  initial A in participant structure, decausativization suppresses it
* `Voice.as_nucleativization_neutral` — nucleativization is not valency
  increase

## Implementation notes

A slot of the initial frame with no correspondent is suppressed from
participant structure; one whose correspondent is an implicit or an
adpositional position is denucleativized but maintained; two initial
core terms with one correspondent are cumulated. The derived frame of a
passive records the demoted agent as implicit, the canonical short
passive; a long passive refines it. Coding is a per-language property,
so the constants are uncoded and a fragment sets `marking` when it
instantiates one. Within `Syntax/Voice/` this file owns the valency
axis; `Basic.lean` owns the pivot axis.

## References

* [comrie-1989]
* [creissels-2024]
* [dixon-1994]
* [dixon-aikhenvald-2000]
* [song-1996]
-/

namespace Voice

/-! ### Transitivity-related roles (§1.3.3) -/

/-- The role of a nominal term in [creissels-2024]'s binary core-term system: the core
roles S, A and P, and X for obliques. -/
inductive TermRole where
  /-- The sole core term of an intransitive clause. -/
  | S
  /-- The agent-like core term of a transitive clause. -/
  | A
  /-- The patient-like core term of a transitive clause. -/
  | P
  /-- An oblique. -/
  | X
  deriving DecidableEq, Repr

/-- The transitivity-related role of a comparative coding role: recipients and themes are
P-like core terms. -/
def TermRole.ofArgumentRole : ArgumentRole → TermRole
  | .S => .S
  | .A => .A
  | .P | .R | .T => .P

/-! ### Participant fate -/

/-- What an alternation does to a core term of the initial construction. -/
inductive ParticipantFate where
  /-- Not a core term of the derived construction, but maintained in participant structure
      as an oblique or an implied participant. -/
  | denucleativized
  /-- Removed from participant structure. -/
  | suppressed
  /-- A core term of the derived construction. -/
  | maintained
  /-- One core term of the derived construction with another initial core term. -/
  | cumulated
  /-- Not a core term of the initial construction. -/
  | na
  deriving DecidableEq, Repr

/-- The fate removes the participant from core-term status. -/
def ParticipantFate.RemovesFromCoreStatus : ParticipantFate → Prop
  | .denucleativized | .suppressed => True
  | _ => False

instance : DecidablePred ParticipantFate.RemovesFromCoreStatus := fun f ↦ by
  cases f <;> unfold ParticipantFate.RemovesFromCoreStatus <;> infer_instance

/-! ### Marking -/

/-- How a valency alternation is coded: by verbal morphology, an analytic construction,
equipollent marking, or not at all, flexivalency ([creissels-2024] §1.1.3). -/
inductive AlternationMarking where
  | synthetic
  | analytic
  | equipollent
  | uncoded
  deriving DecidableEq, Repr

/-- A coded alternation is a voice alternation. -/
def AlternationMarking.IsVoice (m : AlternationMarking) : Prop := m ≠ .uncoded

instance : DecidablePred AlternationMarking.IsVoice := fun m ↦
  inferInstanceAs (Decidable (m ≠ _))

/-! ### Valency alternations -/

/-- A valency alternation: the initial and the derived argument frame, and the slot of the
derived frame each slot of the initial frame's participant occupies. -/
structure ValencyAlternation where
  /-- The initial construction. -/
  source : ArgumentFrame
  /-- The derived construction. -/
  target : ArgumentFrame
  /-- The derived slot each initial slot's participant occupies; an initial slot without an
      entry is suppressed from participant structure. -/
  correspondence : List (ArgumentFrame.Slot × ArgumentFrame.Slot)
  /-- The coding of the alternation, a per-language property. -/
  marking : AlternationMarking := .uncoded
  deriving DecidableEq, Repr

namespace ValencyAlternation

open ArgumentFrame (Slot)

variable (α : ValencyAlternation)

/-- The derived slot an initial slot's participant occupies. -/
def image (s : Slot) : Option Slot := α.correspondence.lookup s

/-- The initial slots whose participant occupies a derived slot. -/
def preimages (t : Slot) : List Slot :=
  α.source.slots.filter fun s ↦ α.image s == some t

/-- The transitivity-related role of a derived slot: the coding role of a core slot, X for an
expressed oblique, none for an implicit or expletive position. -/
def targetRole (t : Slot) : Option TermRole :=
  match α.target.codingRole t, α.target.get? t with
  | some r, _ => some (TermRole.ofArgumentRole r)
  | none, some p => if p.IsExpressed then some .X else none
  | none, none => none

/-- The fate of an initial slot: suppressed without a correspondent; cumulated when another
initial core term shares its derived core slot; maintained in a derived core slot;
denucleativized otherwise; not applicable to a non-core initial slot. -/
def fate (s : Slot) : ParticipantFate :=
  if s ∈ α.source.coreSlots then
    match α.image s with
    | none => .suppressed
    | some t =>
      if t ∈ α.target.coreSlots then
        if (α.preimages t).any (fun s' ↦ s' != s && s' ∈ α.source.coreSlots) then .cumulated
        else .maintained
      else .denucleativized
  else .na

/-- The fate of the initial core term with a transitivity-related role. -/
def fateOfRole (r : TermRole) : ParticipantFate :=
  match α.source.coreSlots.find? fun s ↦
      (α.source.codingRole s).map TermRole.ofArgumentRole == some r with
  | some s => α.fate s
  | none => .na

/-- The derived slots the derived construction introduces: expressed slots whose participant
was not a core term of the initial construction, either new to it or nucleativized from a
non-core slot. -/
def introduced : List Slot :=
  α.target.slots.filter fun t ↦
    (α.targetRole t).isSome &&
      (α.preimages t).all fun s ↦ s ∉ α.source.coreSlots && t ∈ α.target.coreSlots

/-- The role of the participant the derived construction introduces, if one. -/
def newParticipant : Option TermRole := α.introduced.head?.bind α.targetRole

/-- Some participant becomes a core term. -/
def Nucleativizes : Prop := ∃ t ∈ α.introduced, t ∈ α.target.coreSlots

/-- Some initial core term ceases to be one. -/
def Denucleativizes : Prop :=
  ∃ s ∈ α.source.coreSlots, (α.fate s).RemovesFromCoreStatus

/-- Two initial core terms are cumulated. -/
def Cumulates : Prop := ∃ s ∈ α.source.coreSlots, α.fate s = .cumulated

/-- Valency-increasing: nucleativizes without denucleativizing. -/
def IsValencyIncreasing : Prop := α.Nucleativizes ∧ ¬ α.Denucleativizes

/-- Valency-decreasing: denucleativizes without nucleativizing. -/
def IsValencyDecreasing : Prop := α.Denucleativizes ∧ ¬ α.Nucleativizes

instance : Decidable α.Nucleativizes := inferInstanceAs (Decidable (∃ _ ∈ _, _))
instance : Decidable α.Denucleativizes := inferInstanceAs (Decidable (∃ _ ∈ _, _))
instance : Decidable α.Cumulates := inferInstanceAs (Decidable (∃ _ ∈ _, _))
instance : Decidable α.IsValencyIncreasing := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable α.IsValencyDecreasing := inferInstanceAs (Decidable (_ ∧ _))

end ValencyAlternation

/-! ### The types of [creissels-2024] §8.3 -/

open ArgumentFrame.Slot

/-- Causativization (§8.3.1.1): a causer is nucleativized as the A of a transitive
construction whose P is the initial S. -/
def causativization : ValencyAlternation :=
  { source := .intransitive, target := .np, correspondence := [(external, complement 0)] }

/-- Decausativization (§8.3.1.2): the initial A is suppressed from participant structure and
the initial P is the S of an intransitive construction. Called anticausative elsewhere. -/
def decausativization : ValencyAlternation :=
  { source := .np, target := .unaccusative, correspondence := [(complement 0, complement 0)] }

/-- Passivization (§8.3.2.1): the initial A is denucleativized but maintained in participant
structure, implied here and expressed as an oblique in a long passive, and the initial P is
the S. -/
def passivization : ValencyAlternation :=
  { source := .np, target := ⟨none, [.nominal, .implicit]⟩,
    correspondence := [(external, complement 1), (complement 0, complement 0)] }

/-- The impersonal variant of passivization (§8.3.2.2): the initial P keeps its coding, so
the derived construction has no S; at the level of frames it is passivization. -/
def iPassivization : ValencyAlternation := passivization

/-- Antipassivization (§8.3.2.3): the initial P is denucleativized and the initial A is the
S of an intransitive construction. -/
def antipassivization : ValencyAlternation :=
  { source := .np, target := .pp,
    correspondence := [(external, external), (complement 0, complement 0)] }

/-- S-denucleativization (§8.3.2.4): the S of an intransitive construction is
denucleativized, yielding an impersonal construction. -/
def sDenucleativization : ValencyAlternation :=
  { source := .intransitive, target := ⟨none, [.implicit]⟩,
    correspondence := [(external, complement 0)] }

/-- Reflexivization (§8.3.3): the initial A and P are cumulated in one S. -/
def reflexivization : ValencyAlternation :=
  { source := .np, target := .intransitive,
    correspondence := [(external, external), (complement 0, external)] }

/-- Reciprocalization (§8.3.3): reflexivization with a group reading. -/
def reciprocalization : ValencyAlternation := reflexivization

/-- P-applicativization (§8.3.5): an applied participant is nucleativized as a second P
beside the initial A and P. -/
def pApplicativization : ValencyAlternation :=
  { source := .np, target := .np_np,
    correspondence := [(external, external), (complement 0, complement 0)] }

/-- D-applicativization (§14.1.3): an applied participant is expressed as a dative oblique,
the initial A and P unchanged. -/
def dApplicativization : ValencyAlternation :=
  { source := .np, target := .np_pp,
    correspondence := [(external, external), (complement 0, complement 0)] }

/-- X-applicativization (§14.1.4): an applied participant is expressed as an ordinary
oblique, the initial S unchanged. -/
def xApplicativization : ValencyAlternation :=
  { source := .intransitive, target := .pp, correspondence := [(external, external)] }

/-- A/S-nucleativization of an oblique (§8.3.4.1): an oblique participant, an instrument,
takes over the role of A and the initial A is denucleativized, understood as non-specific. -/
def asNucleativizationOfObliques : ValencyAlternation :=
  { source := .np_pp, target := ⟨some .nominal, [.nominal, .implicit]⟩,
    correspondence :=
      [(external, complement 1), (complement 0, complement 0), (complement 1, external)] }

/-- Concernativization (§8.3.4.2): a concernee is nucleativized as A and the initial S is
the P; at the level of frames it is causativization, the difference lying in the new
participant's relation to the event. -/
def concernativization : ValencyAlternation := causativization

/-- Portative derivation (§8.3.7): an intransitive motion verb becomes transitive, its S the
A and a carried entity the P. -/
def portativeDerivation : ValencyAlternation :=
  { source := .intransitive, target := .np, correspondence := [(external, external)] }

/-! ### Properties of the types -/

theorem causativization_increases : causativization.IsValencyIncreasing := by decide

theorem decausativization_decreases : decausativization.IsValencyDecreasing := by decide

theorem passivization_decreases : passivization.IsValencyDecreasing := by decide

/-- Passivization maintains the initial A in participant structure; decausativization
suppresses it (§8.3.2.1). -/
theorem passivization_vs_decausativization :
    passivization.fateOfRole .A = .denucleativized ∧
      decausativization.fateOfRole .A = .suppressed := by decide

theorem antipassivization_decreases : antipassivization.IsValencyDecreasing := by decide

theorem reflexivization_cumulates : reflexivization.Cumulates := by decide

theorem pApplicativization_increases : pApplicativization.IsValencyIncreasing := by decide

/-- A/S-nucleativization of an oblique nucleativizes the oblique and denucleativizes the
initial A: neither valency-increasing nor valency-decreasing. -/
theorem as_nucleativization_neutral :
    asNucleativizationOfObliques.Nucleativizes ∧ asNucleativizationOfObliques.Denucleativizes ∧
      ¬ asNucleativizationOfObliques.IsValencyIncreasing ∧
      ¬ asNucleativizationOfObliques.IsValencyDecreasing := by decide

/-- Portative derivation is valency-increasing, like causativization and applicativization,
but reduces to neither (§8.3.7). -/
theorem portative_increases : portativeDerivation.IsValencyIncreasing := by decide

/-! ### Alignment (§1.3.4) -/

/-- The alignment of the core terms of transitive and intransitive clauses: S coded like A,
or like P. -/
inductive Alignment where
  /-- S is coded like A, traditionally accusative. -/
  | A_alignment
  /-- S is coded like P, traditionally ergative. -/
  | P_alignment
  deriving DecidableEq, Repr

/-! ### Ambitransitivity (chapter 15) -/

/-- The types of uncoded transitivity alternation (§15.2). -/
inductive AmbitransitivityType where
  /-- The S of the intransitive is the P of the transitive, *the glass broke*. -/
  | P_ambitransitivity
  /-- The S of the intransitive is the A of the transitive, *she ate*. -/
  | A_ambitransitivity
  /-- The intransitive is reflexive, *she washed*. -/
  | reflexive
  /-- The intransitive is reciprocal, *they kissed*. -/
  | reciprocal
  /-- Underspecified. -/
  | unspecified
  deriving DecidableEq, Repr

/-- P-ambitransitivity is uncoded decausativization. -/
theorem p_ambi_is_uncoded_decausativization :
    decausativization.Denucleativizes ∧ decausativization.marking = .uncoded := by decide

/-- A-ambitransitivity is uncoded antipassivization. -/
theorem a_ambi_is_uncoded_antipassivization :
    antipassivization.Denucleativizes ∧ antipassivization.marking = .uncoded := by decide

end Voice
