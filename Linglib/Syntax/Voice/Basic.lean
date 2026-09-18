import Linglib.Syntax.Category.Verb.Defs
import Linglib.Morphology.Morph

/-!
# Voice

A voice relates two argument frames of one predicate, the initial and the
derived construction, by a correspondence between their slots: which slot
of the derived frame each participant of the initial frame occupies. It
records besides the derived slot that is the syntactically privileged term,
the pivot, and the marker by which the verb codes it. Everything a grammar
says of a voice is read off the pair: the fate of an initial core term
(`Voice.fate`), the participant the derived construction introduces
(`newParticipant`), whether the voice nucleativizes or denucleativizes, and so
whether it increases or decreases valency, and whether it leaves transitivity
alone and only selects a pivot (`IsSymmetrical`). The voices a grammar names
are constants: the
`active` and, from the transitive construction, the `passive`, the
`impersonalPassive`, the `antipassive`, the `anticausative`, the `reflexive`
and the `applicative`, the `causative` from the intransitive one, and the
`patientVoice` and `obliqueVoice` of the symmetrical systems. A fragment
states a voice with its marker, `Voice.passive.marked [.suff "x"]`, and two
voices of one language that share an alternation differ by their markers; the
bare constant is the unmarked alternation, a flexivalent verb's or a study's.

## Main definitions

* `Voice.TermRole` — the transitivity-related roles S, A, P and X
* `Voice.ParticipantFate` — what a voice does to an initial core term
* `Voice.Coding` — synthetic, analytic or uncoded
* `Voice` — the initial and derived frames with their slot
  correspondence, the pivot and the marker
* `Voice.image`, `fate`, `fateOfRole`, `introduced`, `newParticipant` —
  the derived participant bookkeeping
* `Voice.Nucleativizes`, `Denucleativizes`, `IsValencyIncreasing`,
  `IsValencyDecreasing`, `Cumulates`, `IsSymmetrical`, `IsImpersonal`,
  `pivotRole`, `SelectsOblique` — the derived classification
* `Voice.coding`, `IsCoded` — the coding read off the marker
* `Voice.marked` — the voice with a marker
* `Voice.refl` — the trivial voice of a frame with itself
* `Voice.active`, `passive`, `impersonalPassive`, `antipassive`,
  `anticausative`, `causative`, `reflexive`, `reciprocal`, `applicative`,
  `agentVoice`, `patientVoice`, `obliqueVoice`, `locativeVoice` — the voices
* `Verb.Alternates` — a verb has frames refining both frames of a voice
* `Voice.Alignment` — alignment of S with A or with P

## Main results

* `Voice.passive_anticausative_fate` — the passive keeps the initial A in
  participant structure, the anticausative suppresses it
* `Voice.impersonalPassive_isImpersonal`, `passive_not_isImpersonal` — the
  impersonal passive privileges no term
* `Voice.isSymmetrical_refl` — the trivial voice neither nucleativizes nor
  denucleativizes
* `Voice.coding_eq_uncoded_iff` — a voice is uncoded exactly when it has no
  marker

## Implementation notes

A slot of the initial frame with no correspondent is suppressed from
participant structure; one whose correspondent is an implicit or an
adpositional position is denucleativized but maintained; two initial core
terms with one correspondent are cumulated. The derived frame of a passive
records the demoted agent as implicit, the canonical short passive. The pivot
defaults to the first core slot of the derived construction, its S or A, and
`none` for an impersonal construction; only the symmetrical voices set it.
The marker is the segmental material coding the voice, in surface order, and
[creissels-2024]'s coding types are read off it: synthetic when every morph is
bound, analytic when a free morph, an auxiliary, is among them, uncoded when it
is empty; a zero-marked voice, told from the initial construction by its
inflection alone, has the empty marker. The marker is a per-language datum with
no bearing on the classification, so the constants are unmarked and a fragment
supplies it. [creissels-2024]'s names for
the alternations are processes, passivization and the rest; the constants here
are the voices, and his typology keeps its vocabulary in his study. Within
`Syntax/Voice/` this file owns a voice; `System.lean` owns a language's set
of voices.

## References

* [comrie-1989]
* [creissels-2024]
* [dixon-1994]
* [dixon-aikhenvald-2000]
* [song-1996]
-/

namespace Voice

/-! ### Transitivity-related roles -/

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

/-- What a voice does to a core term of the initial construction. -/
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

/-! ### Coding -/

/-- How a voice is coded on the verb: by verbal morphology, by an analytic construction, or
not at all, the unmarked voice of a system or a flexivalent alternation ([creissels-2024]
§1.1.3). Equipollence is a property of a system, `Voice.Equipollent`. -/
inductive Coding where
  | synthetic
  | analytic
  | uncoded
  deriving DecidableEq, Repr

/-- The coding type of a marker: uncoded when empty, synthetic when every morph is bound,
analytic otherwise. -/
def Coding.ofMarker (ms : List Morphology.Morph) : Coding :=
  if ms = [] then .uncoded
  else if ms.all fun m ↦ m.kind.side?.isSome then .synthetic
  else .analytic

end Voice

/-- A voice: the initial and the derived argument frame, the slot of the derived frame each
slot of the initial frame's participant occupies, the derived slot that is the pivot, and
the marker on the verb. -/
@[ext]
structure Voice where
  /-- The initial construction. -/
  source : ArgumentFrame
  /-- The derived construction. -/
  target : ArgumentFrame
  /-- The derived slot each initial slot's participant occupies; an initial slot without an
      entry is suppressed from participant structure. -/
  correspondence : List (ArgumentFrame.Slot × ArgumentFrame.Slot)
  /-- The syntactically privileged term of the derived construction: its first core slot, S
      or A, unless a symmetrical voice selects another; `none` for an impersonal
      construction ([creissels-2024] §8.1.7). -/
  pivot : Option ArgumentFrame.Slot := target.coreSlots.head?
  /-- The morphs coding the voice on the verb, in surface order: affixes, an auxiliary, or
      none for a zero-marked or an unmarked voice. -/
  marker : List Morphology.Morph := []
  deriving DecidableEq, Repr

namespace Voice

open ArgumentFrame (Slot)

variable (v : Voice)

/-! ### Participant bookkeeping -/

/-- The derived slot an initial slot's participant occupies. -/
def image (s : Slot) : Option Slot := v.correspondence.lookup s

/-- The initial slots whose participant occupies a derived slot. -/
def preimages (t : Slot) : List Slot :=
  v.source.slots.filter fun s ↦ v.image s == some t

/-- The transitivity-related role of a derived slot: the coding role of a core slot, X for an
expressed oblique, none for an implicit or expletive position. -/
def targetRole (t : Slot) : Option TermRole :=
  match v.target.codingRole t, v.target.get? t with
  | some r, _ => some (TermRole.ofArgumentRole r)
  | none, some p => if p.IsExpressed then some .X else none
  | none, none => none

/-- The fate of an initial slot: suppressed without a correspondent; cumulated when another
initial core term shares its derived core slot; maintained in a derived core slot;
denucleativized otherwise; not applicable to a non-core initial slot. -/
def fate (s : Slot) : ParticipantFate :=
  if s ∈ v.source.coreSlots then
    match v.image s with
    | none => .suppressed
    | some t =>
      if t ∈ v.target.coreSlots then
        if (v.preimages t).any (fun s' ↦ s' != s && s' ∈ v.source.coreSlots) then .cumulated
        else .maintained
      else .denucleativized
  else .na

/-- The fate of the initial core term with a transitivity-related role. -/
def fateOfRole (r : TermRole) : ParticipantFate :=
  match v.source.coreSlots.find? fun s ↦
      (v.source.codingRole s).map TermRole.ofArgumentRole == some r with
  | some s => v.fate s
  | none => .na

/-- The derived slots the derived construction introduces: expressed slots whose participant
was not a core term of the initial construction, either new to it or nucleativized from a
non-core slot. -/
def introduced : List Slot :=
  v.target.slots.filter fun t ↦
    (v.targetRole t).isSome &&
      (v.preimages t).all fun s ↦ s ∉ v.source.coreSlots && t ∈ v.target.coreSlots

/-- The role of the participant the derived construction introduces, if one. -/
def newParticipant : Option TermRole := v.introduced.head?.bind v.targetRole

/-- The transitivity-related role of the pivot: S, A or P for a core term, X for an
oblique. -/
def pivotRole : Option TermRole := v.pivot.bind v.targetRole

/-! ### Classification -/

/-- Some participant becomes a core term. -/
def Nucleativizes : Prop := ∃ t ∈ v.introduced, t ∈ v.target.coreSlots

/-- Some initial core term ceases to be one. -/
def Denucleativizes : Prop :=
  ∃ s ∈ v.source.coreSlots, (v.fate s).RemovesFromCoreStatus

/-- Two initial core terms are cumulated. -/
def Cumulates : Prop := ∃ s ∈ v.source.coreSlots, v.fate s = .cumulated

/-- Valency-increasing: nucleativizes without denucleativizing. -/
def IsValencyIncreasing : Prop := v.Nucleativizes ∧ ¬ v.Denucleativizes

/-- Valency-decreasing: denucleativizes without nucleativizing. -/
def IsValencyDecreasing : Prop := v.Denucleativizes ∧ ¬ v.Nucleativizes

/-- Symmetrical: the voice neither nucleativizes nor denucleativizes, so it does not affect
the transitivity of the construction ([creissels-2024] §8.1.7). -/
def IsSymmetrical : Prop := ¬ v.Nucleativizes ∧ ¬ v.Denucleativizes

/-- The pivot is an oblique, the selection a binary system does not allow
([creissels-2024] §8.5.2). -/
def SelectsOblique : Prop := v.pivotRole = some .X

/-- No term is privileged: an impersonal construction ([creissels-2024] §8.3.2.2). -/
def IsImpersonal : Prop := v.pivot = none

/-- The coding type of the voice, read off its marker ([creissels-2024] §1.1.3). -/
def coding : Coding := .ofMarker v.marker

/-- Coded on the verb: a voice as against flexivalency ([creissels-2024] §1.1.3). -/
def IsCoded : Prop := v.marker ≠ []

instance : Decidable v.Nucleativizes := inferInstanceAs (Decidable (∃ _ ∈ _, _))
instance : Decidable v.Denucleativizes := inferInstanceAs (Decidable (∃ _ ∈ _, _))
instance : Decidable v.Cumulates := inferInstanceAs (Decidable (∃ _ ∈ _, _))
instance : Decidable v.IsValencyIncreasing := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable v.IsValencyDecreasing := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable v.IsSymmetrical := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable v.SelectsOblique := inferInstanceAs (Decidable (_ = _))
instance : Decidable v.IsImpersonal := inferInstanceAs (Decidable (_ = _))
instance : Decidable v.IsCoded := inferInstanceAs (Decidable (_ ≠ _))

/-! ### Marking -/

/-- The voice with the given marker. -/
def marked (ms : List Morphology.Morph) : Voice := { v with marker := ms }

@[simp] theorem marker_marked (ms : List Morphology.Morph) : (v.marked ms).marker = ms := rfl

@[simp] theorem source_marked (ms : List Morphology.Morph) : (v.marked ms).source = v.source :=
  rfl

@[simp] theorem target_marked (ms : List Morphology.Morph) : (v.marked ms).target = v.target :=
  rfl

theorem coding_eq_uncoded_iff : v.coding = .uncoded ↔ v.marker = [] := by
  unfold coding Coding.ofMarker
  split_ifs <;> simp_all

theorem isCoded_iff : v.IsCoded ↔ v.coding ≠ .uncoded := by
  rw [IsCoded, Ne, Ne, coding_eq_uncoded_iff]

variable {v}

theorem IsValencyIncreasing.not_isSymmetrical (h : v.IsValencyIncreasing) :
    ¬ v.IsSymmetrical := fun h' ↦ h'.1 h.1

theorem IsValencyDecreasing.not_isSymmetrical (h : v.IsValencyDecreasing) :
    ¬ v.IsSymmetrical := fun h' ↦ h'.2 h.1

/-! ### The trivial voice -/

/-- The trivial voice of a frame with itself: the initial construction of a system. -/
def refl (fr : ArgumentFrame) : Voice :=
  { source := fr, target := fr, correspondence := fr.slots.map fun s ↦ (s, s) }

private theorem lookup_map_diag {β : Type*} [DecidableEq β] {l : List β} {a : β} (h : a ∈ l) :
    (l.map fun x ↦ (x, x)).lookup a = some a := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    simp only [List.map_cons, List.lookup_cons]
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · split
      · rename_i hx; rw [beq_iff_eq] at hx; subst hx; rfl
      · exact ih h

@[simp] theorem source_refl (fr : ArgumentFrame) : (refl fr).source = fr := rfl

@[simp] theorem target_refl (fr : ArgumentFrame) : (refl fr).target = fr := rfl

theorem image_refl {fr : ArgumentFrame} {s : Slot} (h : s ∈ fr.slots) :
    (refl fr).image s = some s :=
  lookup_map_diag h

theorem image_refl_eq_some_iff {fr : ArgumentFrame} {s t : Slot} (h : s ∈ fr.slots) :
    (refl fr).image s = some t ↔ s = t := by
  rw [image_refl h, Option.some.injEq]

/-- The trivial voice is symmetrical. -/
theorem isSymmetrical_refl (fr : ArgumentFrame) : (refl fr).IsSymmetrical := by
  refine ⟨fun ⟨t, ht, htc⟩ ↦ ?_, fun ⟨s, hs, hf⟩ ↦ ?_⟩
  · simp only [introduced, List.mem_filter, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq] at ht
    have ht₁ : t ∈ fr.slots := ht.1
    have hp : t ∈ (refl fr).preimages t := by
      simp only [preimages, List.mem_filter, image_refl ht₁, beq_self_eq_true, and_true]
      exact ht₁
    exact (ht.2.2 t hp).1 htc
  · have hsl : s ∈ fr.slots := List.mem_of_mem_filter hs
    have hs' : s ∈ fr.coreSlots := hs
    simp only [fate, source_refl, target_refl, hs', image_refl hsl, ite_true] at hf
    split at hf <;> simp [ParticipantFate.RemovesFromCoreStatus] at hf

/-! ### The voices -/

open ArgumentFrame.Slot

/-- The active: the initial transitive construction. -/
def active : Voice := refl .np

/-- The agent voice of a symmetrical system, the agent the pivot: the active. -/
abbrev agentVoice : Voice := active

/-- The passive of a frame, the transitive one by default: the external argument is
denucleativized but maintained in participant structure, implied here and expressed as an
oblique in a long passive, and the first complement is the pivot ([creissels-2024]
§8.3.2.1). -/
def passive (fr : ArgumentFrame := .np) : Voice :=
  { source := fr, target := ⟨none, fr.complements ++ [.implicit]⟩,
    correspondence := (external, complement fr.complements.length) ::
      (List.range fr.complements.length).map fun i ↦ (complement i, complement i) }

/-- The impersonal passive: the passive whose derived construction privileges no term, the
initial P keeping its coding ([creissels-2024] §8.3.2.2); of an intransitive frame, the
denucleativization of its S (§8.3.2.4). -/
def impersonalPassive (fr : ArgumentFrame := .np) : Voice := { passive fr with pivot := none }

/-- The antipassive: the initial P is denucleativized and the initial A is the S of an
intransitive construction ([creissels-2024] §8.3.2.3). -/
def antipassive : Voice :=
  { source := .np, target := .pp,
    correspondence := [(external, external), (complement 0, complement 0)] }

/-- The anticausative: the initial A is suppressed from participant structure and the
initial P is the S of an intransitive construction; [creissels-2024]'s decausativization
(§8.3.1.2). -/
def anticausative : Voice :=
  { source := .np, target := .unaccusative, correspondence := [(complement 0, complement 0)] }

/-- The causative: a causer is nucleativized as the A of a transitive construction whose P is
the initial S ([creissels-2024] §8.3.1.1). -/
def causative : Voice :=
  { source := .intransitive, target := .np, correspondence := [(external, complement 0)] }

/-- The reflexive: the initial A and P are cumulated in one S ([creissels-2024] §8.3.3). -/
def reflexive : Voice :=
  { source := .np, target := .intransitive,
    correspondence := [(external, external), (complement 0, external)] }

/-- The reciprocal: the reflexive with a group reading ([creissels-2024] §8.3.3). -/
abbrev reciprocal : Voice := reflexive

/-- The applicative: an applied participant is nucleativized as a second P beside the
initial A and P ([creissels-2024] §8.3.5). -/
def applicative : Voice :=
  { source := .np, target := .np_np,
    correspondence := [(external, external), (complement 0, complement 0)] }

/-- The patient voice of a symmetrical system: the transitive construction unchanged, the
patient the pivot ([creissels-2024] §8.5.1). -/
def patientVoice : Voice := { refl .np with pivot := some (complement 0) }

/-- An oblique voice of a multiple symmetrical system: the transitive construction with an
oblique of relation `r` unchanged, the oblique the pivot ([creissels-2024] §8.5.2). -/
def obliqueVoice (r : Adposition.RelationType) : Voice :=
  { refl ⟨some .nominal, [.nominal, .adpositional (some r)]⟩ with pivot := some (complement 1) }

/-- The locative voice: the oblique voice of a spatial oblique. -/
abbrev locativeVoice : Voice := obliqueVoice .spatial

/-! ### Properties of the voices -/

theorem causative_isValencyIncreasing : causative.IsValencyIncreasing := by decide

theorem anticausative_isValencyDecreasing : anticausative.IsValencyDecreasing := by decide

theorem passive_isValencyDecreasing : passive.IsValencyDecreasing := by decide

/-- The passive maintains the initial A in participant structure; the anticausative
suppresses it ([creissels-2024] §8.3.2.1). -/
theorem passive_anticausative_fate :
    passive.fateOfRole .A = .denucleativized ∧ anticausative.fateOfRole .A = .suppressed := by
  decide

theorem impersonalPassive_isImpersonal (fr : ArgumentFrame) :
    (impersonalPassive fr).IsImpersonal := rfl

theorem passive_not_isImpersonal : ¬ passive.IsImpersonal := by decide

theorem antipassive_isValencyDecreasing : antipassive.IsValencyDecreasing := by decide

theorem reflexive_cumulates : reflexive.Cumulates := by decide

theorem applicative_isValencyIncreasing : applicative.IsValencyIncreasing := by decide

theorem patientVoice_isSymmetrical : patientVoice.IsSymmetrical := isSymmetrical_refl _

theorem obliqueVoice_isSymmetrical (r : Adposition.RelationType) :
    (obliqueVoice r).IsSymmetrical := isSymmetrical_refl _

theorem obliqueVoice_selectsOblique (r : Adposition.RelationType) :
    (obliqueVoice r).SelectsOblique := by cases r <;> decide

/-! ### Alternating verbs -/

/-- The verb alternates by `v`: some frame of its refines the initial frame and some the
derived frame. Necessary for the alternation, not sufficient, since the two frames need not be
related by it. -/
def _root_.Verb.Alternates (w : Verb) (v : Voice) : Prop :=
  (∃ fr ∈ w.frames, v.source ≤ fr) ∧ ∃ fr ∈ w.frames, v.target ≤ fr

instance (w : Verb) (v : Voice) : Decidable (w.Alternates v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Alignment -/

/-- The alignment of the core terms of transitive and intransitive clauses: S coded like A,
or like P ([creissels-2024] §1.3.4). -/
inductive Alignment where
  /-- S is coded like A, traditionally accusative. -/
  | A_alignment
  /-- S is coded like P, traditionally ergative. -/
  | P_alignment
  deriving DecidableEq, Repr

end Voice
