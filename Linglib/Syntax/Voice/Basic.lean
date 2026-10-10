module

public import Linglib.Syntax.Category.Verb.Defs
public import Linglib.Morphology.Morph

/-!
# Voice

A construction of a verb gives each of its participants a status: a nominal term with a
transitivity-related role, a dative oblique, an implied participant, or none. A voice relates
two argument frames of one predicate by a correspondence between their slots, and so an initial
and a derived construction over its participants. What a grammar says of a voice is read off
that pair: the fate of each initial core term, whether a participant is nucleativized or
denucleativized and so whether valency increases or decreases, and whether the voice only
selects a pivot. A voice also records its pivot, the derived slot that is the syntactically
privileged term, and the marker by which the verb codes it; a fragment states a voice with its
marker, `Voice.passive.marked [.suff "x"]`, and the bare constants are unmarked.

## Main definitions

* `Voice.Status`, `Voice.Construction`: a participant's status, and a construction.
* `Voice.Construction.Nucleativized`, `Denucleativized`, `fate`: an initial construction
  compared with a derived one.
* `Voice`: two frames with their slot correspondence, the pivot and the marker.
* `Voice.initial`, `Voice.derived`: the constructions a voice relates.
* `Voice.passive`, `antipassive`, `anticausative`, `causative`, `reflexive`, `applicative`,
  `patientVoice`, `obliqueVoice`: the voices.

## Main statements

* `Voice.Construction.valency_eq_of_nucleativized_of_denucleativized`: nucleativization is not
  valency increase.
* `Voice.passive_anticausative_fate`: the passive keeps the initial A in participant structure,
  the anticausative suppresses it.
* `Voice.isSymmetrical_refl`: the trivial voice neither nucleativizes nor denucleativizes.

## Implementation notes

* The participants of a voice are those of the initial slots and those of the derived slots no
  initial slot corresponds to, expletives aside; an initial slot without a correspondent is
  absent from the derived construction.
* A frame's sole core term counts as S, so a frame cannot code a P without an A as an
  impersonal construction does; `IsImpersonal` reads impersonality off the pivot, which defaults
  to the first core slot and is `none` for an impersonal construction.
* The marker is the segmental material coding the voice, in surface order, and the coding type
  is read off it: synthetic when every morph is bound, analytic when a free morph, an
  auxiliary, is among them, uncoded when it is empty.
* The names of the alternations as processes, passivization and the rest, are predicates on
  pairs of constructions in `Studies/Creissels2024.lean`; the constants here are the voices.

## References

* [comrie-1989]
* [creissels-2024]
* [dixon-1994]
* [dixon-aikhenvald-2000]
* [song-1996]
-/

@[expose] public section

namespace Voice

/-! ### Transitivity-related roles -/

/-- The role of a nominal term in [creissels-2024]'s binary core-term system is one of the
core roles S, A and P, or X for an oblique. -/
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

/-- The transitivity-related role of a comparative coding role, under which recipients and
themes are P-like core terms. -/
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

/-! ### Constructions -/

/-- A construction expresses a potential participant of its verb as a nominal term with a
transitivity-related role or as a dative oblique, leaves it implied but unexpressed, or has it
outside participant structure. -/
inductive Status where
  | term (r : TermRole)
  | dative
  | implicit
  | absent
  deriving DecidableEq, Repr

namespace Status

/-- The role of the nominal term, datives counting as obliques. -/
def role : Status → Option TermRole
  | term r => some r
  | dative => some .X
  | _ => none

/-- A participant is nuclear when it is expressed as a core term. -/
def Nuclear : Status → Prop
  | term r => r ≠ .X
  | _ => False

instance : DecidablePred Nuclear := fun s ↦ by cases s <;> unfold Nuclear <;> infer_instance

end Status

/-- A construction of a verb gives each of its potential participants a status. -/
abbrev Construction (ι : Type*) := ι → Status

namespace Construction

variable {ι : Type*} (c d : Construction ι)

/-- A transitive construction has an A term and a P term. -/
def Transitive : Prop := (∃ i, c i = .term .A) ∧ ∃ i, c i = .term .P

/-- An impersonal construction has neither an A term nor an S term. -/
def Impersonal : Prop := ∀ i, c i ≠ .term .A ∧ c i ≠ .term .S

/-- The valency of a construction is its number of nuclear participants. -/
def valency [Fintype ι] : ℕ := (Finset.univ.filter fun i ↦ (c i).Nuclear).card

/-! Comparing an initial construction `c` with a derived construction `d` of the same verb. -/

/-- A participant that is not a core term of the initial construction is one of the derived
construction. -/
def Nucleativized (i : ι) : Prop := ¬ (c i).Nuclear ∧ (d i).Nuclear

/-- A core term of the initial construction is not one of the derived construction. -/
def Denucleativized (i : ι) : Prop := (c i).Nuclear ∧ ¬ (d i).Nuclear

/-- A core term of the initial construction is removed from participant structure. -/
def Suppressed (i : ι) : Prop := (c i).Nuclear ∧ d i = .absent

/-- A participant the initial construction does not express as a core term is expressed, and
differently, by the derived construction. -/
def Introduced (i : ι) : Prop := ¬ (c i).Nuclear ∧ c i ≠ d i ∧ (d i).role.isSome

/-- A core term of the initial construction shares its derived A or S term with another; a
clause has one A and one S, so two participants with either share it. -/
def Cumulated (i : ι) : Prop :=
  (c i).Nuclear ∧ (d i = .term .A ∨ d i = .term .S) ∧ ∃ j, j ≠ i ∧ (c j).Nuclear ∧ d j = d i

/-- Some participant is nucleativized. -/
def Nucleativizes : Prop := ∃ i, c.Nucleativized d i

/-- Some participant is denucleativized. -/
def Denucleativizes : Prop := ∃ i, c.Denucleativized d i

/-- The alternation is valency-increasing when it nucleativizes without denucleativizing. -/
def IsValencyIncreasing : Prop := c.Nucleativizes d ∧ ¬ c.Denucleativizes d

/-- The alternation is valency-decreasing when it denucleativizes without nucleativizing. -/
def IsValencyDecreasing : Prop := c.Denucleativizes d ∧ ¬ c.Nucleativizes d

/-- The alternation is symmetrical when it neither nucleativizes nor denucleativizes, so that
it does not affect the transitivity of the construction ([creissels-2024] §8.1.7). -/
def IsSymmetrical : Prop := ¬ c.Nucleativizes d ∧ ¬ c.Denucleativizes d

theorem isSymmetrical_self : c.IsSymmetrical c := ⟨fun ⟨_, h⟩ ↦ h.1 h.2, fun ⟨_, h⟩ ↦ h.2 h.1⟩

section Fintype

variable [Fintype ι] [DecidableEq ι]

instance : Decidable c.Transitive := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable c.Impersonal := inferInstanceAs (Decidable (∀ _, _))
instance (i : ι) : Decidable (c.Nucleativized d i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ι) : Decidable (c.Denucleativized d i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ι) : Decidable (c.Suppressed d i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ι) : Decidable (c.Introduced d i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ι) : Decidable (c.Cumulated d i) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (c.Nucleativizes d) := inferInstanceAs (Decidable (∃ _, _))
instance : Decidable (c.Denucleativizes d) := inferInstanceAs (Decidable (∃ _, _))
instance : Decidable (c.IsValencyIncreasing d) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (c.IsValencyDecreasing d) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (c.IsSymmetrical d) := inferInstanceAs (Decidable (_ ∧ _))

/-- An initial core term is suppressed when it leaves participant structure, cumulated when it
shares its derived core term with another, maintained when it remains a core term, and
denucleativized otherwise. -/
def fate (i : ι) : ParticipantFate :=
  if (c i).Nuclear then
    if d i = .absent then .suppressed
    else if (d i).Nuclear then if c.Cumulated d i then .cumulated else .maintained
    else .denucleativized
  else .na

/-- Nucleativization is not valency increase: an alternation may nucleativize one participant
and denucleativize another, keeping the valency ([creissels-2024] §8.1.3). -/
theorem valency_eq_of_nucleativized_of_denucleativized {c d : Construction ι} {i j : ι}
    (hi : c.Nucleativized d i) (hj : c.Denucleativized d j)
    (h : ∀ k, k ≠ i → k ≠ j → ((c k).Nuclear ↔ (d k).Nuclear)) : c.valency = d.valency :=
  Finset.card_equiv (Equiv.swap i j) fun k ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hk : k = i
    · subst hk; rw [Equiv.swap_apply_left]; exact iff_of_false hi.1 hj.2
    by_cases hk' : k = j
    · subst hk'; rw [Equiv.swap_apply_right]; exact iff_of_true hj.1 hi.2
    rw [Equiv.swap_apply_of_ne_of_ne hk hk']; exact h k hk hk'

end Fintype

end Construction

/-- The status a frame gives the participant of a slot: the transitivity-related role of a core
slot, X for an expressed oblique, implicit for an implicit position, and absent for an expletive
or an unfilled slot. -/
def _root_.ArgumentFrame.status (fr : ArgumentFrame) (s : ArgumentFrame.Slot) : Status :=
  match fr.codingRole s, fr.get? s with
  | some r, _ => .term (.ofArgumentRole r)
  | none, some (.implicit _) => .implicit
  | none, some p => if p.IsExpressed then .term .X else .absent
  | none, none => .absent

/-! ### Coding -/

/-- A voice is coded on the verb by verbal morphology, by an analytic construction, or not at
all, as the unmarked voice of a system and a flexivalent alternation are ([creissels-2024]
§1.1.3). Equipollence is a property of a system, `Voice.Equipollent`. -/
inductive Coding where
  | synthetic
  | analytic
  | uncoded
  deriving DecidableEq, Repr

/-- A marker is uncoded when empty, synthetic when every morph is bound, and analytic
otherwise. -/
def Coding.ofMarker (ms : List Morphology.Morph) : Coding :=
  if ms = [] then .uncoded
  else if ms.all fun m ↦ m.kind.position?.isSome then .synthetic
  else .analytic

end Voice

/-- A voice is an initial and a derived argument frame, the slot of the derived frame each
slot of the initial frame's participant occupies, the derived slot that is the pivot, and the
marker on the verb. -/
@[ext]
structure Voice where
  /-- The initial construction. -/
  source : ArgumentFrame
  /-- The derived construction. -/
  target : ArgumentFrame
  /-- The derived slot each initial slot's participant occupies; an initial slot without an
      entry is suppressed from participant structure. -/
  correspondence : List (ArgumentFrame.Slot × ArgumentFrame.Slot)
  /-- The pivot is the syntactically privileged term of the derived construction, its first
      core slot, S or A, unless a symmetrical voice selects another; it is `none` for an
      impersonal construction ([creissels-2024] §8.1.7). -/
  pivot : Option ArgumentFrame.Slot := target.coreSlots.head?
  /-- The marker lists the morphs coding the voice on the verb in surface order, affixes or an
      auxiliary, and is empty for a zero-marked or an unmarked voice. -/
  marker : List Morphology.Morph := []
  deriving DecidableEq, Repr

namespace Voice

open ArgumentFrame (Slot)

variable (v : Voice)

/-! ### The constructions of a voice -/

/-- The derived slot an initial slot's participant occupies. -/
def image (s : Slot) : Option Slot := v.correspondence.lookup s

/-- The initial slots whose participant occupies a derived slot. -/
def preimages (t : Slot) : List Slot :=
  v.source.slots.filter fun s ↦ v.image s == some t

/-- The derived slots of the participants the derived construction adds: those no initial
slot's participant occupies, expletives aside. -/
def newSlots : List Slot :=
  v.target.slots.filter fun t ↦ v.preimages t = [] ∧ v.target.status t ≠ .absent

/-- The participants of a voice are those of the initial slots and those of the new derived
slots. -/
def participants : List (Slot ⊕ Slot) :=
  v.source.slots.map .inl ++ v.newSlots.map .inr

/-- A participant of the voice. -/
abbrev Participant : Type := {p // p ∈ v.participants}

/-- The initial construction: a participant of an initial slot has its status there, and a
new participant is absent. -/
def initial : Construction v.Participant := fun p ↦ p.1.elim v.source.status fun _ ↦ .absent

/-- The derived construction: a participant of an initial slot has the status of the slot it
occupies, absent if none, and a new participant that of its own slot. -/
def derived : Construction v.Participant :=
  fun p ↦ p.1.elim (fun s ↦ (v.image s).elim .absent v.target.status) v.target.status

/-- The fate of the participant of an initial slot. -/
def fate (s : Slot) : ParticipantFate :=
  if h : s ∈ v.source.slots then
    Construction.fate v.initial v.derived ⟨.inl s, by simp [participants, h]⟩
  else .na

/-- The fate of the initial core term with a transitivity-related role. -/
def fateOfRole (r : TermRole) : ParticipantFate :=
  match v.source.coreSlots.find? fun s ↦
      (v.source.codingRole s).map TermRole.ofArgumentRole == some r with
  | some s => v.fate s
  | none => .na

/-- The role of the first participant the derived construction introduces, if one. -/
def newParticipant : Option TermRole :=
  (v.participants.attach.find? fun p ↦ v.initial.Introduced v.derived p).bind
    fun p ↦ (v.derived p).role

/-- The transitivity-related role of the pivot is S, A or P for a core term and X for an
oblique. -/
def pivotRole : Option TermRole := v.pivot.bind fun t ↦ (v.target.status t).role

/-! ### Classification -/

/-- Some participant becomes a core term. -/
def Nucleativizes : Prop := v.initial.Nucleativizes v.derived

/-- Some initial core term ceases to be one. -/
def Denucleativizes : Prop := v.initial.Denucleativizes v.derived

/-- Two initial core terms are cumulated. -/
def Cumulates : Prop := ∃ p, v.initial.Cumulated v.derived p

/-- A voice is valency-increasing when it nucleativizes without denucleativizing. -/
def IsValencyIncreasing : Prop := v.initial.IsValencyIncreasing v.derived

/-- A voice is valency-decreasing when it denucleativizes without nucleativizing. -/
def IsValencyDecreasing : Prop := v.initial.IsValencyDecreasing v.derived

/-- A voice is symmetrical when it neither nucleativizes nor denucleativizes. -/
def IsSymmetrical : Prop := v.initial.IsSymmetrical v.derived

/-- The pivot is an oblique, the selection a binary system does not allow
([creissels-2024] §8.5.2). -/
def SelectsOblique : Prop := v.pivotRole = some .X

/-- A voice is impersonal when its derived construction privileges no term ([creissels-2024]
§8.3.2.2). -/
def IsImpersonal : Prop := v.pivot = none

/-- The coding type of the voice, read off its marker ([creissels-2024] §1.1.3). -/
def coding : Coding := .ofMarker v.marker

/-- A voice is coded when it is marked on the verb, as against a flexivalent alternation
([creissels-2024] §1.1.3). -/
def IsCoded : Prop := v.marker ≠ []

instance : Decidable v.Nucleativizes := inferInstanceAs (Decidable (Construction.Nucleativizes ..))
instance : Decidable v.Denucleativizes :=
  inferInstanceAs (Decidable (Construction.Denucleativizes ..))
instance : Decidable v.Cumulates := inferInstanceAs (Decidable (∃ _, _))
instance : Decidable v.IsValencyIncreasing :=
  inferInstanceAs (Decidable (Construction.IsValencyIncreasing ..))
instance : Decidable v.IsValencyDecreasing :=
  inferInstanceAs (Decidable (Construction.IsValencyDecreasing ..))
instance : Decidable v.IsSymmetrical := inferInstanceAs (Decidable (Construction.IsSymmetrical ..))
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

/-- The trivial voice of a frame with itself is the initial construction of a system. -/
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

theorem derived_refl (fr : ArgumentFrame) : (refl fr).derived = (refl fr).initial := by
  funext ⟨p, hp⟩
  simp only [participants, newSlots, source_refl, target_refl, List.mem_append, List.mem_map,
    List.mem_filter, decide_eq_true_eq] at hp
  rcases hp with ⟨s, hs, rfl⟩ | ⟨t, ⟨ht, hpre⟩, rfl⟩
  · simp [derived, initial, image_refl hs]
  · have : t ∈ (refl fr).preimages t := by
      simp only [preimages, List.mem_filter, image_refl ht, beq_self_eq_true, and_true]
      exact ht
    simp [hpre] at this

/-- The trivial voice is symmetrical. -/
theorem isSymmetrical_refl (fr : ArgumentFrame) : (refl fr).IsSymmetrical := by
  rw [IsSymmetrical, derived_refl]
  exact Construction.isSymmetrical_self _

/-! ### The voices -/

open ArgumentFrame.Slot

/-- The active is the initial transitive construction. -/
def active : Voice := refl .np

/-- The agent voice of a symmetrical system, with the agent the pivot, is the active. -/
abbrev agentVoice : Voice := active

/-- The passive of a frame, the transitive one by default, denucleativizes the external
argument but maintains it in participant structure, implied here and expressed as an oblique in
a long passive, and makes the first complement the pivot ([creissels-2024] §8.3.2.1). -/
def passive (fr : ArgumentFrame := .np) : Voice :=
  { source := fr, target := ⟨none, fr.complements ++ [.implicit]⟩,
    correspondence := (external, complement fr.complements.length) ::
      (List.range fr.complements.length).map fun i ↦ (complement i, complement i) }

/-- The impersonal passive is the passive with no pivot, its derived construction privileging no
term because the initial P keeps its coding ([creissels-2024] §8.3.2.2), which the frame, its
sole core term counting as S, does not record; of an intransitive frame, it denucleativizes the
S (§8.3.2.4). -/
def impersonalPassive (fr : ArgumentFrame := .np) : Voice := { passive fr with pivot := none }

/-- The antipassive denucleativizes the initial P and makes the initial A the S of an
intransitive construction ([creissels-2024] §8.3.2.3). -/
def antipassive : Voice :=
  { source := .np, target := .pp,
    correspondence := [(external, external), (complement 0, complement 0)] }

/-- The anticausative suppresses the initial A from participant structure and makes the
initial P the S of an intransitive construction, [creissels-2024]'s decausativization
(§8.3.1.2). -/
def anticausative : Voice :=
  { source := .np, target := .unaccusative, correspondence := [(complement 0, complement 0)] }

/-- The causative nucleativizes a causer as the A of a transitive construction whose P is the
initial S ([creissels-2024] §8.3.1.1). -/
def causative : Voice :=
  { source := .intransitive, target := .np, correspondence := [(external, complement 0)] }

/-- The reflexive cumulates the initial A and P in one S ([creissels-2024] §8.3.3). -/
def reflexive : Voice :=
  { source := .np, target := .intransitive,
    correspondence := [(external, external), (complement 0, external)] }

/-- The reciprocal is the reflexive with a group reading ([creissels-2024] §8.3.3). -/
abbrev reciprocal : Voice := reflexive

/-- The applicative nucleativizes an applied participant as a second P beside the initial A
and P ([creissels-2024] §8.3.5). -/
def applicative : Voice :=
  { source := .np, target := .np_np,
    correspondence := [(external, external), (complement 0, complement 0)] }

/-- The patient voice of a symmetrical system leaves the transitive construction unchanged and
makes the patient the pivot ([creissels-2024] §8.5.1). -/
def patientVoice : Voice := { refl .np with pivot := some (complement 0) }

/-- An oblique voice of a multiple symmetrical system leaves the transitive construction with
an oblique marking a case of type `r` unchanged and makes the oblique the pivot
([creissels-2024] §8.5.2). -/
def obliqueVoice (r : Case.Kind) : Voice :=
  { refl ⟨some .nominal, [.nominal, .adpositional (some r)]⟩ with pivot := some (complement 1) }

/-- The locative voice is the oblique voice of a spatial oblique. -/
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

theorem obliqueVoice_isSymmetrical (r : Case.Kind) :
    (obliqueVoice r).IsSymmetrical := isSymmetrical_refl _

theorem obliqueVoice_selectsOblique (r : Case.Kind) :
    (obliqueVoice r).SelectsOblique := by cases r <;> decide

/-! ### Alternating verbs -/

/-- The verb alternates by `v` when some frame of its refines the initial frame and some the
derived frame. Necessary for the alternation, not sufficient, since the two frames need not be
related by it. -/
def _root_.Verb.Alternates (w : Verb) (v : Voice) : Prop :=
  (∃ fr ∈ w.frames, v.source ≤ fr) ∧ ∃ fr ∈ w.frames, v.target ≤ fr

instance (w : Verb) (v : Voice) : Decidable (w.Alternates v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Alignment -/

/-- The alignment of the core terms of transitive and intransitive clauses codes S like A or
like P ([creissels-2024] §1.3.4). -/
inductive Alignment where
  /-- S is coded like A, traditionally accusative. -/
  | A_alignment
  /-- S is coded like P, traditionally ergative. -/
  | P_alignment
  deriving DecidableEq, Repr

end Voice
