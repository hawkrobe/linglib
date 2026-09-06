import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Voice.Alternation
import Linglib.Syntax.Voice.Basic
import Linglib.Data.Examples.Creissels2024

/-!
# Creissels's typology of transitivity, valency and voice

The nominal terms of a clause bear transitivity-related roles defined by coding rather than
by meaning: A and P are the two terms coded like the agent and the patient of a prototypical
transitive verb; S is the term of an intransitive clause coded like the sole argument of
monovalent verbs; every other nominal term is an oblique, a dative oblique where recipients
are coded apart from patients. A construction of a verb assigns each of the verb's potential
participants a nominal term with one of these roles, leaves it implied but unexpressed, or
has it outside participant structure altogether, and a valency alternation is a relation
between two constructions of the same verb. Where verbal morphology marks the alternation
it is a voice alternation and the morphologically simpler, or semantically unmarked,
construction is the initial one; where nothing marks it the verb is flexivalent, and a change
of transitivity without marking is ambitransitivity. Two operations characterise oriented
alternations: nucleativization, a participant that is not a core term of the initial
construction becomes one, and denucleativization, a core term of the initial construction is
not one of the derived construction, whether it remains implied or is suppressed from
participant structure. The main types are defined from them. Passivization, its impersonal
variant, antipassivization and S-denucleativization denucleativize one core term without
suppressing it and nucleativize nothing; decausativization suppresses the initial A; an
A-nucleativization makes a new participant the A or S and codes the initial A or S as P or
denucleativizes it, whether the new participant is a causer, causativization in the narrow
sense, an instrument, or a concernee; reflexivization and reciprocalization cumulate two
participant roles in one S; applicativization keeps the initial A or S and adds an applied
phrase, as P, as a dative or as an ordinary oblique, for a participant the initial
construction could not code that way; portative derivation makes the initial S the A of a
transitive construction whose P is a carried entity. Nucleativization is not valency
increase, since a participant may be nucleativized while another is denucleativized. One
marker commonly codes several types, and markers may stack compositionally, the composite
alternation being the composition of its parts, subject to language-particular restrictions
and non-compositional readings. Symmetrical voices, the pivot-prominent systems of Western
Austronesian and of a few languages elsewhere, select a participant as pivot without
nucleativizing or denucleativizing anything and so fall outside the typology. Transitive
and intransitive constructions align in coding, S coded like A or like P, and the
Obligatory Coding Principle, one coding assigned by every verb to one of its participants,
reformulates the accusative and ergative types as obligatory A-coding and obligatory
P-coding, which split-S languages violate. The book's examples are the rows of
`Data/Examples/Creissels2024.json`.

## Implementation notes

* A construction over a finite type of potential participants sends each to a status: a
  nominal term with the substrate's transitivity-related role, a dative oblique, implied but
  unexpressed, or absent from participant structure. Statuses record coding, so the sole
  P-coded term of an impersonal construction keeps the status P although the clause has no
  A. The alternation types are predicates on pairs of constructions, with the nucleativized
  or applied participant as a parameter where the definition singles one out. The semantic
  conditions that separate causativization from the A-nucleativization of an instrument or
  a concernee, or reflexivization from reciprocalization, are not modelled: the three
  A-nucleativizations are one predicate and the rows carry the book's label.
* The substrate's summary records of the alternation types, indexed by the fate of the
  initial A, P and S, are not redefined: a record describes a pair of constructions when the
  fates computed from the pair agree with its fields, and the book's defining example of
  each type is shown to be described by the corresponding record.
* Stacking is composition of relations, and valency is the number of nuclear participants.
* Alignment and the Obligatory Coding Principle are stated over the flagging of S in the
  book's intransitive examples; the book's principle ranges over every verb's coding frame,
  and its examples also show indexation.

## TODO

* Chapters 2 to 7 on participant coding, transitivity prominence, impersonal constructions
  and trivalent verbs, and chapters 9 to 17 beyond their definitions, are not modelled.
* The potential-participant condition on nucleativization, which excludes the Yupik
  believer derivation from voice; inflectional and equipollent voice systems; the
  non-compositional readings of stacked markers; and the diachronic scenarios are prose.
* The substrate's records fix an intransitive base for causativization and an intransitive
  derived construction for passivization and antipassivization, which the Balinese
  causative (51), the Tswana passive (38f) and the Nahuatl antipassive (39c) do not have;
  the records describe the defining examples only.

## References

* [D. Creissels, *Transitivity, Valency, and Voice* (2024)][creissels-2024]
* [N. N. Bahrt, *Voice Syncretism* (2021)][bahrt-2021]
-/

namespace Creissels2024

open Voice Data.Examples

/-! ### Constructions and transitivity-related roles (§1.3) -/

/-- What a construction does with a potential participant of the verb: expresses it as a
nominal term with a transitivity-related role, as a dative oblique, leaves it implied but
unexpressed, or has it outside participant structure. -/
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

/-- A nuclear participant: one expressed as a core term. -/
def Nuclear : Status → Prop
  | term r => r ≠ .X
  | _ => False

/-- In participant structure. -/
def Present (s : Status) : Prop := s ≠ absent

/-- Expressed by a nominal term. -/
def Expressed (s : Status) : Prop := s.role.isSome

instance : DecidablePred Nuclear := λ s => by cases s <;> unfold Nuclear <;> infer_instance
instance : DecidablePred Present := λ s => by unfold Present; infer_instance
instance : DecidablePred Expressed := λ s => by unfold Expressed; infer_instance

end Status

/-- A construction of a verb over its potential participants. -/
abbrev Construction (ι : Type*) := ι → Status

variable {ι : Type*}

namespace Construction

/-- A transitive construction has an A term and a P term. -/
def Transitive (c : Construction ι) : Prop := (∃ i, c i = .term .A) ∧ ∃ i, c i = .term .P

/-- An impersonal construction has neither an A term nor an S term. -/
def Impersonal (c : Construction ι) : Prop := ∀ i, c i ≠ .term .A ∧ c i ≠ .term .S

section
variable [Fintype ι] [DecidableEq ι]

/-- The valency of a construction: its number of nuclear participants. -/
def valency (c : Construction ι) : ℕ := (Finset.univ.filter λ i => (c i).Nuclear).card

instance (c : Construction ι) : Decidable c.Transitive := by unfold Transitive; infer_instance
instance (c : Construction ι) : Decidable c.Impersonal := by unfold Impersonal; infer_instance

end

end Construction

/-! ### Nucleativization and denucleativization (§8.1.3) -/

/-- A participant that is not a core term of the initial construction is one of the derived
construction. -/
def Nucleativized (c d : Construction ι) (i : ι) : Prop := ¬ (c i).Nuclear ∧ (d i).Nuclear

/-- A core term of the initial construction is not one of the derived construction. -/
def Denucleativized (c d : Construction ι) (i : ι) : Prop := (c i).Nuclear ∧ ¬ (d i).Nuclear

/-- A core term of the initial construction is removed from participant structure. -/
def Suppressed (c d : Construction ι) (i : ι) : Prop := (c i).Nuclear ∧ d i = .absent

/-- A participant the initial construction does not express as a core term is expressed,
and differently, by the derived construction. -/
def Introduced (c d : Construction ι) (i : ι) : Prop :=
  ¬ (c i).Nuclear ∧ c i ≠ d i ∧ (d i).Expressed

/-- Some participant is nucleativized. -/
def Nucleativization (c d : Construction ι) : Prop := ∃ i, Nucleativized c d i

/-- Some participant is denucleativized. -/
def Denucleativization (c d : Construction ι) : Prop := ∃ i, Denucleativized c d i

/-- The two constructions imply the same participant roles. -/
def PreservesStructure (c d : Construction ι) : Prop := ∀ i, (c i).Present ↔ (d i).Present

section
variable [Fintype ι] [DecidableEq ι]

instance (c d : Construction ι) (i : ι) : Decidable (Nucleativized c d i) := by
  unfold Nucleativized; infer_instance
instance (c d : Construction ι) (i : ι) : Decidable (Denucleativized c d i) := by
  unfold Denucleativized; infer_instance
instance (c d : Construction ι) (i : ι) : Decidable (Suppressed c d i) := by
  unfold Suppressed; infer_instance
instance (c d : Construction ι) (i : ι) : Decidable (Introduced c d i) := by
  unfold Introduced; infer_instance
instance (c d : Construction ι) : Decidable (Nucleativization c d) := by
  unfold Nucleativization; infer_instance
instance (c d : Construction ι) : Decidable (Denucleativization c d) := by
  unfold Denucleativization; infer_instance
instance (c d : Construction ι) : Decidable (PreservesStructure c d) := by
  unfold PreservesStructure; infer_instance

/-- Nucleativization is not valency increase: a construction may nucleativize one participant
and denucleativize another, keeping its valency, as a causative that codes the initial A as P
and denucleativizes the initial P does. -/
theorem valency_eq_of_nucleativized_denucleativized {c d : Construction ι} {i j : ι}
    (hi : Nucleativized c d i) (hj : Denucleativized c d j)
    (h : ∀ k, k ≠ i → k ≠ j → ((c k).Nuclear ↔ (d k).Nuclear)) : c.valency = d.valency :=
  Finset.card_equiv (Equiv.swap i j) λ k => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hk : k = i
    · subst hk; rw [Equiv.swap_apply_left]; exact iff_of_false hi.1 hj.2
    by_cases hk' : k = j
    · subst hk'; rw [Equiv.swap_apply_right]; exact iff_of_true hj.1 hi.2
    rw [Equiv.swap_apply_of_ne_of_ne hk hk']; exact h k hk hk'

end

/-- A construction nucleativizes none of its own participants. -/
theorem not_nucleativized_self (c : Construction ι) (i : ι) : ¬ Nucleativized c c i :=
  λ h => h.1 h.2

/-- A construction denucleativizes none of its own participants. -/
theorem not_denucleativized_self (c : Construction ι) (i : ι) : ¬ Denucleativized c c i :=
  λ h => h.2 h.1

/-! ### The main types of voice alternation (§8.3) -/

/-- The common core of §8.3.2: a nuclear participant of the initial construction is
denucleativized without being deleted from participant structure, and no participant is
nucleativized. -/
def Demoted (c d : Construction ι) (i : ι) : Prop :=
  Denucleativized c d i ∧ (d i).Present ∧ ¬ Nucleativization c d

/-- Passivization: the initial construction is transitive, its A is demoted but maintained in
participant structure, and its P remains a core term, as S in the canonical case and as the
P of a transitive construction after a double-P construction. -/
def Passivization (c d : Construction ι) : Prop :=
  c.Transitive ∧ (∀ i, c i = .term .A → Demoted c d i) ∧ ∀ i, c i = .term .P → (d i).Nuclear

/-- The impersonal variant of passivization: the initial P keeps its coding, so the derived
construction has neither A nor S. -/
def IPassivization (c d : Construction ι) : Prop := Passivization c d ∧ d.Impersonal

/-- Antipassivization: the initial construction is transitive, participant structure is
unchanged, a P is demoted, and the initial A becomes the S of an intransitive construction,
or keeps the role of A after a double-P construction. -/
def Antipassivization (c d : Construction ι) : Prop :=
  c.Transitive ∧ PreservesStructure c d ∧ (∃ i, c i = .term .P ∧ Demoted c d i) ∧
    ∀ i, c i = .term .A → d i = .term .S ∨ d i = .term .A

/-- S-denucleativization: the initial construction is intransitive and its S is demoted. -/
def SDenucleativization (c d : Construction ι) : Prop :=
  ¬ c.Transitive ∧ (∃ i, c i = .term .S) ∧ ∀ i, c i = .term .S → Demoted c d i

/-- Decausativization: the initial construction is transitive, its A is suppressed from
participant structure, its P becomes the S of an intransitive construction, and nothing is
nucleativized. -/
def Decausativization (c d : Construction ι) : Prop :=
  c.Transitive ∧ (∀ i, c i = .term .A → Suppressed c d i) ∧
    (∀ i, c i = .term .P → d i = .term .S) ∧ ¬ Nucleativization c d

/-- A-nucleativization: a participant is nucleativized and takes over the role of A or S,
and the participant coded as A or S in the initial construction is coded as P or
denucleativized. Causativization in the narrow sense of chapter 12, where the new
participant instigates or controls the event, the A-nucleativization of an instrumental
oblique, and concernativization, where the new participant is a concernee of the initial S
or P, share this structure and differ in the new participant's semantic relation to the
event, which is not modelled. -/
def ANucleativization (c d : Construction ι) (i : ι) : Prop :=
  Nucleativized c d i ∧ (d i = .term .A ∨ d i = .term .S) ∧
    ∀ j, (c j = .term .A ∨ c j = .term .S) → d j = .term .P ∨ ¬ (d j).Nuclear

/-- Reflexivization and reciprocalization: two participant roles expressed as A and P, or as
S and a dative oblique, in the initial construction are cumulated by the S term of the
derived construction. Whether the S refers to an individual or to a group is not modelled. -/
def Cumulation (c d : Construction ι) : Prop :=
  ∃ a p, a ≠ p ∧ ((c a = .term .A ∧ c p = .term .P) ∨ (c a = .term .S ∧ c p = .dative)) ∧
    d a = .term .S ∧ d p = .term .S

/-- Applicativization: the participant coded as A or S in the initial construction keeps
the role of A or S, and the derived construction expresses, in a role other than A or S, an
applied participant that the initial construction did not express that way. -/
def Applicativization (c d : Construction ι) (applied : ι) : Prop :=
  (∀ j, (c j = .term .A ∨ c j = .term .S) → d j = .term .A ∨ d j = .term .S) ∧
    ¬ (c applied).Nuclear ∧ c applied ≠ d applied ∧ (d applied).Expressed ∧
      d applied ≠ .term .A ∧ d applied ≠ .term .S

/-- P-applicativization: the applied phrase is a P, so the initial A or S is the A of the
derived transitive construction. -/
def PApplicativization (c d : Construction ι) (applied : ι) : Prop :=
  Applicativization c d applied ∧ d applied = .term .P ∧
    ∀ j, (c j = .term .A ∨ c j = .term .S) → d j = .term .A

/-- D-applicativization: the applied phrase is a dative oblique. -/
def DApplicativization (c d : Construction ι) (applied : ι) : Prop :=
  Applicativization c d applied ∧ d applied = .dative

/-- X-applicativization: the applied phrase is an ordinary oblique. -/
def XApplicativization (c d : Construction ι) (applied : ι) : Prop :=
  Applicativization c d applied ∧ d applied = .term .X

/-- Portative derivation: an intransitive verb of motion becomes transitive, its S the A of
the derived construction and a carried entity its P. -/
def Portative (c d : Construction ι) (carried : ι) : Prop :=
  ¬ c.Transitive ∧ Nucleativized c d carried ∧ d carried = .term .P ∧
    ∀ j, c j = .term .S → d j = .term .A

/-- A symmetrical voice alternation selects a pivot without changing which participants are
core terms. -/
def Symmetrical (c d : Construction ι) : Prop := ∀ i, (c i).Nuclear ↔ (d i).Nuclear

section
variable [Fintype ι] [DecidableEq ι]

instance (c d : Construction ι) (i : ι) : Decidable (Demoted c d i) := by
  unfold Demoted; infer_instance
instance (c d : Construction ι) : Decidable (Passivization c d) := by
  unfold Passivization; infer_instance
instance (c d : Construction ι) : Decidable (IPassivization c d) := by
  unfold IPassivization; infer_instance
instance (c d : Construction ι) : Decidable (Antipassivization c d) := by
  unfold Antipassivization; infer_instance
instance (c d : Construction ι) : Decidable (SDenucleativization c d) := by
  unfold SDenucleativization; infer_instance
instance (c d : Construction ι) : Decidable (Decausativization c d) := by
  unfold Decausativization; infer_instance
instance (c d : Construction ι) (i : ι) : Decidable (ANucleativization c d i) := by
  unfold ANucleativization; infer_instance
instance (c d : Construction ι) : Decidable (Cumulation c d) := by
  unfold Cumulation; infer_instance
instance (c d : Construction ι) (i : ι) : Decidable (Applicativization c d i) := by
  unfold Applicativization; infer_instance
instance (c d : Construction ι) (i : ι) : Decidable (PApplicativization c d i) := by
  unfold PApplicativization; infer_instance
instance (c d : Construction ι) (i : ι) : Decidable (DApplicativization c d i) := by
  unfold DApplicativization; infer_instance
instance (c d : Construction ι) (i : ι) : Decidable (XApplicativization c d i) := by
  unfold XApplicativization; infer_instance
instance (c d : Construction ι) (i : ι) : Decidable (Portative c d i) := by
  unfold Portative; infer_instance
instance (c d : Construction ι) : Decidable (Symmetrical c d) := by
  unfold Symmetrical; infer_instance

end

/-- Decausativization modifies participant structure: the initial A leaves it. -/
theorem Decausativization.not_preservesStructure {c d : Construction ι}
    (h : Decausativization c d) : ¬ PreservesStructure c d :=
  let ⟨⟨⟨a, ha⟩, _⟩, hA, _, _⟩ := h
  λ hp => (hp a).mp (by simp [Status.Present, ha]) (hA a ha).2

/-- The maintenance of the initial A in participant structure separates passivization from
decausativization. -/
theorem Passivization.not_decausativization {c d : Construction ι} (h : Passivization c d) :
    ¬ Decausativization c d :=
  let ⟨⟨⟨a, ha⟩, _⟩, hA, _⟩ := h
  λ h' => (hA a ha).2.1 (h'.2.1 a ha).2

/-- S-denucleativization leaves no core term when the initial construction has no core term
but its S. -/
theorem SDenucleativization.not_nuclear {c d : Construction ι} (h : SDenucleativization c d)
    (hc : ∀ i, (c i).Nuclear → c i = .term .S) (i : ι) : ¬ (d i).Nuclear := by
  intro hd
  by_cases hi : (c i).Nuclear
  · exact (h.2.2 i (hc i hi)).1.2 hd
  · obtain ⟨s, hs⟩ := h.2.1
    exact (h.2.2 s hs).2.2 ⟨i, hi, hd⟩

/-- Portative derivation is not causativization in the narrow sense: the initial S is the A
of the one and the P of the other. -/
theorem Portative.not_aNucleativization {c d : Construction ι} {i : ι} (h : Portative c d i)
    (hS : ∃ s, c s = .term .S) (j : ι) : ¬ ANucleativization c d j := by
  rintro ⟨-, -, hc⟩
  obtain ⟨s, hs⟩ := hS
  have := h.2.2.2 s hs
  rcases hc s (.inr hs) with hP | hN
  · exact absurd (hP.symm.trans this) (by decide)
  · exact hN (by simp [this, Status.Nuclear])

/-- A symmetrical voice nucleativizes nothing. -/
theorem Symmetrical.not_nucleativization {c d : Construction ι} (h : Symmetrical c d) :
    ¬ Nucleativization c d :=
  λ ⟨i, hi⟩ => hi.1 ((h i).mpr hi.2)

/-- A symmetrical voice denucleativizes nothing. -/
theorem Symmetrical.not_denucleativization {c d : Construction ι} (h : Symmetrical c d) :
    ¬ Denucleativization c d :=
  λ ⟨i, hi⟩ => hi.2 ((h i).mp hi.1)

/-- A symmetrical voice is not a passivization, nor any type defined by denucleativization. -/
theorem Symmetrical.not_passivization {c d : Construction ι} (h : Symmetrical c d) :
    ¬ Passivization c d :=
  λ ⟨⟨⟨a, ha⟩, _⟩, hA, _⟩ => h.not_denucleativization ⟨a, (hA a ha).1⟩

/-- A symmetrical voice is not an A-nucleativization, nor any type defined by
nucleativization. -/
theorem Symmetrical.not_aNucleativization {c d : Construction ι} (h : Symmetrical c d)
    (i : ι) : ¬ ANucleativization c d i :=
  λ hc => h.not_nucleativization ⟨i, hc.1⟩

/-! ### The substrate's summary records -/

section
variable [Fintype ι] [DecidableEq ι]

/-- The fate of an initial core term, read off the two constructions: suppressed when it
leaves participant structure, cumulated when it shares its derived core term with another
initial core term, maintained when it remains a core term, denucleativized otherwise. -/
def fate (c d : Construction ι) (i : ι) : ParticipantFate :=
  if (c i).Nuclear then
    if d i = .absent then .suppressed
    else if (d i).Nuclear then
      if ∃ j, j ≠ i ∧ (c j).Nuclear ∧ d j = d i then .cumulated else .maintained
    else .denucleativized
  else .na

/-- A summary record of the substrate describes a pair of constructions when the fates it
records are those of the initial A, P and S, a role it records as absent is absent, the
participant it introduces is the one the derived construction introduces, and the
transitivity it fixes is the constructions'. -/
def Describes (va : ValencyAlternation) (c d : Construction ι) : Prop :=
  (∀ i, c i = .term .A → fate c d i = va.fateOfA) ∧
  (∀ i, c i = .term .P → fate c d i = va.fateOfP) ∧
  (∀ i, c i = .term .S → fate c d i = va.fateOfS) ∧
  (va.fateOfA = .na → ¬ ∃ i, c i = .term .A) ∧ (va.fateOfP = .na → ¬ ∃ i, c i = .term .P) ∧
  (va.fateOfS = .na → ¬ ∃ i, c i = .term .S) ∧
  (match va.newParticipant with
    | some r => ∃ i, Introduced c d i ∧ (d i).role = some r
    | none => ¬ ∃ i, Introduced c d i) ∧
  (∀ b, va.initialTransitive = some b → (c.Transitive ↔ b = true)) ∧
  ∀ b, va.derivedTransitive = some b → (d.Transitive ↔ b = true)

instance (va : ValencyAlternation) (c d : Construction ι) : Decidable (Describes va c d) := by
  unfold Describes
  cases va.newParticipant <;> infer_instance

end

/-! ### Alignment and the Obligatory Coding Principle (§1.3.4) -/

/-- The flagging of a core term: the zero case, an accusative or an ergative. -/
inductive Flag where
  | zero
  | accusative
  | ergative
  deriving DecidableEq, Repr

/-- The flags of A and of P in an A/P-prominent transitive construction, which contrast. -/
structure Coding where
  /-- The flag of A. -/
  a : Flag
  /-- The flag of P. -/
  p : Flag
  /-- A and P are flagged apart. -/
  ne : a ≠ p
  deriving DecidableEq, Repr

namespace Coding

/-- The alignment of an intransitive construction whose S carries a flag: with A, with P, or
neither. -/
def alignment (t : Coding) (s : Flag) : Option Alignment :=
  if s = t.a then some .A_alignment else if s = t.p then some .P_alignment else none

/-- A flag aligns with A exactly when it is the A flag. -/
@[simp] theorem alignment_eq_A_iff {t : Coding} {s : Flag} :
    t.alignment s = some .A_alignment ↔ s = t.a := by
  unfold alignment; split_ifs with h₁ <;> simp [h₁]

/-- A flag aligns with P exactly when it is the P flag. -/
@[simp] theorem alignment_eq_P_iff {t : Coding} {s : Flag} :
    t.alignment s = some .P_alignment ↔ s = t.p := by
  unfold alignment; split_ifs with h₁ <;> simp_all [t.ne]

end Coding

/-- The Obligatory Coding Principle, over the intransitive constructions of the examples: a
flag of the transitive construction that every verb assigns to one of its participants, here
every intransitive verb through its S. -/
def ObligatoryCoding (t : Coding) (ss : List Flag) (k : Flag) : Prop :=
  (k = t.a ∨ k = t.p) ∧ ∀ s ∈ ss, s = k

/-- An obligatory A-coding language, the consistently accusative type. -/
def ObligatoryACoding (t : Coding) (ss : List Flag) : Prop := ObligatoryCoding t ss t.a

/-- An obligatory P-coding language, the consistently ergative type. -/
def ObligatoryPCoding (t : Coding) (ss : List Flag) : Prop := ObligatoryCoding t ss t.p

/-- A split-S language: some intransitive constructions align with A and some with P. -/
def SplitS (t : Coding) (ss : List Flag) : Prop :=
  (∃ s ∈ ss, t.alignment s = some .A_alignment) ∧ ∃ s ∈ ss, t.alignment s = some .P_alignment

instance (t : Coding) (ss : List Flag) (k : Flag) : Decidable (ObligatoryCoding t ss k) := by
  unfold ObligatoryCoding; infer_instance
instance (t : Coding) (ss : List Flag) : Decidable (ObligatoryACoding t ss) := by
  unfold ObligatoryACoding; infer_instance
instance (t : Coding) (ss : List Flag) : Decidable (ObligatoryPCoding t ss) := by
  unfold ObligatoryPCoding; infer_instance
instance (t : Coding) (ss : List Flag) : Decidable (SplitS t ss) := by
  unfold SplitS; infer_instance

/-- Over the S flags alone, obligatory A-coding is A-alignment throughout. -/
theorem obligatoryACoding_iff {t : Coding} {ss : List Flag} :
    ObligatoryACoding t ss ↔ ∀ s ∈ ss, t.alignment s = some .A_alignment := by
  simp [ObligatoryACoding, ObligatoryCoding]

/-- Over the S flags alone, obligatory P-coding is P-alignment throughout. -/
theorem obligatoryPCoding_iff {t : Coding} {ss : List Flag} :
    ObligatoryPCoding t ss ↔ ∀ s ∈ ss, t.alignment s = some .P_alignment := by
  simp [ObligatoryPCoding, ObligatoryCoding]

/-- A split-S language is not obligatory A-coding. -/
theorem SplitS.not_obligatoryACoding {t : Coding} {ss : List Flag} (h : SplitS t ss) :
    ¬ ObligatoryACoding t ss :=
  let ⟨_, sp, hsp, hp⟩ := h
  λ hA => t.ne ((hA.2 sp hsp).symm.trans (Coding.alignment_eq_P_iff.mp hp))

/-- A split-S language is not obligatory P-coding. -/
theorem SplitS.not_obligatoryPCoding {t : Coding} {ss : List Flag} (h : SplitS t ss) :
    ¬ ObligatoryPCoding t ss :=
  let ⟨⟨sa, hsa, ha⟩, _⟩ := h
  λ hP => t.ne ((Coding.alignment_eq_A_iff.mp ha).symm.trans (hP.2 sa hsa))

/-! ### The book's examples -/

/-- The types of voice alternation the book names, symmetrical voices included. -/
inductive Kind where
  | passivization
  | iPassivization
  | antipassivization
  | sDenucleativization
  | decausativization
  | causativization
  | concernativization
  | aNucleativization
  | reflexivization
  | reciprocalization
  | pApplicativization
  | dApplicativization
  | xApplicativization
  | portative
  | symmetrical
  deriving DecidableEq, Repr, Fintype

/-- Whether a pair of constructions realizes a type, given the participant the type singles
out; the three A-nucleativizations and the two cumulations share their structure. -/
def Kind.Realize (c d : Construction ι) : Kind → Option ι → Prop
  | .passivization, _ => Passivization c d
  | .iPassivization, _ => IPassivization c d
  | .antipassivization, _ => Antipassivization c d
  | .sDenucleativization, _ => SDenucleativization c d
  | .decausativization, _ => Decausativization c d
  | .causativization, some i => ANucleativization c d i
  | .concernativization, some i => ANucleativization c d i
  | .aNucleativization, some i => ANucleativization c d i
  | .reflexivization, _ => Cumulation c d
  | .reciprocalization, _ => Cumulation c d
  | .pApplicativization, some i => PApplicativization c d i
  | .dApplicativization, some i => DApplicativization c d i
  | .xApplicativization, some i => XApplicativization c d i
  | .portative, some i => Portative c d i
  | .symmetrical, _ => Symmetrical c d
  | _, none => False

instance [Fintype ι] [DecidableEq ι] (c d : Construction ι) (k : Kind) (o : Option ι) :
    Decidable (k.Realize c d o) := by
  cases k <;> cases o <;> simp only [Kind.Realize] <;> infer_instance

/-- The share of the languages in Bahrt's sample with synthetic marking of each type, in
percent; Bahrt's applicativization pools the three applicativizations with non-causative
A/S-nucleativization, and the book's symmetrical voices are outside his survey. -/
def Kind.bahrtShare : Kind → Option ℚ
  | .causativization => some (739 / 10)
  | .reciprocalization => some (604 / 10)
  | .pApplicativization | .dApplicativization | .xApplicativization | .aNucleativization
  | .concernativization => some (459 / 10)
  | .reflexivization => some (419 / 10)
  | .decausativization => some 36
  | .passivization => some 36
  | .antipassivization => some (185 / 10)
  | _ => none

/-- Causativization is the most widely marked type and antipassivization the least. -/
theorem bahrtShare_extremes : ∀ k : Kind, ∀ x ∈ k.bahrtShare,
    (∀ y ∈ Kind.bahrtShare .causativization, x ≤ y) ∧
    ∀ y ∈ Kind.bahrtShare .antipassivization, y ≤ x := by
  decide +kernel

/-- The types by name. -/
def kindNames : List (String × Kind) :=
  [("passivization", .passivization), ("iPassivization", .iPassivization),
    ("antipassivization", .antipassivization), ("sDenucleativization", .sDenucleativization),
    ("decausativization", .decausativization), ("causativization", .causativization),
    ("concernativization", .concernativization), ("aNucleativization", .aNucleativization),
    ("reflexivization", .reflexivization), ("reciprocalization", .reciprocalization),
    ("pApplicativization", .pApplicativization), ("dApplicativization", .dApplicativization),
    ("xApplicativization", .xApplicativization), ("portative", .portative),
    ("symmetrical", .symmetrical)]

/-- The statuses by name. -/
def statusNames : List (String × Status) :=
  [("A", .term .A), ("P", .term .P), ("S", .term .S), ("X", .term .X), ("dative", .dative),
    ("implicit", .implicit), ("absent", .absent)]

/-- The participant slots of a row by name. -/
def slotNames : List (String × Fin 5) := [("p1", 0), ("p2", 1), ("p3", 2), ("p4", 3), ("p5", 4)]

/-- The flags by name. -/
def flagNames : List (String × Flag) :=
  [("zero", .zero), ("accusative", .accusative), ("ergative", .ergative)]

/-- The markings by name. -/
def markingNames : List (String × AlternationMarking) :=
  [("synthetic", .synthetic), ("analytic", .analytic), ("equipollent", .equipollent),
    ("uncoded", .uncoded)]

namespace Examples

/-- The construction a row describes over its five participant slots, absent where
unlisted. -/
def construction (row : LinguisticExample) : Construction (Fin 5) :=
  ![slot row "p1", slot row "p2", slot row "p3", slot row "p4", slot row "p5"]
where
  /-- The status of one slot. -/
  slot (row : LinguisticExample) (k : String) : Status := (row.parse? k statusNames).getD .absent

/-- The rows of the same example whose variant the row names under a key: its initial
construction, or the transitive use of a flexivalent verb. -/
def paired (key : String) (row : LinguisticExample) : List LinguisticExample :=
  all.filter λ r =>
    r.feature? "example" = row.feature? "example" ∧ r.feature? "variant" = row.feature? key

/-- The S flags of a language's intransitive examples. -/
def sFlags (language : String) : List Flag :=
  (all.filter (·.language = language)).filterMap (·.parse? "S" flagNames)

/-- The A and P flags of a language's transitive example. -/
def coding (language : String) : Option Coding :=
  (all.filter (·.language = language)).findSome? λ r => do
    let a ← r.parse? "A" flagNames
    let p ← r.parse? "P" flagNames
    if h : a ≠ p then some ⟨a, p, h⟩ else none

/-- The types a marker of a language codes across the book's examples. -/
def coExpressed (language marker : String) : List Kind :=
  (all.filter λ r => r.language = language ∧ r.feature? "marker" = some marker).filterMap
    (·.parse? "alternation" kindNames)

end Examples

open Examples

/-- Every label the rows carry parses to a type. -/
theorem alternation_parses : ∀ row ∈ all,
    (row.feature? "alternation").isSome → (row.parse? "alternation" kindNames).isSome := by
  decide +kernel

/-- Every initial construction or transitive use a row names is a row of the same example. -/
theorem paired_resolves : ∀ row ∈ all, ∀ key ∈ ["initial", "transitive"],
    (row.feature? key).isSome → paired key row ≠ [] := by
  decide +kernel

/-- Every derived construction of the book's examples realizes the type the book assigns
it, relative to its initial construction. -/
theorem rows_classified : ∀ row ∈ all, ∀ k ∈ row.parse? "alternation" kindNames,
    ∀ init ∈ paired "initial" row,
    k.Realize (construction init) (construction row) (row.parse? "new" slotNames) := by
  decide +kernel

/-- A symmetrical voice selects a different, expressed participant as pivot. -/
theorem symmetrical_rows : ∀ row ∈ all, row.parse? "alternation" kindNames = some .symmetrical →
    ∀ init ∈ paired "initial" row, ∃ p ∈ row.parse? "pivot" slotNames,
    ∃ q ∈ init.parse? "pivot" slotNames, p ≠ q ∧ (construction row p).Expressed := by
  decide +kernel

/-- Each substrate record with the book's initial and derived example of its type. -/
def definingExamples : List (ValencyAlternation × LinguisticExample × LinguisticExample) :=
  [(passivization, ex_8_1a, ex_8_1b), (iPassivization, ex_8_14a, ex_8_14c),
    (sDenucleativization, ex_8_14d, ex_8_14e), (antipassivization, ex_8_21a, ex_8_21b),
    (decausativization, ex_8_19a, ex_8_19b), (causativization, ex_8_18a, ex_8_18b),
    (reflexivization, ex_8_23a, ex_8_23b), (reciprocalization, ex_8_24a, ex_8_24b),
    (asNucleativizationOfObliques, ex_8_13a, ex_8_13b),
    (concernativization, ex_8_27a, ex_8_27b), (pApplicativization, ex_8_6a, ex_8_6b),
    (dApplicativization, ex_8_5a, ex_8_5b), (xApplicativization, ex_8_28a, ex_8_28b),
    (portativeDerivation, ex_8_33a, ex_8_33b)]

/-- The book's defining example of each type is described by the substrate's record of it. -/
theorem records_described :
    ∀ e ∈ definingExamples, Describes e.1 (construction e.2.1) (construction e.2.2) := by
  decide +kernel

/-- Mandinka (13) of chapter 1: 'repair' takes A and P, 'forget' takes S and a postpositional
oblique. -/
theorem mandinka_roles :
    (construction ex_1_13a).Transitive ∧ ¬ (construction ex_1_13b).Transitive := by
  decide +kernel

/-- Russian (23) is obligatory A-coding, Avar (24) obligatory P-coding, and Basque (22),
with an ergative S beside a zero-flagged one, split-S and neither. -/
theorem alignment_rows :
    (∃ t ∈ coding "russ1263",
      sFlags "russ1263" ≠ [] ∧ ObligatoryACoding t (sFlags "russ1263")) ∧
    (∃ t ∈ coding "avar1256",
      sFlags "avar1256" ≠ [] ∧ ObligatoryPCoding t (sFlags "avar1256")) ∧
    ∃ t ∈ coding "basq1248", SplitS t (sFlags "basq1248") := by
  decide +kernel

/-- The uncoded alternations of Bambara (2), (3) and Basque (4), which the book calls
P-ambitransitivity for Basque and describes in the same terms as the Tswana passive for
Bambara, are P-ambitransitivity: the initial P is the S of an intransitive construction and
the initial A is not a core term; Bambara's preserves participant structure, with the agent
an optional oblique, and Basque's does not. -/
theorem ambitransitivity_rows : ∀ row ∈ all,
    row.parse? "marking" markingNames = some .uncoded → ∀ init ∈ paired "transitive" row,
    (construction init).Transitive ∧ ¬ (construction row).Transitive ∧
    (∀ i, construction init i = .term .P → construction row i = .term .S) ∧
    (∀ i, construction init i = .term .A → ¬ (construction row i).Nuclear) ∧
    (PreservesStructure (construction init) (construction row) ↔ row.language = "bamb1269") := by
  decide +kernel

/-- Tswana *-w* codes passivization, its impersonal variant and S-denucleativization; Tswana
*-ɛl* codes P-applicativization, X-applicativization and the A-nucleativization of an
oblique; Tswana *-is* codes causativization and, in chapter 12, portative derivation; Diré
Songhay *-ndi* codes causativization and passivization. -/
theorem coexpression :
    [Kind.passivization, .iPassivization, .sDenucleativization] ⊆ coExpressed "tswa1253" "-w" ∧
    [Kind.pApplicativization, .xApplicativization, .aNucleativization] ⊆
      coExpressed "tswa1253" "-ɛl" ∧
    [Kind.causativization, .portative] ⊆ coExpressed "tswa1253" "-is" ∧
    [Kind.causativization, .passivization] ⊆ coExpressed "koyr1240" "-ndi" := by
  decide +kernel

/-- Tswana (38): passivizing the applicative of the causative is the composite of the three
alternations, through (38d) and (38e). -/
theorem stacking_tswana :
    Relation.Comp (Relation.Comp (ANucleativization · · 2) (PApplicativization · · 3))
      Passivization (construction ex_8_38a) (construction ex_8_38h) :=
  ⟨construction ex_8_38e, ⟨construction ex_8_38d, by decide +kernel, by decide +kernel⟩,
    by decide +kernel⟩

/-- Classical Nahuatl (39): the passive of the antipassive of the causative, through (39b)
and (39c). -/
theorem stacking_nahuatl :
    Relation.Comp (Relation.Comp (ANucleativization · · 2) Antipassivization) Passivization
      (construction ex_8_39a) (construction ex_8_39e) :=
  ⟨construction ex_8_39c, ⟨construction ex_8_39b, by decide +kernel, by decide +kernel⟩,
    by decide +kernel⟩

/-- Passivization need not yield an intransitive construction: the passive (38f) of the
double-P applicative (38c) is transitive, the applied P taking A coding. -/
theorem passive_transitive :
    Passivization (construction ex_8_38c) (construction ex_8_38f) ∧
    (construction ex_8_38f).Transitive := by
  decide +kernel

/-- The Balinese causative (51) nucleativizes a causer and denucleativizes the initial P,
the initial A taking the role of P: its valency is unchanged. -/
theorem causative_valency :
    Nucleativization (construction ex_8_51a) (construction ex_8_51b) ∧
    Denucleativization (construction ex_8_51a) (construction ex_8_51b) ∧
    (construction ex_8_51a).valency = (construction ex_8_51b).valency := by
  decide +kernel

/-- Portative derivation in Tswana (3) of chapter 12: the woman who brought the food came,
and the food, which cannot come, is not the initial S. -/
theorem portative_rows :
    ex_12_3b.judgment = .acceptable ∧ ex_12_3c.judgment = .unacceptable ∧
    construction ex_12_3b 0 = .term .S ∧ construction ex_12_3c 1 = .term .S := by
  decide +kernel

/-! ### Symmetrical voice systems (§8.5) -/

/-- Balinese (47): a binary symmetrical system, agent voice and patient voice. -/
def balineseVoices : List VoiceEntry :=
  [⟨"agent voice", .agent⟩, ⟨"patient voice", .patient⟩]

/-- Tagalog (48): a multiple symmetrical system whose locative, conveyance and instrumental
voices select an oblique as pivot; the substrate has no conveyance pivot, so the conveyance
voice, whose pivot is a beneficiary or a displaced theme, is entered as benefactive. -/
def tagalogVoices : List VoiceEntry :=
  [⟨"agent voice", .agent⟩, ⟨"patient voice", .patient⟩, ⟨"locative voice", .locative⟩,
    ⟨"conveyance voice", .benefactive⟩, ⟨"instrumental voice", .instrumental⟩]

/-- Only the multiple system lets an oblique be the pivot. -/
theorem multiple_distinguishesObliques :
    ¬ distinguishesObliques balineseVoices ∧ distinguishesObliques tagalogVoices := by
  decide

end Creissels2024
