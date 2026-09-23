module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Evidential.Basic
public import Linglib.Fragments.Turkish.Evidentiality
public import Linglib.Fragments.Abkhaz.Evidentiality
public import Linglib.Fragments.Slavic.Bulgarian.Evidentiality
public import Linglib.Fragments.Quechua.Evidentiality
public import Linglib.Fragments.Tuyuca.Evidentiality
public import Linglib.Fragments.Tariana.Evidentiality
public import Linglib.Fragments.Kashaya.Evidentiality
public import Linglib.Fragments.Romance.French.Evidentiality
public import Linglib.Fragments.Japanese.Evidentiality
public import Linglib.Data.Examples.Aikhenvald2004

/-!
# Aikhenvald (2004): Evidentiality

This file formalizes the typology of grammatical evidentiality systems in chapter 2 of
[aikhenvald-2004]. Systems are classified by how many information sources a speaker must
choose among and how those sources are grouped: five kinds with two choices (A1–A5), five
with three (B1–B5), three with four (C1–C3) and one with five (D1), each a grouping of the six
semantic parameters of information source into the terms of a paradigm. Four kinds (A2, A3,
A5, B5) are organized around an evidentiality-neutral "everything else" term; the rest oppose
marked terms only. What counts as an evidential is a form whose main meaning is information
source: the perfects of Georgian and the Iranian languages, the French conditional and the
Japanese sentence-final devices are evidentiality strategies, not evidentials.

A term is the shape of an evidential's coverage (`Term.of`), read off the coarse predicates of
the substrate: within one of Willett's domains a head term (visual evidence with or without
the other senses, inference, hearsay) or a tail term (the other senses, assumption or
quotation alone), across domains the non-firsthand term. A kind is the set of terms it
distinguishes (`Kind.terms`, Table 2.1 together with the marked terms of the everything-else
kinds), and the kind of a language is the one whose terms are exactly those of its Fragment
inventory (`kind`). Disjoint evidentials realize distinct terms, so in a well-formed inventory
the letter of the kind counts the evidentials, plus one for an everything-else term
(`choices_eq_length`). Turkish, Abkhaz and Bulgarian derive as A2 once their unmarked pasts
are read as evidentiality-neutral rather than firsthand, Cuzco Quechua as B1, Tuyuca and
Tariana as D1, while Kashaya's performative lies outside the six parameters, so its paradigm
fits no kind.

## References

* [aikhenvald-2004]
* [barnes-1984]
* [oswalt-1986]
* [willett-1988]
-/

@[expose] public section

namespace Aikhenvald2004

open Evidential

/-! ### Terms -/

/-- The terms of Table 2.1: the shapes a term's coverage can take. -/
inductive Term
  | visual | sensory | inferred | assumed | reported | quotative | nonfirsthand
  deriving DecidableEq, Repr

/-- The parameter heading a term, covered by every evidential that realizes it. -/
def Term.head : Term → Parameter
  | .visual => .visual
  | .sensory => .sensory
  | .inferred | .nonfirsthand => .inference
  | .assumed => .assumption
  | .reported => .hearsay
  | .quotative => .quotative

/-- The term an evidential realizes. Within one of Willett's domains it is the head term when
the coverage includes the domain's head parameter (visual evidence, inference, hearsay) and
the tail term otherwise (the other senses, assumption, quotation alone); across domains it is
the non-firsthand term; any other coverage realizes no term of the typology. -/
def Term.of (e : Evidential) : Option Term :=
  if e.IsDirect then some (if .visual ∈ e.covers then .visual else .sensory)
  else if e.IsInferential then some (if .inference ∈ e.covers then .inferred else .assumed)
  else if e.IsReportative then some (if .hearsay ∈ e.covers then .reported else .quotative)
  else if e.IsNonfirsthand then some .nonfirsthand
  else none

/-- Willett's type of evidence of a term; a non-firsthand term spans two. -/
def Term.evidenceType? : Term → Option EvidenceType
  | .visual | .sensory => some .attested
  | .inferred | .assumed => some .inferring
  | .reported | .quotative => some .reported
  | .nonfirsthand => none

/-- The evidence type of an evidential's term is the evidential's. -/
theorem Term.evidenceType?_of (e : Evidential) :
    (Term.of e).bind Term.evidenceType? = e.evidenceType? := by
  unfold Term.of Evidential.evidenceType?
  split_ifs <;> rfl

private theorem mem_of_subset_pair {α : Type*} [DecidableEq α] {s : Finset α} {a b : α}
    (hs : s.Nonempty) (h : s ⊆ {a, b}) (ha : a ∉ s) : b ∈ s := by
  obtain ⟨p, hp⟩ := hs
  rcases Finset.mem_insert.1 (h hp) with rfl | hb
  · exact absurd hp ha
  · exact Finset.mem_singleton.1 hb ▸ hp

theorem Term.head_mem {e : Evidential} {t : Term} (h : Term.of e = some t) :
    t.head ∈ e.covers := by
  unfold Term.of at h
  split_ifs at h with hd hv hi hia hr hh hn <;> cases h
  · exact hv
  · exact mem_of_subset_pair hd.1 hd.2 hv
  · exact hia
  · exact mem_of_subset_pair hi.1 hi.2 hia
  · exact hh
  · exact mem_of_subset_pair hr.1 hr.2 hh
  · exact hn.1

/-- Disjoint evidentials realize distinct terms. -/
theorem Term.ne_of_disjoint {a b : Evidential} {t t' : Term} (hab : Disjoint a.covers b.covers)
    (ha : Term.of a = some t) (hb : Term.of b = some t') : t ≠ t' := by
  rintro rfl
  exact Finset.disjoint_left.1 hab (head_mem ha) (head_mem hb)

/-- The terms an inventory distinguishes, if each of its evidentials realizes one. -/
def terms (es : List Evidential) : Option (Finset Term) :=
  if ∀ e ∈ es, (Term.of e).isSome then some (es.filterMap Term.of).toFinset else none

/-- In a well-formed inventory each evidential realizes its own term, so the inventory has as
many evidentials as it distinguishes terms. -/
theorem length_eq_card {es : List Evidential} {S : Finset Term} (h : WellFormed es)
    (hS : terms es = some S) : es.length = S.card := by
  unfold terms at hS
  split_ifs at hS with hall
  obtain rfl := Option.some.inj hS
  rw [List.toFinset_card_of_nodup, List.filterMap_length_eq_length.2 hall]
  exact List.pairwise_filterMap.2 (h.imp fun hab _ ha _ hb => Term.ne_of_disjoint hab ha hb)

/-! ### The kinds of system -/

/-- The fourteen kinds of evidentiality system: the letter gives the number of choices, the
digit the grouping of information sources. -/
inductive Kind
  | A1 | A2 | A3 | A4 | A5 | B1 | B2 | B3 | B4 | B5 | C1 | C2 | C3 | D1
  deriving DecidableEq, Repr, Fintype

namespace Kind

/-- The number of evidentiality choices, counting an evidentiality-neutral term. -/
def choices : Kind → ℕ
  | .A1 | .A2 | .A3 | .A4 | .A5 => 2
  | .B1 | .B2 | .B3 | .B4 | .B5 => 3
  | .C1 | .C2 | .C3 => 4
  | .D1 => 5

/-- The kinds organized around an evidentiality-neutral "everything else" term. -/
def HasDefault (k : Kind) : Prop := k ∈ ({.A2, .A3, .A5, .B5} : Finset Kind)

instance : DecidablePred HasDefault := fun _ => inferInstanceAs (Decidable (_ ∈ _))

/-- The terms a system of each kind distinguishes: the rows of Table 2.1 and the marked terms
of the everything-else kinds. -/
def terms : Kind → Finset Term
  | .A1 => {.visual, .nonfirsthand}
  | .A2 => {.nonfirsthand}
  | .A3 => {.reported}
  | .A4 => {.visual, .reported}
  | .A5 => {.sensory}
  | .B1 => {.visual, .inferred, .reported}
  | .B2 => {.visual, .sensory, .inferred}
  | .B3 => {.visual, .sensory, .reported}
  | .B4 => {.sensory, .inferred, .reported}
  | .B5 => {.reported, .quotative}
  | .C1 => {.visual, .sensory, .inferred, .reported}
  | .C2 => {.visual, .inferred, .assumed, .reported}
  | .C3 => {.visual, .inferred, .reported, .quotative}
  | .D1 => {.visual, .sensory, .inferred, .assumed, .reported}

/-- The letter counts choices: the distinguished terms, plus one for an everything-else term. -/
theorem choices_eq_card_terms (k : Kind) :
    k.choices = k.terms.card + if k.HasDefault then 1 else 0 := by cases k <;> decide

/-- No system expresses all six parameters. -/
theorem card_terms_le_five (k : Kind) : k.terms.card ≤ 5 := by cases k <;> decide

/-- Only one kind of five-choice system has been found. -/
theorem eq_D1_of_choices (k : Kind) (h : k.choices = 5) : k = .D1 := by
  cases k <;> first | rfl | exact absurd h (by decide)

/-- Distinct kinds distinguish distinct terms. -/
theorem terms_injective : Function.Injective terms := by decide

/-- B1 groups the parameters into Willett's three types of evidence. -/
theorem B1_willett :
    Kind.B1.terms.image Term.evidenceType? =
      {some .attested, some .inferring, some .reported} := by
  decide

end Kind

/-! ### Classifying an inventory -/

/-- The kind of system an inventory instantiates: the kind distinguishing exactly its terms. -/
def kind (es : List Evidential) : Option Kind :=
  (terms es).bind fun S =>
    if h : S ∈ Set.range Kind.terms then some (Kind.terms_injective.invOfMemRange ⟨S, h⟩)
    else none

theorem kind_eq_some_iff (es : List Evidential) (k : Kind) :
    kind es = some k ↔ terms es = some k.terms := by
  unfold kind
  cases terms es with
  | none => simp
  | some S =>
    simp only [Option.bind_some, Option.some.injEq]
    split_ifs with h
    · simp only [Option.some.injEq]
      constructor <;> rintro rfl
      exacts [(Kind.terms_injective.left_inv_of_invOfMemRange ⟨S, h⟩).symm,
        Kind.terms_injective.right_inv_of_invOfMemRange k]
    · exact ⟨nofun, fun hS => (h ⟨k, hS.symm⟩).elim⟩

theorem kind_eq_none_iff (es : List Evidential) :
    kind es = none ↔ ∀ k : Kind, terms es ≠ some k.terms := by
  simp only [Option.eq_none_iff_forall_ne_some, ne_eq, kind_eq_some_iff]

/-- The letter of a well-formed inventory's kind counts its evidentials, plus one for an
everything-else term. -/
theorem choices_eq_length {es : List Evidential} {k : Kind} (h : WellFormed es)
    (hk : kind es = some k) : k.choices = es.length + if k.HasDefault then 1 else 0 := by
  rw [k.choices_eq_card_terms, length_eq_card h ((kind_eq_some_iff es k).1 hk)]

/-- An empty inventory — an evidentiality strategy, or none at all — is of no kind. -/
theorem kind_nil : kind [] = none := (kind_eq_none_iff _).2 fun k => by cases k <;> decide

/-! ### The Fragment languages -/

/-- The inventories classified here are well formed: no parameter is covered twice. -/
theorem sample_wellFormed :
    ∀ es ∈ [Turkish.Evidentiality.evidentials, Abkhaz.Evidentiality.evidentials,
      Bulgarian.Evidentiality.evidentials, Quechua.Evidentiality.evidentials,
      Tuyuca.Evidentiality.evidentials, Tariana.Evidentiality.evidentials,
      Kashaya.Evidentiality.evidentials], Evidential.WellFormed es := by decide

theorem turkish : kind Turkish.Evidentiality.evidentials = some .A2 :=
  (kind_eq_some_iff _ _).2 (by decide)

theorem abkhaz : kind Abkhaz.Evidentiality.evidentials = some .A2 :=
  (kind_eq_some_iff _ _).2 (by decide)

theorem bulgarian : kind Bulgarian.Evidentiality.evidentials = some .A2 :=
  (kind_eq_some_iff _ _).2 (by decide)

theorem quechua : kind Quechua.Evidentiality.evidentials = some .B1 :=
  (kind_eq_some_iff _ _).2 (by decide)

theorem tuyuca : kind Tuyuca.Evidentiality.evidentials = some .D1 :=
  (kind_eq_some_iff _ _).2 (by decide)

theorem tariana : kind Tariana.Evidentiality.evidentials = some .D1 :=
  (kind_eq_some_iff _ _).2 (by decide)

/-- Kashaya's performative covers none of the six parameters, so its paradigm — visual,
auditory, inferential and reported terms besides — is beyond the fourteen kinds. -/
theorem kashaya_unclassified : kind Kashaya.Evidentiality.evidentials = none :=
  (kind_eq_none_iff _).2 fun k => by cases k <;> decide

/-! ### The book's illustrations -/

/-- The term named by an example's `term` feature. -/
def Term.ofString? : String → Option Term
  | "visual" => some .visual
  | "sensory" => some .sensory
  | "inferred" => some .inferred
  | "assumed" => some .assumed
  | "reported" => some .reported
  | "quotative" => some .quotative
  | "nonfirsthand" => some .nonfirsthand
  | _ => none

/-- The terms illustrated by the examples from a language. -/
def illustrated (lang : String) : Finset Term :=
  ((Examples.all.filter (·.language = lang)).filterMap
    (fun r => r.feature? "term" >>= Term.ofString?)).toFinset

/-- The Tariana illustration runs through every term of a D1 system. -/
theorem tariana_illustration : illustrated "tari1256" = Kind.D1.terms := by decide

/-- The Wanka Quechua examples run through every term of a B1 system. -/
theorem wanka_illustration : illustrated "jauj1238" = Kind.B1.terms := by decide

/-- The Turkish examples show one non-firsthand term covering report, inference and non-visual
perception. -/
theorem turkish_illustration : illustrated "nucl1301" = Kind.A2.terms := by decide

end Aikhenvald2004
