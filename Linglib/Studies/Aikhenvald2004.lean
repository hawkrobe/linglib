import Mathlib.Data.Finset.Card
import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Evidential.Basic
import Linglib.Fragments.Turkish.Evidentiality
import Linglib.Fragments.Abkhaz.Evidentiality
import Linglib.Fragments.Slavic.Bulgarian.Evidentiality
import Linglib.Fragments.Quechua.Evidentiality
import Linglib.Fragments.Tuyuca.Evidentiality
import Linglib.Fragments.Tariana.Evidentiality
import Linglib.Fragments.Kashaya.Evidentiality
import Linglib.Fragments.Romance.French.Evidentiality
import Linglib.Fragments.Japanese.Evidentiality
import Linglib.Data.Examples.Aikhenvald2004

/-!
# Evidentiality systems by number of choices

Aikhenvald classifies the world's grammatical evidentiality systems by how many information
sources a speaker must choose among and how those sources are grouped: five kinds with two
choices (A1–A5), five with three (B1–B5), three with four (C1–C3), and one with five (D1), each
a grouping of six recurrent semantic parameters — visual, non-visual sensory, inference,
assumption, hearsay and quotative — into the terms of a paradigm. Four of the kinds (A2, A3,
A5, B5) are organized around an evidentiality-neutral "everything else" term; the rest oppose
marked terms only. What counts as an evidential is a form whose main meaning is information
source: the perfects of Georgian and the Iranian languages, the French conditional and the
Japanese sentence-final devices are evidentiality strategies, not evidentials.

Here a term is the shape of the parameters an evidential covers (`Term.ofCovers`: visual with
or without the other senses, non-visual sensory, inference with or without assumption, and so
on), each kind is the set of terms it distinguishes (`Kind.terms`, Table 2.1 together with the
marked terms of the everything-else kinds), and the kind of a language is derived from its
Fragment inventory (`kind`), whose well-formed terms partition the parameters it expresses
(`sample_wellFormed`). The letters count choices (`choices_eq_card_terms`), no system
expresses all six parameters (`card_terms_le_five`), D1 is the only five-choice kind
(`eq_D1_of_choices`), and B1 is the grouping that matches Willett's tripartition
(`B1_willett`). Turkish, Abkhaz and Bulgarian derive as A2 once their unmarked pasts are read
as evidentiality-neutral rather than firsthand (`turkish`, `abkhaz`, `bulgarian`), Cuzco
Quechua as B1, Tuyuca and Tariana as D1, while Kashaya's performative lies outside the six
parameters so its paradigm fits no kind (`kashaya_unclassified`), and the strategy languages
have nothing to classify (`kind_nil`). The book's own illustrations exhaust the terms of their
systems (`tariana_illustration`, `wanka_illustration`, `turkish_illustration`).

## References

* [aikhenvald-2004]
* [barnes-1984]
* [oswalt-1986]
* [willett-1988]
-/

namespace Aikhenvald2004

open Semantics.Evidential

/-! ### Terms -/

/-- The terms of Table 2.1: the shapes a term's coverage can take. -/
inductive Term
  | visual | sensory | inferred | assumed | reported | quotative | nonfirsthand
  deriving DecidableEq, Repr

/-- The term a coverage realizes: visual evidence with or without the other senses, non-visual
sensory evidence, inference with or without assumption, assumption alone, hearsay with or
without quotation, quotation alone, or inference and hearsay together without visual evidence
(non-firsthand); any other coverage is no term of the typology. -/
def Term.ofCovers (s : Finset Parameter) : Option Term :=
  if .visual ∈ s ∧ s ⊆ {.visual, .sensory} then some .visual
  else if s = {.sensory} then some .sensory
  else if .inference ∈ s ∧ s ⊆ {.inference, .assumption} then some .inferred
  else if s = {.assumption} then some .assumed
  else if .hearsay ∈ s ∧ s ⊆ {.hearsay, .quotative} then some .reported
  else if s = {.quotative} then some .quotative
  else if .inference ∈ s ∧ .hearsay ∈ s ∧ .visual ∉ s then some .nonfirsthand
  else none

/-- Willett's domain of a term; a non-firsthand term spans two. -/
def Term.coarse : Term → Option CoarseSource
  | .visual | .sensory => some .direct
  | .inferred | .assumed => some .inference
  | .reported | .quotative => some .hearsay
  | .nonfirsthand => none

/-- The terms an inventory distinguishes, if each of its evidentials realizes one. -/
def terms (es : List Evidential) : Option (Finset Term) :=
  (es.mapM (Term.ofCovers ·.covers)).map List.toFinset

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
def HasDefault : Kind → Prop
  | .A2 | .A3 | .A5 | .B5 => True
  | _ => False

instance : DecidablePred HasDefault := fun k => by cases k <;> unfold HasDefault <;> infer_instance

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

/-- B1 groups the parameters into Willett's three domains: direct, inference and report. -/
theorem B1_willett :
    Kind.B1.terms.image Term.coarse = {some .direct, some .inference, some .hearsay} := by
  decide

/-- Every kind, for classification by search. -/
def all : List Kind := [.A1, .A2, .A3, .A4, .A5, .B1, .B2, .B3, .B4, .B5, .C1, .C2, .C3, .D1]

theorem mem_all (k : Kind) : k ∈ all := by cases k <;> decide

end Kind

/-! ### Classifying an inventory -/

/-- The kind of system an inventory instantiates: the kind distinguishing exactly its terms. -/
def kind (es : List Evidential) : Option Kind :=
  (terms es).bind fun S => Kind.all.find? (·.terms = S)

theorem find?_terms_eq_some_iff (S : Finset Term) (k : Kind) :
    Kind.all.find? (·.terms = S) = some k ↔ k.terms = S := by
  refine ⟨fun h => by simpa using List.find?_some h, fun h => ?_⟩
  have hs : (Kind.all.find? (fun x => decide (x.terms = S))).isSome :=
    List.find?_isSome.2 ⟨k, Kind.mem_all k, decide_eq_true h⟩
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.1 hs
  have hk : k'.terms = S := by simpa using List.find?_some hk'
  rw [hk', Kind.terms_injective (hk.trans h.symm)]

theorem kind_eq_some_iff (es : List Evidential) (k : Kind) :
    kind es = some k ↔ terms es = some k.terms := by
  unfold kind
  cases terms es with
  | none => simp
  | some S =>
    simp only [Option.bind_some, Option.some.injEq]
    exact (find?_terms_eq_some_iff S k).trans eq_comm

/-- An empty inventory — an evidentiality strategy, or none at all — is of no kind. -/
theorem kind_nil : kind [] = none := by decide

/-! ### The Fragment languages -/

/-- The inventories classified here are well formed: no parameter is covered twice. -/
theorem sample_wellFormed :
    ∀ es ∈ [Turkish.Evidentiality.evidentials, Abkhaz.Evidentiality.evidentials,
      Bulgarian.Evidentiality.evidentials, Quechua.Evidentiality.evidentials,
      Tuyuca.Evidentiality.evidentials, Tariana.Evidentiality.evidentials,
      Kashaya.Evidentiality.evidentials], Evidential.WellFormed es := by decide

theorem turkish : kind Turkish.Evidentiality.evidentials = some .A2 := by decide

theorem abkhaz : kind Abkhaz.Evidentiality.evidentials = some .A2 := by decide

theorem bulgarian : kind Bulgarian.Evidentiality.evidentials = some .A2 := by decide

theorem quechua : kind Quechua.Evidentiality.evidentials = some .B1 := by decide

theorem tuyuca : kind Tuyuca.Evidentiality.evidentials = some .D1 := by decide

theorem tariana : kind Tariana.Evidentiality.evidentials = some .D1 := by decide

/-- Kashaya's performative covers none of the six parameters, so its paradigm — visual,
auditory, inferential and reported terms besides — is beyond the fourteen kinds. -/
theorem kashaya_unclassified : kind Kashaya.Evidentiality.evidentials = none := by decide

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
