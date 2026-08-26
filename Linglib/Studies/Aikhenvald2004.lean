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

Here each kind is the set of cells it distinguishes (`Kind.cells`, Table 2.1 together with the
marked terms of the everything-else kinds, a firsthand term occupying the visual column), and
the kind of a language is derived from its Fragment inventory (`kind`). The letters count
choices (`choices_eq_card_cells`), no system expresses all six parameters
(`card_cells_le_five`), D1 is the only five-choice kind (`eq_D1_of_choices`), and B1 is the
grouping that matches Willett's tripartition (`B1_willett`). Turkish, Abkhaz and Bulgarian
derive as A2 once their unmarked pasts are read as evidentiality-neutral rather than firsthand
(`turkish`, `abkhaz`, `bulgarian`), Cuzco Quechua as B1, Tuyuca and Tariana as D1, while
Kashaya's factual/visual, auditory, inferential and reported terms fit no kind
(`kashaya_unclassified`), and the strategy languages have nothing to classify (`kind_nil`).
The book's own illustrations exhaust the cells of their systems (`tariana_illustration`,
`wanka_illustration`, `turkish_illustration`).

## References

* [aikhenvald-2004]
* [barnes-1984]
* [oswalt-1986]
* [willett-1988]
-/

namespace Aikhenvald2004

open Semantics.Evidential
open Semantics.Evidential.Entry (Cell)

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

/-- The cells a system of each kind distinguishes: the rows of Table 2.1, the marked terms of
the everything-else kinds, and a firsthand term in the visual column. -/
def cells : Kind → Finset Cell
  | .A1 => {.visual, .nonfirsthand}
  | .A2 => {.nonfirsthand}
  | .A3 => {.reported}
  | .A4 => {.visual, .reported}
  | .A5 => {.auditory}
  | .B1 => {.visual, .inferred, .reported}
  | .B2 => {.visual, .nonvisualSensory, .inferred}
  | .B3 => {.visual, .nonvisualSensory, .reported}
  | .B4 => {.nonvisualSensory, .inferred, .reported}
  | .B5 => {.reported, .quotative}
  | .C1 => {.visual, .nonvisualSensory, .inferred, .reported}
  | .C2 => {.visual, .inferred, .assumed, .reported}
  | .C3 => {.visual, .inferred, .reported, .quotative}
  | .D1 => {.visual, .nonvisualSensory, .inferred, .assumed, .reported}

/-- The letter counts choices: the distinguished cells, plus one for an everything-else term. -/
theorem choices_eq_card_cells (k : Kind) :
    k.choices = k.cells.card + if k.HasDefault then 1 else 0 := by cases k <;> decide

/-- No system expresses all six parameters. -/
theorem card_cells_le_five (k : Kind) : k.cells.card ≤ 5 := by cases k <;> decide

/-- Only one kind of five-choice system has been found. -/
theorem eq_D1_of_choices (k : Kind) (h : k.choices = 5) : k = .D1 := by
  cases k <;> first | rfl | exact absurd h (by decide)

/-- Distinct kinds distinguish distinct cells. -/
theorem cells_injective : Function.Injective cells := by decide

/-- B1 groups the parameters into Willett's three domains: direct, inference and report. -/
theorem B1_willett :
    Kind.B1.cells.image Cell.toCoarseSource = {some .direct, some .inference, some .hearsay} := by
  decide

/-- Every kind, for classification by search. -/
def all : List Kind := [.A1, .A2, .A3, .A4, .A5, .B1, .B2, .B3, .B4, .B5, .C1, .C2, .C3, .D1]

theorem mem_all (k : Kind) : k ∈ all := by cases k <;> decide

end Kind

/-! ### Classifying an inventory -/

/-- A firsthand term, covering the senses together, occupies the visual column. -/
def Cell.normalize : Cell → Cell
  | .firsthand => .visual
  | c => c

/-- The cells an inventory distinguishes. -/
def cells (es : List Entry) : Finset Cell := (es.map (Cell.normalize ∘ Entry.cell)).toFinset

/-- The kind of system an inventory instantiates: the kind distinguishing exactly its cells. -/
def kind (es : List Entry) : Option Kind := Kind.all.find? (·.cells = cells es)

theorem kind_eq_some_iff (es : List Entry) (k : Kind) :
    kind es = some k ↔ k.cells = cells es := by
  unfold kind
  refine ⟨fun h => by simpa using List.find?_some h, fun h => ?_⟩
  have hs : (Kind.all.find? (fun x => decide (x.cells = cells es))).isSome :=
    List.find?_isSome.2 ⟨k, Kind.mem_all k, decide_eq_true h⟩
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.1 hs
  have hk : k'.cells = cells es := by simpa using List.find?_some hk'
  rw [hk', Kind.cells_injective (hk.trans h.symm)]

/-- An empty inventory — an evidentiality strategy, or none at all — is of no kind. -/
theorem kind_nil : kind [] = none := by decide

/-! ### The Fragment languages -/

theorem turkish : kind Turkish.Evidentiality.evidentials = some .A2 := by decide

theorem abkhaz : kind Abkhaz.Evidentiality.evidentials = some .A2 := by decide

theorem bulgarian : kind Bulgarian.Evidentiality.evidentials = some .A2 := by decide

theorem quechua : kind Quechua.Evidentiality.evidentials = some .B1 := by decide

theorem tuyuca : kind Tuyuca.Evidentiality.evidentials = some .D1 := by decide

theorem tariana : kind Tariana.Evidentiality.evidentials = some .D1 := by decide

/-- Kashaya distinguishes factual/visual, auditory, inferential and reported terms, a system
beyond the fourteen kinds. -/
theorem kashaya_unclassified : kind Kashaya.Evidentiality.evidentials = none := by decide

/-! ### The book's illustrations -/

/-- The cell named by an example's `cell` feature. -/
def Cell.ofString? : String → Option Cell
  | "firsthand" => some .firsthand
  | "visual" => some .visual
  | "nonvisualSensory" => some .nonvisualSensory
  | "auditory" => some .auditory
  | "inferred" => some .inferred
  | "assumed" => some .assumed
  | "reported" => some .reported
  | "quotative" => some .quotative
  | "nonfirsthand" => some .nonfirsthand
  | _ => none

/-- The cells illustrated by the examples from a language. -/
def illustrated (lang : String) : Finset Cell :=
  ((Examples.all.filter (·.language = lang)).filterMap
    (fun r => r.feature? "cell" >>= Cell.ofString?)).toFinset.image Cell.normalize

/-- The Tariana illustration runs through every cell of a D1 system. -/
theorem tariana_illustration : illustrated "tari1256" = Kind.D1.cells := by decide

/-- The Wanka Quechua examples run through every cell of a B1 system. -/
theorem wanka_illustration : illustrated "jauj1238" = Kind.B1.cells := by decide

/-- The Turkish examples show one non-firsthand term covering report, inference and non-visual
perception. -/
theorem turkish_illustration : illustrated "nucl1301" = Kind.A2.cells := by decide

end Aikhenvald2004
