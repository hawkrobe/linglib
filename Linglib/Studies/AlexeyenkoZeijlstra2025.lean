import Linglib.Features.WordOrder
import Linglib.Features.Number.Basic
import Linglib.Features.Gender.Basic
import Linglib.Semantics.Definiteness.Defs
import Linglib.Studies.ZwickyPullum1983
import Linglib.Fragments.Slavic.Russian.Agreement
import Linglib.Fragments.Slavic.Russian.Case
import Linglib.Fragments.Slavic.Serbian.Case
import Linglib.Fragments.German.Case
import Linglib.Fragments.Greek.Case
import Linglib.Fragments.Latin.Case
import Linglib.Fragments.Icelandic.Case
import Linglib.Data.Examples.AlexeyenkoZeijlstra2025

/-!
# Alexeyenko and Zeijlstra (2025): linearization of complex modifiers

The Head-Final Filter — prenominal modifiers contain no post-head material —
both overgenerates (Greek and Russian allow A–XP–N) and undergenerates (Basque,
Chácobo and Eastern Oromo bar the mirror order N–XP–A while Farsi, Atong and
Kalaallisut allow it). The paper's replacement, the Modifier-Noun Adjacency
Generalization, lets an XP separate an attributive adjective from its noun only
if the adjective's agreement marker is shared with the predicative form and
covers every nominal feature, or its attributivizer is morphophonologically
independent of the adjective.

Both conditions are derived here from the paper's analysis: direct modification
is available only to adjectives that carry all φ and case features (`classify`,
read off per-language concord data and the Fragment case inventories); every
other language needs an attributivizer, which forces adjacency exactly when it
is an adjectival affix, overt or null, under the Input Correspondence Principle
(`AttrStatus.Adjacent`). The resulting `Possible` reproduces the decision trees
and agrees with the sample of Table 3 on every language the paper profiles; the
example rows ground the AP-internal orders and the attributive judgments.

## References

* [alexeyenko-zeijlstra-2025]
* [williams-1982]
* [greenberg-1963]
* [ackema-neeleman-2004]
* [zwicky-pullum-1983]
-/

namespace AlexeyenkoZeijlstra2025

open Features Semantics.Definiteness Data.Examples

/-! ### Adjectival concord -/

/-- The nominal features an adjectival form is specified for. -/
structure Concord where
  numbers : Finset Number := ∅
  genders : Finset Gender := ∅
  cases : Finset Case := ∅
  definiteness : Finset Definiteness := ∅
  deriving DecidableEq

/-- Pointwise inclusion of specifications. -/
instance : LE Concord where
  le a b := a.numbers ⊆ b.numbers ∧ a.genders ⊆ b.genders ∧ a.cases ⊆ b.cases ∧
    a.definiteness ⊆ b.definiteness

instance : DecidableLE Concord := λ _ _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A language's adjectival concord: the predicative and attributive forms and the
    φ-features of its DP. Case is present on every DP whether or not it is
    realized, so completeness demands overt case on the adjective as well. -/
structure AdjConcord where
  pred : Concord
  attr : Concord
  dp : Concord

/-- The four ways an adjective can be marked: no overt agreement; agreement on
    attributive forms that predicative forms lack (an agreeing attributivizer, or
    definiteness-sensitive forms as in Icelandic); a shared marker missing some
    nominal feature; a shared marker covering them all. -/
inductive Agreement
  | unmarked
  | distinct
  | incomplete
  | complete
  deriving DecidableEq

/-- Read the marking type off concord data. -/
def AdjConcord.classify (c : AdjConcord) : Agreement :=
  if c.attr = {} then .unmarked
  else if c.pred ≠ c.attr then .distinct
  else if c.dp ≤ c.attr ∧ c.attr.cases.Nonempty then .complete
  else .incomplete

/-! ### Attributivizers -/

/-- Morphophonological status of the attributivizer. -/
inductive AttrStatus
  | adjectivalAffix
  | null
  | clitic
  | freeWord
  | nominalAffix
  deriving DecidableEq

/-- An affix takes the head it selects as its host (the Input Correspondence
    Principle), and the paper extends this to null affixes; clitics, free words and
    affixes on the noun leave the adjective free. -/
def AttrStatus.Adjacent : AttrStatus → Prop
  | .adjectivalAffix | .null => True
  | _ => False

instance : DecidablePred AttrStatus.Adjacent := λ s ↦ by
  cases s <;> simp [AttrStatus.Adjacent] <;> infer_instance

/-- The Zwicky–Pullum cline the paper appeals to for the affix/clitic distinction. -/
def AttrStatus.ofMorphStatus : Morphology.Diagnostics.MorphStatus → AttrStatus
  | .freeWord => .freeWord
  | .simpleClitic | .specialClitic => .clitic
  | .inflAffix | .derivAffix => .adjectivalAffix

/-! ### Profiles and the generalization -/

/-- Side of the noun an attributive adjective occupies. -/
inductive Position
  | prenominal
  | postnominal
  deriving DecidableEq

/-- The AP-internal order that puts the dependent between adjective and noun. -/
def Position.intervening : Position → HeadDirection
  | .prenominal => .headInitial
  | .postnominal => .headFinal

/-- What the generalization needs to know about a language: where its adjectives
    stand, which AP-internal orders its predicative adjectives allow, how they are
    marked, and what attributivizer they take. A language whose adjectives are not
    φ/κ-complete must have an attributivizer. -/
structure Profile where
  positions : Finset Position
  apOrders : Finset HeadDirection
  agreement : Agreement
  attributivizer : Option AttrStatus
  attr_of_incomplete : agreement ≠ .complete → attributivizer ≠ none

/-- An XP may separate the adjective from the noun on the given side: the AP order
    creates the configuration and either the adjective modifies directly or its
    attributivizer does not need to be adjacent to it. -/
def Possible (p : Profile) (pos : Position) : Prop :=
  pos.intervening ∈ p.apOrders ∧
    (p.agreement = .complete ∨ ∃ s ∈ p.attributivizer, ¬ s.Adjacent)

instance (p : Profile) (pos : Position) : Decidable (Possible p pos) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ ∃ s ∈ _, _)))

/-- The Modifier-Noun Adjacency Generalization: intervention only under a complete
    shared agreement marker or an independent attributivizer. -/
theorem mag (p : Profile) (pos : Position) (h : Possible p pos) :
    p.agreement = .complete ∨ ∃ s ∈ p.attributivizer, ¬ s.Adjacent :=
  h.2

/-! ### The languages the paper profiles -/

private def full (cases : Finset Case) (definiteness : Finset Definiteness := ∅) : Concord :=
  { numbers := {.singular, .plural}, genders := {.masculine, .feminine, .neuter}, cases,
    definiteness }

/-- Greek: one form, inflected for gender, number and case in both uses. -/
def greekConcord : AdjConcord :=
  ⟨full Greek.Case.caseInventory, full Greek.Case.caseInventory, full Greek.Case.caseInventory⟩

/-- Russian long forms, the only attributive forms, carry number, gender and case in
    both uses; the caseless short forms are predicative only and never at issue. -/
def russianConcord : AdjConcord :=
  ⟨full Russian.Case.caseInventory, full Russian.Case.caseInventory,
    full Russian.Case.caseInventory⟩

/-- Latin adjectives are marked for gender, number and case in both uses. -/
def latinConcord : AdjConcord :=
  ⟨full Latin.Case.caseInventory, full Latin.Case.caseInventory, full Latin.Case.caseInventory⟩

/-- German predicative adjectives are bare; attributive forms carry gender, number
    and case. -/
def germanConcord : AdjConcord :=
  ⟨{}, full German.Case.caseInventory, full German.Case.caseInventory⟩

private def italianForm : Concord :=
  { numbers := {.singular, .plural}, genders := {.masculine, .feminine} }

/-- Italian adjectives agree in gender and number but never case. -/
def italianConcord : AdjConcord := ⟨italianForm, italianForm, italianForm⟩

/-- English adjectives carry no agreement at all. -/
def englishConcord : AdjConcord := ⟨{}, {}, { numbers := {.singular, .plural} }⟩

/-- Icelandic strong forms appear predicatively; attributive forms additionally
    encode definiteness through the strong/weak choice. -/
def icelandicConcord : AdjConcord :=
  ⟨full Icelandic.Case.caseInventory, full Icelandic.Case.caseInventory {.definite, .indefinite},
    full Icelandic.Case.caseInventory {.definite, .indefinite}⟩

/-- Serbo-Croatian short forms are predicative; attributive long forms add
    definiteness or specificity. -/
def serboCroatianConcord : AdjConcord :=
  ⟨full Serbian.Case.caseInventory, full Serbian.Case.caseInventory {.definite, .indefinite},
    full Serbian.Case.caseInventory {.definite, .indefinite}⟩

private def dutchForm : Concord :=
  { numbers := {.singular, .plural}, genders := {.common, .neuter},
    definiteness := {.definite, .indefinite} }

/-- Dutch predicative adjectives are bare; the attributive schwa is sensitive to
    gender, number and definiteness. -/
def dutchConcord : AdjConcord := ⟨{}, dutchForm, dutchForm⟩

/-- Build a profile from concord data. -/
def Profile.ofConcord (positions : Finset Position) (apOrders : Finset HeadDirection)
    (c : AdjConcord) (attributivizer : Option AttrStatus)
    (h : c.classify ≠ .complete → attributivizer ≠ none := by decide +kernel) : Profile :=
  ⟨positions, apOrders, c.classify, attributivizer, h⟩

def greek : Profile := .ofConcord {.prenominal} {.headInitial} greekConcord none
def russian : Profile := .ofConcord {.prenominal} {.headInitial} russianConcord none
def latin : Profile := .ofConcord {.prenominal} {.headInitial} latinConcord none
def italian : Profile :=
  .ofConcord {.prenominal, .postnominal} {.headInitial} italianConcord (some .null)
def german : Profile :=
  .ofConcord {.prenominal} {.headInitial, .headFinal} germanConcord (some .adjectivalAffix)
def dutch : Profile :=
  .ofConcord {.prenominal} {.headInitial, .headFinal} dutchConcord (some .adjectivalAffix)
def english : Profile := .ofConcord {.prenominal} {.headInitial} englishConcord (some .null)
def icelandic : Profile :=
  .ofConcord {.prenominal} {.headInitial, .headFinal} icelandicConcord (some .adjectivalAffix)
def serboCroatian : Profile :=
  .ofConcord {.prenominal} {.headInitial} serboCroatianConcord (some .adjectivalAffix)

/-- The dimensions a specification covaries in — its projection onto the agreement
    profile of the Fragments. -/
def Concord.dims (c : Concord) : Finset Agreement.Dimension :=
  (if c.numbers = ∅ then ∅ else {.number}) ∪ (if c.genders = ∅ then ∅ else {.gender}) ∪
    (if c.cases = ∅ then ∅ else {.case}) ∪ (if c.definiteness = ∅ then ∅ else {.definiteness})

/-- The Russian long-form specification covaries in exactly the dimensions the
    Fragment's agreement profile records for attributive and predicate targets. -/
theorem russian_dims :
    russianConcord.attr.dims = Russian.Agreement.profile .attributive ∧
    russianConcord.pred.dims = Russian.Agreement.profile .predicate := by
  decide +kernel

/-- The marking types the paper motivates are what the concord data yield. -/
theorem classify_profiled :
    greekConcord.classify = .complete ∧ russianConcord.classify = .complete ∧
    latinConcord.classify = .complete ∧ germanConcord.classify = .distinct ∧
    italianConcord.classify = .incomplete ∧ englishConcord.classify = .unmarked ∧
    icelandicConcord.classify = .distinct ∧ serboCroatianConcord.classify = .distinct ∧
    dutchConcord.classify = .distinct := by
  decide +kernel

/-- Mandarin: no agreement; the attributivizer *de* cliticizes to the AP. -/
def mandarin : Profile :=
  ⟨{.prenominal}, {.headInitial, .headFinal}, .unmarked, some .clitic, by decide⟩

/-- Tagalog: no agreement; the linker is a clitic. -/
def tagalog : Profile := ⟨{.prenominal}, {.headInitial}, .unmarked, some .clitic, by decide⟩

/-- Farsi: no agreement; the ezafe cliticizes to the noun phrase. -/
def farsi : Profile := ⟨{.postnominal}, {.headFinal}, .unmarked, some .clitic, by decide⟩

/-- Atong: no agreement; clitic attributivizer. -/
def atong : Profile := ⟨{.postnominal}, {.headFinal}, .unmarked, some .clitic, by decide⟩

/-- Kalaallisut: affixal agreement shared by predicative and attributive forms and
    covering the nominal features. -/
def kalaallisut : Profile := ⟨{.postnominal}, {.headFinal}, .complete, none, by decide⟩

/-- Basque: the decision tree places it under a null attributivizer with adjectives
    that are not φ/κ-complete. -/
def basque : Profile := ⟨{.postnominal}, {.headFinal}, .unmarked, some .null, by decide⟩

/-- Japanese: strictly head-final APs, so the filter is obeyed trivially. -/
def japanese : Profile := ⟨{.prenominal}, {.headFinal}, .unmarked, some .null, by decide⟩

theorem japanese_trivial : ¬ Possible japanese .prenominal := by decide +kernel

/-! ### Table 3 -/

/-- A language of the sample: name, glottocode, side of the noun, and whether an XP
    can intervene. -/
structure Sample where
  name : String
  glottocode : String
  position : Position
  intervention : Bool

/-- The sample of Table 3. -/
def table3 : List Sample :=
  [ ⟨"Abkhaz", "abkh1244", .prenominal, true⟩, ⟨"Bulgarian", "bulg1262", .prenominal, true⟩,
    ⟨"Polish", "poli1260", .prenominal, true⟩, ⟨"Russian", "russ1263", .prenominal, true⟩,
    ⟨"Latin", "lati1261", .prenominal, true⟩, ⟨"Lithuanian", "lith1251", .prenominal, true⟩,
    ⟨"Mandarin", "mand1415", .prenominal, true⟩, ⟨"Modern Greek", "mode1248", .prenominal, true⟩,
    ⟨"St'át'imcets", "lill1248", .prenominal, true⟩, ⟨"Tagalog", "taga1270", .prenominal, true⟩,
    ⟨"Armenian", "nucl1235", .prenominal, false⟩, ⟨"Dutch", "dutc1256", .prenominal, false⟩,
    ⟨"English", "stan1293", .prenominal, false⟩, ⟨"German", "stan1295", .prenominal, false⟩,
    ⟨"Icelandic", "icel1247", .prenominal, false⟩, ⟨"Estonian", "esto1258", .prenominal, false⟩,
    ⟨"Finnish", "finn1318", .prenominal, false⟩, ⟨"Hungarian", "hung1274", .prenominal, false⟩,
    ⟨"French", "stan1290", .prenominal, false⟩, ⟨"Italian", "ital1282", .prenominal, false⟩,
    ⟨"Portuguese", "port1283", .prenominal, false⟩, ⟨"Romanian", "roma1327", .prenominal, false⟩,
    ⟨"Spanish", "stan1288", .prenominal, false⟩, ⟨"Georgian", "nucl1302", .prenominal, false⟩,
    ⟨"Serbo-Croatian", "sout1528", .prenominal, false⟩,
    ⟨"Atong", "aton1241", .postnominal, true⟩, ⟨"Farsi", "west2369", .postnominal, true⟩,
    ⟨"Kalaallisut", "kala1399", .postnominal, true⟩,
    ⟨"Basque", "basq1248", .postnominal, false⟩, ⟨"Chácobo", "chac1251", .postnominal, false⟩,
    ⟨"Eastern Oromo", "east2652", .postnominal, false⟩ ]

/-- The profile the paper's discussion supports, by glottocode. -/
def profileOf : String → Option Profile
  | "mode1248" => some greek | "russ1263" => some russian | "lati1261" => some latin
  | "ital1282" => some italian | "stan1295" => some german | "dutc1256" => some dutch
  | "stan1293" => some english | "icel1247" => some icelandic | "sout1528" => some serboCroatian
  | "mand1415" => some mandarin | "taga1270" => some tagalog | "west2369" => some farsi
  | "aton1241" => some atong | "kala1399" => some kalaallisut | "basq1248" => some basque
  | _ => none

/-- On every profiled language the generalization returns Table 3's verdict. -/
theorem table3_predicted :
    ∀ s ∈ table3, ∀ p ∈ profileOf s.glottocode, (Possible p s.position ↔ s.intervention) := by
  decide +kernel

/-- The side of the noun alone decides nothing: each block of the table holds both
    verdicts, so no filter stated on position — the Head-Final Filter or its mirror —
    fits the sample. -/
theorem position_insufficient (pos : Position) :
    ∃ s ∈ table3, ∃ t ∈ table3, s.position = pos ∧ t.position = pos ∧ s.intervention ∧
      ¬ t.intervention := by
  cases pos <;> decide

/-! ### The *enough* exception -/

/-- Hosts an attributivizer may attach to when a degree word closes the AP. -/
inductive Host
  | adjective
  | degreeWord

/-- A null affix attaches to the head of the phrase it selects, DegP included; an
    overt affix may attach to a non-lexical head only if that head is itself an
    affix (the Affix Continuity Constraint), which *enough* and *genoeg* are not. -/
def AttrStatus.MayHost : AttrStatus → Host → Prop
  | .null, _ => True
  | .adjectivalAffix, .adjective => True
  | .adjectivalAffix, .degreeWord => False
  | _, _ => True

instance : DecidableRel AttrStatus.MayHost := λ s h ↦ by
  cases s <;> cases h <;> simp [AttrStatus.MayHost] <;> infer_instance

/-! ### Rows -/

/-- The attributivizer a row reports. -/
def attributivizerOf (row : LinguisticExample) : Option AttrStatus :=
  match row.feature? "attributivizer" with
  | some "affix" => some .adjectivalAffix
  | some "null" => some .null
  | some "clitic" => some .clitic
  | _ => none

/-- Every predicative order attested in the rows is in the profile, and every
    attributive judgment on an intervening order is the generalization's. -/
theorem rows_agree :
    ∀ row ∈ Examples.all, ∀ p ∈ profileOf row.language, ∀ o ∈ row.feature? "order",
      (o = "A-XP" → row.judgment = .acceptable → .headInitial ∈ p.apOrders) ∧
      (o = "XP-A" → row.judgment = .acceptable → .headFinal ∈ p.apOrders) ∧
      (o = "A-XP-N" → (row.judgment = .acceptable ↔ Possible p .prenominal)) ∧
      (o = "N-XP-A" → (row.judgment = .acceptable ↔ Possible p .postnominal)) := by
  decide +kernel

/-- A degree word between adjective and noun is tolerated exactly by a null
    attributivizer. -/
theorem degree_rows :
    ∀ row ∈ Examples.all, row.feature? "order" = some "A-Deg-N" →
      ∀ s ∈ attributivizerOf row, (row.judgment = .acceptable ↔ s.MayHost .degreeWord) := by
  decide +kernel

end AlexeyenkoZeijlstra2025
