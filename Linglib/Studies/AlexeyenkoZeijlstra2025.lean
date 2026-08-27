import Linglib.Features.WordOrder
import Linglib.Studies.ZwickyPullum1983
import Linglib.Fragments.Slavic.Russian.Agreement
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
is available only to adjectives whose agreement profile (`Agreement.Profile`,
the Fragments' target-by-dimension record) is shared across the predicative and
attributive targets and covers every feature of the DP, case included
(`marking`); every other language needs an attributivizer, which forces
adjacency exactly when it is an adjectival affix, overt or null, under the
Input Correspondence Principle (`AttrStatus.Adjacent`). The resulting
`Possible` encodes the decision trees and agrees with the sample of Table 3 on
every language the paper profiles. The example rows carry only their lexical
anchors (adjective, noun, dependent); the linear orders are computed from token
positions (`orderOf`) and checked against the profiles and the judgments.

## References

* [alexeyenko-zeijlstra-2025]
* [williams-1982]
* [greenberg-1963]
* [ackema-neeleman-2004]
* [zwicky-pullum-1983]
-/

namespace AlexeyenkoZeijlstra2025

open Features Data.Examples

/-! ### Agreement marking -/

/-- How an adjective is marked: no overt agreement; agreement on attributive forms
    that predicative forms lack (an agreeing attributivizer, or the
    definiteness-sensitive forms of Icelandic); a shared marker missing some
    nominal feature; a shared marker covering them all. -/
inductive Marking
  | unmarked
  | distinct
  | incomplete
  | complete
  deriving DecidableEq

/-- Read the marking off an agreement profile and the features available in the DP.
    Case is present on every DP whether or not it is realized, so completeness
    demands overt case on the adjective. -/
def marking (agr : Agreement.Profile) (dp : Finset Agreement.Dimension) : Marking :=
  if agr .attributive = ∅ then .unmarked
  else if agr .predicate ≠ agr .attributive then .distinct
  else if dp ⊆ agr .attributive ∧ .case ∈ agr .attributive then .complete
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
    stand, which AP-internal orders its predicative adjectives allow, how they
    agree, which features its DP carries, and what attributivizer they take. A
    language whose adjectives are not φ/κ-complete must have an attributivizer. -/
structure Profile where
  positions : Finset Position
  apOrders : Finset HeadDirection
  agreement : Agreement.Profile
  dp : Finset Agreement.Dimension
  attributivizer : Option AttrStatus
  attr_of_incomplete : marking agreement dp ≠ .complete → attributivizer ≠ none

def Profile.marking (p : Profile) : Marking := AlexeyenkoZeijlstra2025.marking p.agreement p.dp

/-- An XP may separate the adjective from the noun on the given side: the AP order
    creates the configuration and either the adjective modifies directly or its
    attributivizer does not need to be adjacent to it. -/
def Possible (p : Profile) (pos : Position) : Prop :=
  pos.intervening ∈ p.apOrders ∧
    (p.marking = .complete ∨ ∃ s ∈ p.attributivizer, ¬ s.Adjacent)

instance (p : Profile) (pos : Position) : Decidable (Possible p pos) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ ∃ s ∈ _, _)))

/-- The Modifier-Noun Adjacency Generalization: intervention only under a complete
    shared agreement marker or an independent attributivizer. -/
theorem mag (p : Profile) (pos : Position) (h : Possible p pos) :
    p.marking = .complete ∨ ∃ s ∈ p.attributivizer, ¬ s.Adjacent :=
  h.2

/-! ### The languages the paper profiles -/

/-- An adjectival agreement profile from its attributive and predicative targets. -/
private def adj (attr pred : Finset Agreement.Dimension) : Agreement.Profile
  | .attributive => attr
  | .predicate => pred
  | _ => ∅

/-- Gender, number and case on the adjective. -/
private def φκ : Finset Agreement.Dimension := {.number, .gender, .case}

/-- Greek: one form, inflected for gender, number and case in both uses. -/
def greek : Profile := ⟨{.prenominal}, {.headInitial}, adj φκ φκ, φκ, none, by decide +kernel⟩

/-- Russian long forms, the only attributive forms, carry number, gender and case in
    both uses (the Fragment's profile); the caseless short forms are predicative
    only and never at issue. -/
def russian : Profile :=
  ⟨{.prenominal}, {.headInitial}, Russian.Agreement.profile, φκ, none, by decide +kernel⟩

/-- Latin adjectives are marked for gender, number and case in both uses. -/
def latin : Profile := ⟨{.prenominal}, {.headInitial}, adj φκ φκ, φκ, none, by decide +kernel⟩

/-- Kalaallisut: affixal number and case agreement shared by predicative and
    attributive forms. -/
def kalaallisut : Profile :=
  ⟨{.postnominal}, {.headFinal}, adj {.number, .case} {.number, .case}, {.number, .case}, none,
    by decide +kernel⟩

/-- Italian adjectives agree in gender and number but never case; the DP carries
    case regardless. -/
def italian : Profile :=
  ⟨{.prenominal, .postnominal}, {.headInitial}, adj {.number, .gender} {.number, .gender},
    {.number, .gender}, some .null, by decide +kernel⟩

/-- German predicative adjectives are bare; attributive forms carry gender, number
    and case. -/
def german : Profile :=
  ⟨{.prenominal}, {.headInitial, .headFinal}, adj φκ ∅, φκ, some .adjectivalAffix,
    by decide +kernel⟩

/-- Dutch predicative adjectives are bare; the attributive schwa is sensitive to
    gender, number and definiteness. -/
def dutch : Profile :=
  ⟨{.prenominal}, {.headInitial, .headFinal}, adj {.number, .gender, .definiteness} ∅,
    {.number, .gender, .definiteness}, some .adjectivalAffix, by decide +kernel⟩

/-- English adjectives carry no agreement at all. -/
def english : Profile :=
  ⟨{.prenominal}, {.headInitial}, adj ∅ ∅, {.number}, some .null, by decide +kernel⟩

/-- Icelandic strong forms appear predicatively; attributive forms additionally
    encode definiteness through the strong/weak choice. -/
def icelandic : Profile :=
  ⟨{.prenominal}, {.headInitial, .headFinal}, adj (φκ ∪ {.definiteness}) φκ,
    φκ ∪ {.definiteness}, some .adjectivalAffix, by decide +kernel⟩

/-- Serbo-Croatian short forms are predicative; attributive long forms add
    definiteness or specificity. -/
def serboCroatian : Profile :=
  ⟨{.prenominal}, {.headInitial}, adj (φκ ∪ {.definiteness}) φκ, φκ ∪ {.definiteness},
    some .adjectivalAffix, by decide +kernel⟩

/-- Mandarin: no agreement; the attributivizer *de* cliticizes to the AP. -/
def mandarin : Profile :=
  ⟨{.prenominal}, {.headInitial, .headFinal}, adj ∅ ∅, ∅, some .clitic, by decide +kernel⟩

/-- Tagalog: no agreement; the linker is a clitic. -/
def tagalog : Profile :=
  ⟨{.prenominal}, {.headInitial}, adj ∅ ∅, ∅, some .clitic, by decide +kernel⟩

/-- Farsi: no agreement; the ezafe cliticizes to the noun phrase. -/
def farsi : Profile :=
  ⟨{.postnominal}, {.headFinal}, adj ∅ ∅, ∅, some .clitic, by decide +kernel⟩

/-- Atong: no agreement; clitic attributivizer. -/
def atong : Profile :=
  ⟨{.postnominal}, {.headFinal}, adj ∅ ∅, ∅, some .clitic, by decide +kernel⟩

/-- Basque: the decision tree places it under a null attributivizer with adjectives
    that are not φ/κ-complete. -/
def basque : Profile :=
  ⟨{.postnominal}, {.headFinal}, adj ∅ ∅, ∅, some .null, by decide +kernel⟩

/-- Japanese: strictly head-final APs, so the filter is obeyed trivially. -/
def japanese : Profile :=
  ⟨{.prenominal}, {.headFinal}, adj ∅ ∅, ∅, some .null, by decide +kernel⟩

theorem japanese_trivial : ¬ Possible japanese .prenominal := by decide +kernel

/-- The marking types the paper motivates are what the profiles yield. -/
theorem marking_profiled :
    greek.marking = .complete ∧ russian.marking = .complete ∧ latin.marking = .complete ∧
    kalaallisut.marking = .complete ∧ italian.marking = .incomplete ∧
    german.marking = .distinct ∧ dutch.marking = .distinct ∧ icelandic.marking = .distinct ∧
    serboCroatian.marking = .distinct ∧ english.marking = .unmarked := by
  decide +kernel

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

/-- Split on spaces. -/
private def words : List Char → List (List Char)
  | [] => []
  | ' ' :: cs => words cs
  | c :: cs =>
    match words cs with
    | [] => [[c]]
    | w :: ws => if cs.head? = some ' ' then [c] :: w :: ws else (c :: w) :: ws

/-- A row's tokens, punctuation dropped. -/
def tokens (row : LinguisticExample) : List (List Char) :=
  (if row.glossedTokens = [] then words row.primaryText.toList
    else row.surfaceTokens.map String.toList).map (·.filter (· ∉ ['.', ',']))

/-- Position of the token a feature names. -/
def anchor (row : LinguisticExample) (key : String) : Option ℕ :=
  (row.feature? key).bind λ t ↦ (tokens row).findIdx? (· = t.toList)

/-- Linear order of adjective, dependent and noun, read off token positions. -/
inductive Order
  | bare
  | aXp
  | xpA
  | aN
  | nA
  | aXpN
  | xpAN
  | aNXp
  | nAXp
  | nXpA
  | aDegN
  deriving DecidableEq

/-- The order of a row from its anchors: the adjective, the modified noun (absent in
    predicative use), the first word of the adjective's dependent, and a degree
    word. -/
def orderOf (row : LinguisticExample) : Option Order :=
  match anchor row "head", anchor row "noun", anchor row "dependent", anchor row "degree" with
  | some _, none, none, _ => some .bare
  | some h, none, some d, _ => some (if h < d then .aXp else .xpA)
  | some h, some n, some d, _ =>
    if h < n then some (if d < h then .xpAN else if d < n then .aXpN else .aNXp)
    else if d < n then none else some (if d < h then .nXpA else .nAXp)
  | some h, some n, none, deg =>
    if h < n then some (if ∃ g ∈ deg, h < g ∧ g < n then .aDegN else .aN) else some .nA
  | none, _, _, _ => none

example : orderOf Examples.az2025_1b = some .aXpN := by decide +kernel
example : orderOf Examples.az2025_2a = some .aXp := by decide +kernel
example : orderOf Examples.az2025_3a = some .xpA := by decide +kernel
example : orderOf Examples.az2025_4b = some .nXpA := by decide +kernel
example : orderOf Examples.az2025_36b = some .nAXp := by decide +kernel
example : orderOf Examples.az2025_41b = some .xpAN := by decide +kernel
example : orderOf Examples.az2025_71c = some .aDegN := by decide +kernel

/-- Every attributive row stands on a side of the noun the profile allows, every
    predicative order attested is in the profile, and every judgment on an
    intervening order is the generalization's; relative-clause paraphrases are
    outside the generalization. -/
theorem rows_agree :
    ∀ row ∈ Examples.all, ∀ p ∈ profileOf row.language, row.feature? "construction" = none →
      ∀ o ∈ orderOf row,
        (o ∈ [.aN, .aXpN, .xpAN, .aDegN] → .prenominal ∈ p.positions) ∧
        (o ∈ [.nA, .nAXp, .nXpA] → .postnominal ∈ p.positions) ∧
        (o = .aXp → row.judgment = .acceptable → .headInitial ∈ p.apOrders) ∧
        (o = .xpA → row.judgment = .acceptable → .headFinal ∈ p.apOrders) ∧
        (o = .aXpN → (row.judgment = .acceptable ↔ Possible p .prenominal)) ∧
        (o = .nXpA → (row.judgment = .acceptable ↔ Possible p .postnominal)) := by
  decide +kernel

/-- A degree word between adjective and noun is tolerated exactly by a null
    attributivizer. -/
theorem degree_rows :
    ∀ row ∈ Examples.all, orderOf row = some .aDegN →
      ∀ s ∈ attributivizerOf row, (row.judgment = .acceptable ↔ s.MayHost .degreeWord) := by
  decide +kernel

end AlexeyenkoZeijlstra2025
