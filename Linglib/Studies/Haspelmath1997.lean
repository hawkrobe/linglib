/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Sublists
import Linglib.Syntax.Category.Pronoun.IndefiniteParadigm

/-!
# Haspelmath (1997): Indefinite Pronouns

This file formalizes the implicational map of [haspelmath-1997] and the distributional claims
made over it: the adjacency requirement that every indefinite series cover a connected region of
the nine-function map, the two further principles of §4.5 restricting which connected regions
occur, and the series of fourteen languages of the 40-language sample as Appendix A draws them.

`attestedCombinations` is Table 4.1, the combinations of functions attested in the sample;
`Principle1` and `Principle2` are the restrictions of §4.5, which `excluded_contiguous` shows to
be independent of adjacency. `exists_covers_adjacent` derives from contiguity that every function
of a multi-function series has a map neighbour in the series, so a series covering a leaf of the
map (specific-known, direct negation, free choice) covers the leaf's unique neighbour; the
specific-known case is the ban on the `.ABA` syncretism. The paradigms verify the adjacency
requirement (`sample_contiguous`) and the overlap of series that the book holds against
contrast-based accounts of grammatical meaning (`sample_overlap`). The book's examples for these
languages are the rows of `Data/Examples/Haspelmath1997.json`.

## Implementation notes

The map is `HaspelmathFunction.adjacent` and connectedness `HaspelmathFunction.isContiguous`,
both in `Features/Indefinite.lean`; the book's numbering of the functions is
`HaspelmathFunction.number`, so Table 4.1 is entered in the book's digit notation. Each paradigm
follows the figure and text of its Appendix A section rather than Table 4.1 where the two
differ: Hungarian *akár-* is 4589 in the table but excluded from questions and admitted under
indirect negation in A.26, so it is entered as 5689. Finnish *hyvänsä* is entered with the
comparative, which the book restricts to equative standards, and Swahili CL-o CL-ote with the
comparative the book predicts without data; both are the book's own map-driven analyses. Series
that are not pronouns in the book's sense (Georgian free-choice *nebismieri*, Turkish *kimse*,
the Italian determiner *qualsiasi*) are omitted, so a paradigm need not cover all nine
functions. The Fragments' English, German and Russian paradigms record narrower,
competition-driven allocations for the studies that consume them; the paradigms here are the
book's data.

## TODO

* The book counts 95 geometrically possible combinations under the adjacency requirement; the
  encoded map has 108 connected regions, and no reading of the edges of Fig. 4.4 recovers the
  book's count.

## References

* [haspelmath-1997]
-/

namespace Haspelmath1997

open Indefinite

/-! ### The map -/

/-- Every function of a connected region with a second member has a map neighbour in the
region. -/
theorem exists_mem_adjacent_of_isContiguous :
    ∀ l ∈ HaspelmathFunction.all.sublists, HaspelmathFunction.isContiguous l = true →
      ∀ f ∈ l, l ≠ [f] → ∃ g ∈ f.adjacent, g ∈ l := by
  decide +kernel

variable (e : IndefinitePronoun) {f : HaspelmathFunction}

/-- A contiguous series covering `f` and a second function covers a map neighbour of `f`. -/
theorem exists_covers_adjacent (h : HaspelmathFunction.isContiguous e.functionList = true)
    (hf : e.covers f = true) (hc : 1 < e.coverage) : ∃ g ∈ f.adjacent, e.covers g = true := by
  have hl : e.functionList ∈ HaspelmathFunction.all.sublists :=
    List.mem_sublists.2 List.filter_sublist
  have hfl : f ∈ e.functionList := List.mem_filter.2 ⟨HaspelmathFunction.mem_all f, hf⟩
  have hne : e.functionList ≠ [f] := λ h1 => by simp [IndefinitePronoun.coverage, h1] at hc
  obtain ⟨g, hg, hgl⟩ := exists_mem_adjacent_of_isContiguous _ hl h f hfl hne
  exact ⟨g, hg, (List.mem_filter.1 hgl).2⟩

/-- Specific-known's only neighbour is specific-unknown: no series expresses specific-known and
irrealis non-specific without specific-unknown, the `.ABA` syncretism. -/
theorem covers_specificUnknown_of_covers_specificKnown
    (h : HaspelmathFunction.isContiguous e.functionList = true)
    (hf : e.covers .specificKnown = true) (hc : 1 < e.coverage) :
    e.covers .specificUnknown = true := by
  obtain ⟨g, hg, hgc⟩ := exists_covers_adjacent e h hf hc
  simp only [HaspelmathFunction.adjacent, List.mem_singleton] at hg
  exact hg ▸ hgc

/-- Direct negation's only neighbour is indirect negation. -/
theorem covers_indirectNeg_of_covers_directNeg
    (h : HaspelmathFunction.isContiguous e.functionList = true)
    (hf : e.covers .directNeg = true) (hc : 1 < e.coverage) : e.covers .indirectNeg = true := by
  obtain ⟨g, hg, hgc⟩ := exists_covers_adjacent e h hf hc
  simp only [HaspelmathFunction.adjacent, List.mem_singleton] at hg
  exact hg ▸ hgc

/-- Free choice's only neighbour is the comparative. -/
theorem covers_comparative_of_covers_freeChoice
    (h : HaspelmathFunction.isContiguous e.functionList = true)
    (hf : e.covers .freeChoice = true) (hc : 1 < e.coverage) : e.covers .comparative = true := by
  obtain ⟨g, hg, hgc⟩ := exists_covers_adjacent e h hf hc
  simp only [HaspelmathFunction.adjacent, List.mem_singleton] at hg
  exact hg ▸ hgc

/-! ### Table 4.1 and the principles of §4.5 -/

/-- The functions with the given numbers, in map order: the book's digit notation. -/
def region (ns : List Nat) : List HaspelmathFunction :=
  HaspelmathFunction.all.filter (·.number ∈ ns)

/-- The middle of the map: question, conditional, indirect negation, comparative. -/
def middle : List HaspelmathFunction := region [4, 5, 6, 8]

/-- Their Principle 1: a series confined to the middle of the map covers at least three
functions. -/
def Principle1 (l : List HaspelmathFunction) : Prop :=
  (∀ f ∈ l, f ∈ middle) → 3 ≤ l.length

instance (l : List HaspelmathFunction) : Decidable (Principle1 l) :=
  inferInstanceAs (Decidable (_ → _))

/-- Their Principle 2: the comparative and free-choice functions are never combined with
specific-known. -/
def Principle2 (l : List HaspelmathFunction) : Prop :=
  .specificKnown ∈ l → .comparative ∉ l ∧ .freeChoice ∉ l

instance (l : List HaspelmathFunction) : Decidable (Principle2 l) :=
  inferInstanceAs (Decidable (_ → _))

/-- Table 4.1: the combinations of functions attested in the 40-language sample, each with the
series the table gives as its example. -/
def attestedCombinations : List (String × List HaspelmathFunction) :=
  [ ("Russian koe-", region [1]), ("Kazakh älde-", region [1, 2]),
    ("Serbian/Croatian ne-", region [1, 2, 3]), ("English some-", region [1, 2, 3, 4, 5]),
    ("German etwas", region [1, 2, 3, 4, 5, 6]), ("Swedish någon", region [1, 2, 3, 4, 5, 6, 7]),
    ("Kannada -oo", region [2]), ("Basque bait-", region [2, 3]),
    ("Latin ali-, Greek ka-", region [2, 3, 4, 5]),
    ("Portuguese qualquer", region [2, 3, 4, 5, 6, 7, 8, 9]),
    ("German irgend", region [2, 3, 4, 5, 6, 8, 9]), ("Russian -nibud'", region [3, 4, 5]),
    ("Ossetic is-", region [3, 4, 5, 6]), ("Greek tipota", region [3, 4, 5, 6, 7]),
    ("Nanay -daa", region [3, 4, 5, 6, 7, 8]), ("Hindi/Urdu bhii", region [3, 4, 5, 6, 7, 8, 9]),
    ("Lithuanian nors", region [3, 4, 5, 6, 8]), ("Dutch dan ook", region [3, 4, 5, 6, 8, 9]),
    ("Hebrew iš", region [4, 5, 6, 7]), ("Catalan cap", region [4, 5, 6, 7, 8]),
    ("English any", region [4, 5, 6, 7, 8, 9]), ("German je", region [4, 5, 6, 8]),
    ("Serbian/Croatian bilo", region [4, 5, 6, 8, 9]), ("Hungarian akár", region [4, 5, 8, 9]),
    ("Italian nessuno", region [4, 6, 7]), ("Finnish -kaan", region [4, 6, 7, 8]),
    ("Icelandic nokkur", region [4, 6, 8]), ("Russian by to ni bylo", region [5, 6, 8]),
    ("Bulgarian -to i da e", region [5, 6, 8, 9]), ("Modern Greek -dhipote", region [5, 8, 9]),
    ("Icelandic n-", region [6, 7]), ("Maltese ebda", region [6, 7, 8]),
    ("Kannada -uu", region [6, 7, 8, 9]), ("German jeder", region [6, 8, 9]),
    ("German n-", region [7]), ("Swedish som helst", region [8, 9]),
    ("Icelandic sem er", region [9]) ]

/-- The combinations Principle 1 lists as excluded. -/
def excludedByPrinciple1 : List (List HaspelmathFunction) :=
  [region [4], region [5], region [6], region [8], region [4, 5], region [4, 6], region [5, 8],
    region [6, 8]]

/-- The combinations Principle 2 lists as excluded. -/
def excludedByPrinciple2 : List (List HaspelmathFunction) :=
  [region [1, 2, 3, 4, 5, 6, 8], region [1, 2, 3, 4, 6, 7, 8], region [1, 2, 3, 4, 6, 8, 9],
    region [1, 2, 3, 4, 6, 7, 8, 9], region [1, 2, 3, 5, 8], region [1, 2, 3, 4, 5, 8, 9]]

/-- The adjacency requirement: every attested combination is a connected region of the map. -/
theorem attested_contiguous :
    ∀ c ∈ attestedCombinations, HaspelmathFunction.isContiguous c.2 = true := by
  decide

/-- Every attested combination satisfies both principles. -/
theorem attested_principles :
    ∀ c ∈ attestedCombinations, Principle1 c.2 ∧ Principle2 c.2 := by
  decide

/-- The principles restrict beyond adjacency: every combination they exclude is a connected
region. -/
theorem excluded_contiguous :
    ∀ l ∈ excludedByPrinciple1 ++ excludedByPrinciple2,
      HaspelmathFunction.isContiguous l = true := by
  decide

theorem excluded_violate :
    (∀ l ∈ excludedByPrinciple1, ¬ Principle1 l) ∧
      ∀ l ∈ excludedByPrinciple2, ¬ Principle2 l := by
  decide

/-! ### Fourteen languages of the 40-language sample -/

/-- A series of the person category, the ontological category Appendix A tabulates first. -/
private def series (form : String) (basis : MorphologicalBasis)
    (functions : Finset HaspelmathFunction) (ontology : OntologicalCategory := .person) :
    IndefinitePronoun :=
  { form, ontology, basis, functions }

/-- English (A.3, §4.3.1): *some-* 12345, *any-* 456789, *no-* 7. -/
def english : IndefiniteParadigm :=
  { language := "English", isoCode := "eng",
    forms :=
      [ series "some-" .genericNoun
          {.specificKnown, .specificUnknown, .irrealis, .question, .conditional},
        series "any-" .genericNoun
          {.question, .conditional, .indirectNeg, .directNeg, .comparative, .freeChoice},
        series "no-" .genericNoun {.directNeg} ] }

/-- Russian (A.16): *koe-* 1, *-to* 2, *-nibud'* 345, *-libo* 34568, *by to ni bylo* 568,
*ni-* 7, *ugodno* 9; the *-to*-series is mainly specific, and *-libo* replaces *-nibud'* under
indirect negation and in comparatives. -/
def russian : IndefiniteParadigm :=
  { language := "Russian", isoCode := "rus",
    forms :=
      [ series "koe-kto" .interrogative {.specificKnown},
        series "kto-to" .interrogative {.specificUnknown},
        series "kto-nibud'" .interrogative {.irrealis, .question, .conditional},
        series "kto-libo" .interrogative
          {.irrealis, .question, .conditional, .indirectNeg, .comparative},
        series "kto by to ni bylo" .interrogative {.conditional, .indirectNeg, .comparative},
        series "nikto" .interrogative {.directNeg},
        series "kto ugodno" .interrogative {.freeChoice} ] }

/-- German (A.1): *etwas* 123456, *irgend-* 2345689, temporal *je* 4568, *jeder* 689, *n-* 7. -/
def german : IndefiniteParadigm :=
  { language := "German", isoCode := "deu",
    forms :=
      [ series "jemand" .genericNoun
          {.specificKnown, .specificUnknown, .irrealis, .question, .conditional, .indirectNeg},
        series "irgendwer" .special
          {.specificUnknown, .irrealis, .question, .conditional, .indirectNeg, .comparative,
            .freeChoice},
        series "je" .special {.question, .conditional, .indirectNeg, .comparative} .time,
        series "jeder" .special {.indirectNeg, .comparative, .freeChoice},
        series "niemand" .genericNoun {.directNeg} ] }

/-- Japanese (A.38): *-ka* 12345, *-mo* 678, *-demo* 9. -/
def japanese : IndefiniteParadigm :=
  { language := "Japanese", isoCode := "jpn",
    forms :=
      [ series "dare-ka" .interrogative
          {.specificKnown, .specificUnknown, .irrealis, .question, .conditional},
        series "dare-mo" .interrogative {.indirectNeg, .directNeg, .comparative},
        series "dare-demo" .interrogative {.freeChoice} ] }

/-- Mandarin Chinese (A.36): generic nouns 12, the bare interrogatives in all non-specific
non-emphatic functions 34567 (with no data for indirect negation), *dōu*/*yě* 7, the determiner
*rènhé* 6789. -/
def mandarin : IndefiniteParadigm :=
  { language := "Mandarin Chinese", isoCode := "cmn",
    forms :=
      [ series "rén" .genericNoun {.specificKnown, .specificUnknown},
        series "shéi" .interrogative
          {.irrealis, .question, .conditional, .indirectNeg, .directNeg},
        series "shéi dōu / shéi yě" .interrogative {.directNeg},
        series "rènhé" .special {.indirectNeg, .directNeg, .comparative, .freeChoice}
          .determiner ] }

/-- Turkish (A.23): *bir-* 1234567, *hiç* 467, *herhangi* 23456789. -/
def turkish : IndefiniteParadigm :=
  { language := "Turkish", isoCode := "tur",
    forms :=
      [ series "biri(si)" .genericNoun
          {.specificKnown, .specificUnknown, .irrealis, .question, .conditional, .indirectNeg,
            .directNeg},
        series "hiç kimse" .genericNoun {.question, .indirectNeg, .directNeg},
        series "herhangi biri" .genericNoun
          {.specificUnknown, .irrealis, .question, .conditional, .indirectNeg, .directNeg,
            .comparative, .freeChoice} ] }

/-- Hindi/Urdu (A.22): *koii* 1234567, *koii bhii* 3456789. -/
def hindi : IndefiniteParadigm :=
  { language := "Hindi/Urdu", isoCode := "hin",
    forms :=
      [ series "koii" .special
          {.specificKnown, .specificUnknown, .irrealis, .question, .conditional, .indirectNeg,
            .directNeg},
        series "koii bhii" .special
          {.irrealis, .question, .conditional, .indirectNeg, .directNeg, .comparative,
            .freeChoice} ] }

/-- Italian (A.10): *qualche-* 123456, *nessuno* 467 (questions but not conditionals),
*-unque* 89. -/
def italian : IndefiniteParadigm :=
  { language := "Italian", isoCode := "ita",
    forms :=
      [ series "qualcuno" .special
          {.specificKnown, .specificUnknown, .irrealis, .question, .conditional, .indirectNeg},
        series "nessuno" .special {.question, .indirectNeg, .directNeg},
        series "chiunque" .interrogative {.comparative, .freeChoice} ] }

/-- Finnish (A.27): *eräs* 1, *-kin* 2345, *-kaan* 4678, *hyvänsä* 589 with the comparative
only as an equative standard. -/
def finnish : IndefiniteParadigm :=
  { language := "Finnish", isoCode := "fin",
    forms :=
      [ series "eräs" .special {.specificKnown},
        series "joku" .special {.specificUnknown, .irrealis, .question, .conditional},
        series "kukaan" .interrogative {.question, .indirectNeg, .directNeg, .comparative},
        series "kuka hyvänsä" .interrogative {.conditional, .comparative, .freeChoice} ] }

/-- Korean (A.39): the bare interrogatives and *-nka* 123456 alike, *-to* 678, *-na* and
*-tunci* 9. -/
def korean : IndefiniteParadigm :=
  { language := "Korean", isoCode := "kor",
    forms :=
      [ series "nwukwu / nwukwu-nka" .interrogative
          {.specificKnown, .specificUnknown, .irrealis, .question, .conditional, .indirectNeg},
        series "nwukwu-to / amu-to" .interrogative {.indirectNeg, .directNeg, .comparative},
        series "nwukwu-na / nwukwu-tunci" .interrogative {.freeChoice} ] }

/-- Hungarian (A.26): *vala-* 123456, *sem-* 7, *akár-* and *bár-* 5689, excluded from
questions. -/
def hungarian : IndefiniteParadigm :=
  { language := "Hungarian", isoCode := "hun",
    forms :=
      [ series "valaki" .interrogative
          {.specificKnown, .specificUnknown, .irrealis, .question, .conditional, .indirectNeg},
        series "senki" .interrogative {.directNeg},
        series "akárki / bárki" .interrogative
          {.conditional, .indirectNeg, .comparative, .freeChoice} ] }

/-- Georgian (A.34): *-yac* 12, *-me* 34568, *ara-* 7; free choice is expressed by the adjective
*nebismieri*, not an indefinite pronoun. -/
def georgian : IndefiniteParadigm :=
  { language := "Georgian", isoCode := "kat",
    forms :=
      [ series "vi-yac" .interrogative {.specificKnown, .specificUnknown},
        series "vin-me" .interrogative
          {.irrealis, .question, .conditional, .indirectNeg, .comparative},
        series "ara-vin" .interrogative {.directNeg} ] }

/-- Ancash Quechua (A.37): the bare interrogatives for the specific functions, which the map of
the language does not distinguish, and *-pis* 3456789. -/
def quechua : IndefiniteParadigm :=
  { language := "Ancash Quechua", isoCode := "qwh",
    forms :=
      [ series "pi" .interrogative {.specificKnown, .specificUnknown},
        series "pi-pis" .interrogative
          {.irrealis, .question, .conditional, .indirectNeg, .directNeg, .comparative,
            .freeChoice} ] }

/-- Swahili (A.33): generic nouns 1234567, CL-o CL-ote 456789 with the comparative predicted. -/
def swahili : IndefiniteParadigm :=
  { language := "Swahili", isoCode := "swh",
    forms :=
      [ series "mtu" .genericNoun
          {.specificKnown, .specificUnknown, .irrealis, .question, .conditional, .indirectNeg,
            .directNeg},
        series "mtu ye yote" .special
          {.question, .conditional, .indirectNeg, .directNeg, .comparative, .freeChoice} ] }

/-- The fourteen languages. -/
def sample : List IndefiniteParadigm :=
  [ english, russian, german, japanese, mandarin, turkish, hindi, italian, finnish, korean,
    hungarian, georgian, quechua, swahili ]

/-- The adjacency requirement on the sample: every series covers a connected region. -/
theorem sample_contiguous : ∀ p ∈ sample, p.AllContiguous := by decide

/-- Both principles hold of every series in the sample. -/
theorem sample_principles :
    ∀ p ∈ sample, ∀ e ∈ p.forms,
      Principle1 e.functionList ∧ Principle2 e.functionList := by
  decide

/-- In most languages several series overlap in distribution, which the book holds against
accounts of grammatical meaning that rely on contrast: eleven of the fourteen paradigms have a
function expressed by more than one series. -/
theorem sample_overlap :
    ∀ p ∈ [english, russian, german, mandarin, turkish, hindi, italian, finnish, korean,
      hungarian, swahili], ¬ p.FormsDisjoint := by
  decide

/-- The comparative's other neighbour is indirect negation, and a series may cover it with the
negation functions and without free choice: Japanese *-mo*. -/
theorem mo_comparative_with_negation :
    ∃ e ∈ japanese.forms,
      e.covers .comparative = true ∧ e.covers .directNeg = true ∧
        e.covers .freeChoice = false := by
  decide

end Haspelmath1997
