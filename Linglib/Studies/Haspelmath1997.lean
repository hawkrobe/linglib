/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Combinatorics.SimpleGraph.Connectivity.Connected
import Linglib.Data.Examples.Haspelmath1997
import Linglib.Fragments.English.Indefinites
import Linglib.Fragments.German.Indefinites
import Linglib.Fragments.Kannada.Indefinites
import Linglib.Fragments.Latin.Indefinites
import Linglib.Fragments.Slavic.Russian.Indefinites
import Linglib.Fragments.Yakut.Indefinites

/-!
# Haspelmath (1997): Indefinite Pronouns

This file formalizes the implicational map of [haspelmath-1997] and the distributional claims
made over it: the adjacency requirement that every indefinite series cover a connected region of
the nine-function map, the two further principles of §4.5 restricting which connected regions
occur, and the series of seventeen languages of the 40-language sample as Appendix A draws them.

`attestedCombinations` is Table 4.1, the combinations of functions attested in the sample;
`Principle1` and `Principle2` are the restrictions of §4.5, which `excluded_contiguous` shows to
be independent of adjacency. `exists_adj_mem_of_contiguous` derives from contiguity that every
function of a multi-function region has a map neighbour in the region, so a series covering a
leaf of the map (specific known, direct negation, free choice) covers the leaf's unique
neighbour; the specific-known case is the ban on the ABA syncretism
(`specificUnknown_mem_of_irrealis_mem`). The paradigms verify the
adjacency requirement (`sample_contiguous`) and the overlap of series that the book holds against
contrast-based accounts of grammatical meaning (`sample_overlap`). The book's examples for
fourteen of the languages are the rows of `Data/Examples/Haspelmath1997.json`, one row for each
variant the book prints in a line; the figures cover the acceptable rows and exclude the starred
ones (`acceptable_covers`, `ungrammatical_excludes`), with one idealization (`to_irrealis`).

## Implementation notes

The map is `Indefinite.implicationalMap` and contiguity `Indefinite.Contiguous`, the
connectedness of the induced subgraph; the book's numbering of the functions is
`HaspelmathFunction.number`, so Table 4.1 is entered in the book's digit notation. Each paradigm
follows the figure and text of its Appendix A section rather than Table 4.1 where the two
differ: Hungarian *akár-* is 4589 in the table but excluded from questions and admitted under
indirect negation in A.26, so it is entered as 5689. Finnish *hyvänsä* is entered with the
comparative, which the book restricts to equative standards, and Swahili CL-o CL-ote with the
comparative the book predicts without data; both are the book's own map-driven analyses. Series
that are not pronouns in the book's sense (Georgian free-choice *nebismieri*, Turkish *kimse*,
the Italian determiner *qualsiasi*) are omitted, so a paradigm need not cover all nine
functions.

A `Series` pairs a pronoun with the region its Appendix A figure encloses. The region is the
book's analysis of the series and not a lexical property of the pronoun: a figure idealizes
(Russian *-to* is drawn as specific unknown alone, while the book's own example of *kogo-to*
under *xočet* 'wants' finds its non-specific reading possible beside the preferred *-nibud'*)
and fills cells the book has no data for on the strength of the map (Yakut *da* and Mandarin
bare interrogatives under indirect negation, the Swahili comparative). For those cells
`sample_contiguous` restates the map; it tests the adjacency requirement on the others. The
pronouns of English, German, Kannada, Latin, Russian and Yakut are their Fragments' entries.

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

variable {s : Finset HaspelmathFunction}

/-- Every function of a contiguous region with a second member has a map neighbour in the
region. -/
theorem exists_adj_mem_of_contiguous (h : Contiguous s) (hs : 1 < s.card) {f : HaspelmathFunction}
    (hf : f ∈ s) : ∃ g ∈ s, implicationalMap.Adj f g :=
  h.preconnected.exists_adj_mem_of_nontrivial (Finset.one_lt_card_iff_nontrivial.1 hs) hf

/-- Specific known's only neighbour is specific unknown: no series expresses specific known and
irrealis non-specific without specific unknown, the ABA syncretism. -/
theorem specificUnknown_mem_of_specificKnown_mem (h : Contiguous s) (hs : 1 < s.card)
    (hf : .specificKnown ∈ s) : .specificUnknown ∈ s := by
  obtain ⟨g, hg, hadj⟩ := exists_adj_mem_of_contiguous h hs hf
  simp only [implicationalMap, HaspelmathFunction.adjacent, List.mem_singleton] at hadj
  exact hadj ▸ hg

/-- A series covering specific known and irrealis non-specific covers specific unknown: the ABA
syncretism of the three specific functions is not a connected region. -/
theorem specificUnknown_mem_of_irrealis_mem (h : Contiguous s) (hk : .specificKnown ∈ s)
    (hi : .irrealis ∈ s) : .specificUnknown ∈ s :=
  specificUnknown_mem_of_specificKnown_mem h
    (Finset.one_lt_card.2 ⟨_, hk, _, hi, by decide⟩) hk

/-- Direct negation's only neighbour is indirect negation. -/
theorem indirectNeg_mem_of_directNeg_mem (h : Contiguous s) (hs : 1 < s.card)
    (hf : .directNeg ∈ s) : .indirectNeg ∈ s := by
  obtain ⟨g, hg, hadj⟩ := exists_adj_mem_of_contiguous h hs hf
  simp only [implicationalMap, HaspelmathFunction.adjacent, List.mem_singleton] at hadj
  exact hadj ▸ hg

/-- Free choice's only neighbour is the comparative. -/
theorem comparative_mem_of_freeChoice_mem (h : Contiguous s) (hs : 1 < s.card)
    (hf : .freeChoice ∈ s) : .comparative ∈ s := by
  obtain ⟨g, hg, hadj⟩ := exists_adj_mem_of_contiguous h hs hf
  simp only [implicationalMap, HaspelmathFunction.adjacent, List.mem_singleton] at hadj
  exact hadj ▸ hg

/-! ### Table 4.1 and the principles of §4.5 -/

/-- The functions with the given numbers: the book's digit notation. -/
def region (ns : List ℕ) : Finset HaspelmathFunction := Finset.univ.filter (·.number ∈ ns)

/-- The middle of the map: question, conditional, indirect negation, comparative. -/
def middle : Finset HaspelmathFunction := region [4, 5, 6, 8]

/-- Principle 1: a series confined to the middle of the map covers at least three
functions. -/
def Principle1 (s : Finset HaspelmathFunction) : Prop := s ⊆ middle → 3 ≤ s.card

instance : DecidablePred Principle1 := fun _ ↦ inferInstanceAs (Decidable (_ → _))

/-- Principle 2: the comparative and free-choice functions are never combined with
specific-known. -/
def Principle2 (s : Finset HaspelmathFunction) : Prop :=
  .specificKnown ∈ s → .comparative ∉ s ∧ .freeChoice ∉ s

instance : DecidablePred Principle2 := fun _ ↦ inferInstanceAs (Decidable (_ → _))

/-- Table 4.1: the combinations of functions attested in the 40-language sample, each with the
series the table gives as its example. -/
def attestedCombinations : List (String × Finset HaspelmathFunction) :=
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
def excludedByPrinciple1 : List (Finset HaspelmathFunction) :=
  [region [4], region [5], region [6], region [8], region [4, 5], region [4, 6], region [5, 8],
    region [6, 8]]

/-- The combinations Principle 2 lists as excluded. -/
def excludedByPrinciple2 : List (Finset HaspelmathFunction) :=
  [region [1, 2, 3, 4, 5, 6, 8], region [1, 2, 3, 4, 6, 7, 8], region [1, 2, 3, 4, 6, 8, 9],
    region [1, 2, 3, 4, 6, 7, 8, 9], region [1, 2, 3, 5, 8], region [1, 2, 3, 4, 5, 8, 9]]

/-- The adjacency requirement: every attested combination is a connected region of the map. -/
theorem attested_contiguous : ∀ c ∈ attestedCombinations, Contiguous c.2 := by decide

/-- Every attested combination satisfies both principles. -/
theorem attested_principles :
    ∀ c ∈ attestedCombinations, Principle1 c.2 ∧ Principle2 c.2 := by
  decide

/-- The principles restrict beyond adjacency: every combination they exclude is a connected
region. -/
theorem excluded_contiguous :
    ∀ s ∈ excludedByPrinciple1 ++ excludedByPrinciple2, Contiguous s := by
  decide +kernel

theorem excluded_violate :
    (∀ s ∈ excludedByPrinciple1, ¬ Principle1 s) ∧
      ∀ s ∈ excludedByPrinciple2, ¬ Principle2 s := by
  decide +kernel

/-! ### Seventeen languages of the 40-language sample -/

/-- An indefinite series as a figure of Appendix A draws it: a pronoun of the series with the
region of the map the figure encloses for it. -/
structure Series where
  /-- The book's name for the series, by which its examples are tagged. -/
  label : String
  /-- A member of the series, of the person category where the series has one. -/
  pronoun : IndefinitePronoun
  /-- The functions the series covers. -/
  functions : Finset HaspelmathFunction
  deriving DecidableEq

/-- A series of the person category, the ontological category Appendix A tabulates first, with
its functions in the book's digit notation. -/
private def series (label form : String) (basis : MorphologicalBasis) (ns : List ℕ)
    (ontology : OntologicalCategory := .person) : Series :=
  ⟨label, { form, ontology, basis }, region ns⟩

/-- English (A.3, §4.3.1): *some-* 12345, *any-* 456789, *no-* 7. -/
def english : List Series :=
  [ ⟨"some-", English.Indefinites.someEntry, region [1, 2, 3, 4, 5]⟩,
    ⟨"any-", English.Indefinites.anyEntry, region [4, 5, 6, 7, 8, 9]⟩,
    ⟨"no-", English.Indefinites.noEntry, region [7]⟩ ]

/-- Russian (A.16): *koe-* 1, *-to* 2, *-nibud'* 345, *-libo* 34568, *by to ni bylo* 568,
*ni-* 7, *ugodno* and the determiner *ljuboj* 9; the *-to*-series is mainly specific, and *-libo* replaces *-nibud'* under
indirect negation and in comparatives. -/
def russian : List Series :=
  [ ⟨"koe-", Russian.Indefinites.koeEntry, region [1]⟩,
    ⟨"-to", Russian.Indefinites.toEntry, region [2]⟩,
    ⟨"-nibud'", Russian.Indefinites.nibudEntry, region [3, 4, 5]⟩,
    ⟨"-libo", Russian.Indefinites.liboEntry, region [3, 4, 5, 6, 8]⟩,
    ⟨"by to ni bylo", Russian.Indefinites.byToNiByloEntry, region [5, 6, 8]⟩,
    ⟨"ni-", Russian.Indefinites.niEntry, region [7]⟩,
    ⟨"ugodno", Russian.Indefinites.ugodnoEntry, region [9]⟩,
    series "ljuboj" "ljuboj" .special [9] .determiner ]

/-- German (A.1): *etwas* 123456, *irgend-* 2345689, temporal *je* 4568, *jeder* 689, *n-* 7. -/
def german : List Series :=
  [ ⟨"etwas-", German.Indefinites.jemandEntry, region [1, 2, 3, 4, 5, 6]⟩,
    ⟨"irgend-", German.Indefinites.irgendEntry, region [2, 3, 4, 5, 6, 8, 9]⟩,
    ⟨"je", German.Indefinites.jeEntry, region [4, 5, 6, 8]⟩,
    ⟨"jeder", German.Indefinites.jederEntry, region [6, 8, 9]⟩,
    ⟨"n-", German.Indefinites.niemandEntry, region [7]⟩ ]

/-- Latin (A.6): *-dam* 1, *ali-* 2345, *-quam* 4568, the negative series 7, *-vis* and
*-libet* 9. -/
def latin : List Series :=
  [ ⟨"-dam", Latin.Indefinites.damEntry, region [1]⟩,
    ⟨"ali-", Latin.Indefinites.aliEntry, region [2, 3, 4, 5]⟩,
    ⟨"-quam", Latin.Indefinites.quamEntry, region [4, 5, 6, 8]⟩,
    ⟨"n-", Latin.Indefinites.nemoEntry, region [7]⟩,
    ⟨"-vis", Latin.Indefinites.visEntry, region [9]⟩ ]

/-- Yakut (A.25): *ere* 12, *eme* 345, *da* 6789 with indirect negation predicted, *bayarar*
9. -/
def yakut : List Series :=
  [ ⟨"ere", Yakut.Indefinites.ereEntry, region [1, 2]⟩,
    ⟨"eme", Yakut.Indefinites.emeEntry, region [3, 4, 5]⟩,
    ⟨"da", Yakut.Indefinites.daEntry, region [6, 7, 8, 9]⟩,
    ⟨"bayarar", Yakut.Indefinites.bayararEntry, region [9]⟩ ]

/-- Kannada (A.35): *-oo* 2, *-aadaruu* 345, *-uu* 6789; no series for a referent the speaker
has in mind. -/
def kannada : List Series :=
  [ ⟨"-oo", Kannada.Indefinites.ooEntry, region [2]⟩,
    ⟨"-aadaruu", Kannada.Indefinites.aadaruuEntry, region [3, 4, 5]⟩,
    ⟨"-uu", Kannada.Indefinites.uuEntry, region [6, 7, 8, 9]⟩ ]

/-- Japanese (A.38): *-ka* 12345, *-mo* 678, *-demo* 9. -/
def japanese : List Series :=
  [ series "-ka" "dare-ka" .interrogative [1, 2, 3, 4, 5],
    series "-mo" "dare-mo" .interrogative [6, 7, 8],
    series "-demo" "dare-demo" .interrogative [9] ]

/-- Mandarin Chinese (A.36): generic nouns 12, the bare interrogatives in all non-specific
non-emphatic functions 34567 (with no data for indirect negation), *dōu*/*yě* 7, the determiner
*rènhé* 6789. -/
def mandarin : List Series :=
  [ series "generic noun" "rén" .genericNoun [1, 2],
    series "bare interrogative" "shéi" .interrogative [3, 4, 5, 6, 7],
    series "dōu" "shéi dōu" .interrogative [7],
    series "yě" "shéi yě" .interrogative [7],
    series "rènhé" "rènhé" .special [6, 7, 8, 9] .determiner ]

/-- Turkish (A.23): *bir-* 1234567, *hiç* 467, *herhangi* 23456789. -/
def turkish : List Series :=
  [ series "bir-" "biri(si)" .genericNoun [1, 2, 3, 4, 5, 6, 7],
    series "hiç" "hiç kimse" .genericNoun [4, 6, 7],
    series "herhangi" "herhangi biri" .genericNoun [2, 3, 4, 5, 6, 7, 8, 9] ]

/-- Hindi/Urdu (A.22): *koii* 1234567, *koii bhii* 3456789. -/
def hindi : List Series :=
  [ series "koii" "koii" .special [1, 2, 3, 4, 5, 6, 7],
    series "bhii" "koii bhii" .special [3, 4, 5, 6, 7, 8, 9] ]

/-- Italian (A.10): *qualche-* 123456, *nessuno* 467 (questions but not conditionals),
*-unque* 89. -/
def italian : List Series :=
  [ series "qualche-" "qualcuno" .special [1, 2, 3, 4, 5, 6],
    series "nessuno" "nessuno" .special [4, 6, 7],
    series "-unque" "chiunque" .interrogative [8, 9] ]

/-- Finnish (A.27): *eräs* 1, *-kin* 2345, *-kaan* 4678, *hyvänsä* 589 with the comparative
only as an equative standard. -/
def finnish : List Series :=
  [ series "eräs" "eräs" .special [1],
    series "-kin" "joku" .special [2, 3, 4, 5],
    series "-kaan" "kukaan" .interrogative [4, 6, 7, 8],
    series "hyvänsä" "kuka hyvänsä" .interrogative [5, 8, 9] ]

/-- Korean (A.39): the bare interrogatives and *-nka* 123456 alike, *-to* 678, *-na* and
*-tunci* 9. -/
def korean : List Series :=
  [ series "bare interrogative" "nwukwu" .interrogative [1, 2, 3, 4, 5, 6],
    series "-nka" "nwukwu-nka" .interrogative [1, 2, 3, 4, 5, 6],
    series "-to" "nwukwu-to / amu-to" .interrogative [6, 7, 8],
    series "-na" "nwukwu-na" .interrogative [9],
    series "-tunci" "nwukwu-tunci" .interrogative [9] ]

/-- Hungarian (A.26): *vala-* 123456, *sem-* 7, *akár-* and *bár-* 5689, excluded from
questions. -/
def hungarian : List Series :=
  [ series "vala-" "valaki" .interrogative [1, 2, 3, 4, 5, 6],
    series "sem-" "senki" .interrogative [7],
    series "akár-" "akárki" .interrogative [5, 6, 8, 9],
    series "bár-" "bárki" .interrogative [5, 6, 8, 9] ]

/-- Georgian (A.34): *-yac* 12, *-me* 34568, *ara-* 7; free choice is expressed by the adjective
*nebismieri*, not an indefinite pronoun. -/
def georgian : List Series :=
  [ series "-yac" "vi-yac" .interrogative [1, 2],
    series "-me" "vin-me" .interrogative [3, 4, 5, 6, 8],
    series "ara-" "ara-vin" .interrogative [7] ]

/-- Ancash Quechua (A.37): the bare interrogatives for the specific functions, which the map of
the language does not distinguish, and *-pis* 3456789. -/
def quechua : List Series :=
  [ series "bare interrogative" "pi" .interrogative [1, 2],
    series "-pis" "pi-pis" .interrogative [3, 4, 5, 6, 7, 8, 9] ]

/-- Swahili (A.33): generic nouns 1234567, CL-o CL-ote 456789 with the comparative predicted. -/
def swahili : List Series :=
  [ series "generic noun" "mtu" .genericNoun [1, 2, 3, 4, 5, 6, 7],
    series "CL-o CL-ote" "mtu ye yote" .special [4, 5, 6, 7, 8, 9] ]

/-- The seventeen languages. -/
def sample : List (List Series) :=
  [ english, russian, german, latin, yakut, kannada, japanese, mandarin, turkish, hindi,
    italian, finnish, korean, hungarian, georgian, quechua, swahili ]

/-- The adjacency requirement on the sample: every series covers a connected region. -/
theorem sample_contiguous : ∀ p ∈ sample, ∀ e ∈ p, Contiguous e.functions := by decide

/-- Both principles hold of every series in the sample. -/
theorem sample_principles :
    ∀ p ∈ sample, ∀ e ∈ p, Principle1 e.functions ∧ Principle2 e.functions := by
  decide

/-- In most languages several series overlap in distribution, which the book holds against
accounts of grammatical meaning that rely on contrast: thirteen of the seventeen paradigms have
a function expressed by more than one series. -/
theorem sample_overlap :
    ∀ p ∈ [english, russian, german, latin, yakut, mandarin, turkish, hindi, italian, finnish,
      korean, hungarian, swahili], ¬ p.Pairwise (Disjoint ·.functions ·.functions) := by
  decide

/-- The comparative's other neighbour is indirect negation, and a series may cover it with the
negation functions and without free choice: Japanese *-mo*. -/
theorem mo_comparative_with_negation :
    ∃ e ∈ japanese, .comparative ∈ e.functions ∧ .directNeg ∈ e.functions ∧
      .freeChoice ∉ e.functions := by
  decide

/-! ### The book's examples -/

open Data.Examples (LinguisticExample)

/-- The paradigm of a language of the sample, by Glottocode; Latin, Yakut and Kannada have no
example rows. -/
def paradigm? : String → Option (List Series)
  | "stan1293" => some english
  | "russ1263" => some russian
  | "stan1295" => some german
  | "nucl1643" => some japanese
  | "mand1415" => some mandarin
  | "nucl1301" => some turkish
  | "hind1269" => some hindi
  | "ital1282" => some italian
  | "finn1318" => some finnish
  | "kore1280" => some korean
  | "hung1274" => some hungarian
  | "nucl1302" => some georgian
  | "huay1240" => some quechua
  | "swah1253" => some swahili
  | _ => none

private def functionTable : List (String × HaspelmathFunction) :=
  [("specificKnown", .specificKnown), ("specificUnknown", .specificUnknown),
    ("irrealis", .irrealis), ("question", .question), ("conditional", .conditional),
    ("indirectNeg", .indirectNeg), ("directNeg", .directNeg), ("comparative", .comparative),
    ("freeChoice", .freeChoice)]

/-- The series an example is tagged with: two for a sentence with two indefinites, none for an
indefinite outside the series of its language. -/
def seriesLabels (e : LinguisticExample) : List String :=
  e.paperFeatures.filterMap fun kv ↦ if kv.1 = "series" then some kv.2 else none

/-- The region the figure of an example's language draws for a series. -/
def region? (e : LinguisticExample) (label : String) : Option (Finset HaspelmathFunction) :=
  (paradigm? e.language).bind fun p ↦ (p.find? (·.label = label)).map (·.functions)

/-- The figure draws the series over the function the example illustrates. -/
def Covers (e : LinguisticExample) (label : String) : Prop :=
  ∃ f ∈ e.parse? "function" functionTable, ∃ r ∈ region? e label, f ∈ r

/-- The figure leaves the function the example illustrates outside the series. -/
def Excludes (e : LinguisticExample) (label : String) : Prop :=
  ∃ f ∈ e.parse? "function" functionTable, ∃ r ∈ region? e label, f ∉ r

instance (e : LinguisticExample) (label : String) : Decidable (Covers e label) :=
  inferInstanceAs (Decidable (∃ f ∈ _, ∃ r ∈ _, _))

instance (e : LinguisticExample) (label : String) : Decidable (Excludes e label) :=
  inferInstanceAs (Decidable (∃ f ∈ _, ∃ r ∈ _, _))

/-- The figures cover the book's examples: every acceptable example lies in the region drawn
for each of its series, but for *kogo-to* under *xočet* 'wants'. -/
theorem acceptable_covers :
    ∀ e ∈ Examples.all, e.judgment = .acceptable → e ≠ Examples.ru_A124b_to →
      ∀ l ∈ seriesLabels e, Covers e l := by
  decide +kernel

/-- The figure for Russian idealizes: the non-specific reading of *kogo-to* is possible beside
the preferred *-nibud'*, and the figure draws *-to* as specific unknown alone. -/
theorem to_irrealis :
    Examples.ru_A124b_to.judgment = .acceptable ∧ Excludes Examples.ru_A124b_to "-to" := by
  decide +kernel

/-- The figures exclude what the book stars: every example starred out of context lies outside
the region drawn for each of its series. The two starred English conditionals are starred for
the speaker's expectation, which their context records, and not for the function. -/
theorem ungrammatical_excludes :
    ∀ e ∈ Examples.all, e.judgment = .ungrammatical → e.context = "" →
      ∀ l ∈ seriesLabels e, Excludes e l := by
  decide +kernel

end Haspelmath1997
