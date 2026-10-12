/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Quantification.Indefinite
public import Linglib.Data.Examples.Haspelmath1997
public import Linglib.Fragments.English.Indefinites
public import Linglib.Fragments.Georgian.Indefinites
public import Linglib.Fragments.Hungarian.Indefinites
public import Linglib.Fragments.German.Indefinites
public import Linglib.Fragments.Japanese.Indefinites
public import Linglib.Fragments.Kannada.Indefinites
public import Linglib.Fragments.Latin.Indefinites
public import Linglib.Fragments.Latvian.Indefinites
public import Linglib.Fragments.Slavic.Russian.Indefinites
public import Linglib.Fragments.Turkish.Indefinites
public import Linglib.Fragments.Yakut.Indefinites

/-!
# Haspelmath (1997): Indefinite Pronouns

This file formalizes Haspelmath's implicational map of indefinite functions and the claims
made over it: the adjacency requirement that every indefinite series cover a connected region of
the nine-function map, the two further principles of §4.5 restricting which connected regions
occur, and the series of eighteen languages of the 40-language sample as Appendix A draws them.

`attestedCombinations` is Table 4.1, the combinations of functions attested in the sample;
`Principle1` and `Principle2` are the restrictions of §4.5, which `excluded_connected` shows to
be independent of adjacency. A connected region with a second function contains a neighbour of
each of its functions, so a series covering a leaf of the map (specific known, direct negation,
free choice) covers the leaf's only neighbour (`mem_of_adjacent_eq_singleton`); the
specific-known case is the ban on the ABA syncretism (`specificUnknown_mem_of_irrealis_mem`).
The paradigms verify the adjacency requirement (`sample_connected`) and the overlap of series
that the book holds against contrast-based accounts of grammatical meaning (`sample_overlap`).
The book's examples for fifteen of the languages are the rows of
`Data/Examples/Haspelmath1997.json`, one row for each variant the book prints in a line; the
figures cover the acceptable rows and exclude the starred ones (`acceptable_covers`,
`ungrammatical_excludes`).

## Implementation notes

The map is `Indefinite.implicationalMap` and the adjacency requirement on a region the
connectedness of the subgraph it induces; the book's numbering of the functions is
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
book's analysis of the series and not a lexical property of the pronoun: a figure records
where a series is possible and not where it is preferred (Russian *-to* is drawn over the
functions of *-nibud'*, which is preferred there), and it fills cells the book has no data for
on the strength of the map (Yakut *da* and Mandarin
bare interrogatives under indirect negation, the Swahili comparative). For those cells
`sample_connected` restates the map; it tests the adjacency requirement on the others. The
pronouns of English, Georgian, German, Hungarian, Kannada, Latin, Latvian, Russian and Yakut
are their Fragments' entries.

## TODO

* The book counts 95 geometrically possible combinations under the adjacency requirement; the
  encoded map has 108 connected regions, and no reading of the edges of Fig. 4.4 recovers the
  book's count.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Haspelmath1997

open Indefinite

/-! ### The map -/

variable {s : Finset HaspelmathFunction} {f g : HaspelmathFunction}

/-- A connected region with a second function contains the only neighbour of each leaf of the
map it contains. -/
theorem mem_of_adjacent_eq_singleton (h : (implicationalMap.induce ↑s).Connected)
    (hs : s.Nontrivial) (hf : f ∈ s) (hfg : f.adjacent = [g]) : g ∈ s := by
  have := hs.coe_sort
  obtain ⟨⟨g', hg'⟩, hadj⟩ := h.preconnected.exists_adj_of_nontrivial ⟨f, hf⟩
  rw [SimpleGraph.induce_adj, implicationalMap_adj, hfg, List.mem_singleton] at hadj
  exact hadj ▸ hg'

/-- Specific known's only neighbour is specific unknown. -/
theorem specificUnknown_mem_of_specificKnown_mem (h : (implicationalMap.induce ↑s).Connected)
    (hs : s.Nontrivial) (hf : .specificKnown ∈ s) : .specificUnknown ∈ s :=
  mem_of_adjacent_eq_singleton h hs hf rfl

/-- A series covering specific known and irrealis non-specific covers specific unknown, so the
ABA syncretism of the three specific functions is not a connected region. -/
theorem specificUnknown_mem_of_irrealis_mem (h : (implicationalMap.induce ↑s).Connected)
    (hk : .specificKnown ∈ s) (hi : .irrealis ∈ s) : .specificUnknown ∈ s :=
  specificUnknown_mem_of_specificKnown_mem h ⟨_, hk, _, hi, by decide⟩ hk

/-- Direct negation's only neighbour is indirect negation. -/
theorem indirectNeg_mem_of_directNeg_mem (h : (implicationalMap.induce ↑s).Connected)
    (hs : s.Nontrivial) (hf : .directNeg ∈ s) : .indirectNeg ∈ s :=
  mem_of_adjacent_eq_singleton h hs hf rfl

/-- Free choice's only neighbour is the comparative. -/
theorem comparative_mem_of_freeChoice_mem (h : (implicationalMap.induce ↑s).Connected)
    (hs : s.Nontrivial) (hf : .freeChoice ∈ s) : .comparative ∈ s :=
  mem_of_adjacent_eq_singleton h hs hf rfl

/-! ### Table 4.1 and the principles of §4.5 -/

/-- `region ns` is the set of functions whose numbers are in `ns`, the book's digit notation. -/
def region (ns : List ℕ) : Finset HaspelmathFunction := Finset.univ.filter (·.number ∈ ns)

/-- The middle of the map is question, conditional, indirect negation and comparative. -/
def middle : Finset HaspelmathFunction := region [4, 5, 6, 8]

/-- A region satisfies Principle 1 if it covers at least three functions whenever it is confined
to the middle of the map. -/
def Principle1 (s : Finset HaspelmathFunction) : Prop := s ⊆ middle → 3 ≤ s.card

instance : DecidablePred Principle1 := fun _ ↦ inferInstanceAs (Decidable (_ → _))

/-- A region satisfies Principle 2 if it does not combine specific known with the comparative or
free-choice function. -/
def Principle2 (s : Finset HaspelmathFunction) : Prop :=
  .specificKnown ∈ s → .comparative ∉ s ∧ .freeChoice ∉ s

instance : DecidablePred Principle2 := fun _ ↦ inferInstanceAs (Decidable (_ → _))

/-- Table 4.1 lists the combinations of functions attested in the 40-language sample, each with
the series the table gives as its example. -/
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

/-- Every attested combination is a connected region of the map, as adjacency requires. -/
theorem attested_connected :
    ∀ c ∈ attestedCombinations, (implicationalMap.induce ↑c.2).Connected := by
  -- Reachability from one function of a region is much cheaper to decide than between all pairs.
  simp only [SimpleGraph.connected_iff_exists_forall_reachable]
  decide +kernel

/-- Every attested combination satisfies both principles. -/
theorem attested_principles :
    ∀ c ∈ attestedCombinations, Principle1 c.2 ∧ Principle2 c.2 := by
  decide

-- Decide the quantifier by walking the list, not by enumerating every region of the map.
attribute [local instance high] List.decidableBAll in
/-- The principles restrict beyond adjacency, since every combination they exclude is a
connected region. -/
theorem excluded_connected :
    ∀ s ∈ excludedByPrinciple1 ++ excludedByPrinciple2, (implicationalMap.induce ↑s).Connected := by
  simp only [SimpleGraph.connected_iff_exists_forall_reachable]
  decide +kernel

attribute [local instance high] List.decidableBAll in
theorem excluded_violate :
    (∀ s ∈ excludedByPrinciple1, ¬ Principle1 s) ∧
      ∀ s ∈ excludedByPrinciple2, ¬ Principle2 s := by
  decide +kernel

/-! ### Eighteen languages of the 40-language sample -/

/-- A `Series` pairs a pronoun of an indefinite series with the region of the map that the
series' figure in Appendix A encloses. -/
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
def series (label form : String) (basis : MorphologicalBasis) (ns : List ℕ)
    (ontology : OntologicalCategory := .person) : Series :=
  ⟨label, { form, ontology, basis }, region ns⟩

/-- The English series (A.3, §4.3.1) are *some-* 12345, *any-* 456789 and *no-* 7. -/
def english : List Series :=
  [ ⟨"some-", English.Indefinites.someEntry, region [1, 2, 3, 4, 5]⟩,
    ⟨"any-", English.Indefinites.anyEntry, region [4, 5, 6, 7, 8, 9]⟩,
    ⟨"no-", English.Indefinites.noEntry, region [7]⟩ ]

/-- The Russian series (A.16) are *koe-* 1, *-to* 2345, *-nibud'* 345, *-libo* 34568, *by to ni
bylo* 568, *ni-* 7, and *ugodno* and the determiner *ljuboj* 9. The *-to*-series is mainly used
specifically but is not excluded from the functions of *-nibud'*, where *-nibud'* is preferred;
*-libo* replaces *-nibud'* under indirect negation and in comparatives. -/
def russian : List Series :=
  [ ⟨"koe-", Russian.Indefinites.koeKto, region [1]⟩,
    ⟨"-to", Russian.Indefinites.ktoTo, region [2, 3, 4, 5]⟩,
    ⟨"-nibud'", Russian.Indefinites.ktoNibud, region [3, 4, 5]⟩,
    ⟨"-libo", Russian.Indefinites.ktoLibo, region [3, 4, 5, 6, 8]⟩,
    ⟨"by to ni bylo", Russian.Indefinites.ktoByToNiBylo, region [5, 6, 8]⟩,
    ⟨"ni-", Russian.Indefinites.nikto, region [7]⟩,
    ⟨"ugodno", Russian.Indefinites.ktoUgodno, region [9]⟩,
    series "ljuboj" "ljuboj" .special [9] .determiner ]

/-- The German series (A.1) are *etwas* 123456, *irgend-* 2345689, temporal *je* 4568, *jeder*
689 and *n-* 7. -/
def german : List Series :=
  [ ⟨"etwas-", German.Indefinites.jemandEntry, region [1, 2, 3, 4, 5, 6]⟩,
    ⟨"irgend-", German.Indefinites.irgendEntry, region [2, 3, 4, 5, 6, 8, 9]⟩,
    ⟨"je", German.Indefinites.jeEntry, region [4, 5, 6, 8]⟩,
    ⟨"jeder", German.Indefinites.jederEntry, region [6, 8, 9]⟩,
    ⟨"n-", German.Indefinites.niemandEntry, region [7]⟩ ]

/-- The Latin series (A.6) are *-dam* 1, *ali-* 2345, *-quam* 4568, the negative series 7, and
*-vis* and *-libet* 9. -/
def latin : List Series :=
  [ ⟨"-dam", Latin.Indefinites.damEntry, region [1]⟩,
    ⟨"ali-", Latin.Indefinites.aliEntry, region [2, 3, 4, 5]⟩,
    ⟨"-quam", Latin.Indefinites.quamEntry, region [4, 5, 6, 8]⟩,
    ⟨"n-", Latin.Indefinites.nemoEntry, region [7]⟩,
    ⟨"-vis", Latin.Indefinites.visEntry, region [9]⟩ ]

/-- The Yakut series (A.25) are *ere* 12, *eme* 345, *da* 6789 with indirect negation
predicted, and *bayarar* 9. -/
def yakut : List Series :=
  [ ⟨"ere", Yakut.Indefinites.ereEntry, region [1, 2]⟩,
    ⟨"eme", Yakut.Indefinites.emeEntry, region [3, 4, 5]⟩,
    ⟨"da", Yakut.Indefinites.daEntry, region [6, 7, 8, 9]⟩,
    ⟨"bayarar", Yakut.Indefinites.bayararEntry, region [9]⟩ ]

/-- The Kannada series (A.35) are *-oo* 2, *-aadaruu* 345 and *-uu* 6789; no series expresses a
referent the speaker has in mind. -/
def kannada : List Series :=
  [ ⟨"-oo", Kannada.Indefinites.ooEntry, region [2]⟩,
    ⟨"-aadaruu", Kannada.Indefinites.aadaruuEntry, region [3, 4, 5]⟩,
    ⟨"-uu", Kannada.Indefinites.uuEntry, region [6, 7, 8, 9]⟩ ]

/-- The Latvian series (A.18) are *kaut* 12345, the figure not separating the specific
functions, *ne-* 7 and *jeb-* 689. The bare interrogatives are also used as indefinites, *kāds*
'somebody' in conditionals and under indirect negation, and the figure draws no region for
them. -/
def latvian : List Series :=
  [ ⟨"kaut", Latvian.Indefinites.kautKas, region [1, 2, 3, 4, 5]⟩,
    ⟨"ne-", Latvian.Indefinites.neviens, region [7]⟩,
    ⟨"jeb-", Latvian.Indefinites.jebkāds, region [6, 8, 9]⟩ ]

/-- The Japanese series (A.38) are *-ka* 12345, *-mo* 678 and *-demo* 9. -/
def japanese : List Series :=
  [ ⟨"-ka", Japanese.Indefinites.dareKa, region [1, 2, 3, 4, 5]⟩,
    ⟨"-mo", Japanese.Indefinites.dareMo, region [6, 7, 8]⟩,
    ⟨"-demo", Japanese.Indefinites.dareDemo, region [9]⟩ ]

/-- The Mandarin Chinese series (A.36) are generic nouns 12, the bare interrogatives in all
non-specific non-emphatic functions 34567 (with no data for indirect negation), *dōu*/*yě* 7,
and the determiner *rènhé* 6789. -/
def mandarin : List Series :=
  [ series "generic noun" "rén" .genericNoun [1, 2],
    series "bare interrogative" "shéi" .interrogative [3, 4, 5, 6, 7],
    series "dōu" "shéi dōu" .interrogative [7],
    series "yě" "shéi yě" .interrogative [7],
    series "rènhé" "rènhé" .special [6, 7, 8, 9] .determiner ]

/-- The Turkish series (A.23) are *bir-* 1234567, *hiç* 467 and *herhangi* 23456789. The figure
starts the *herhangi* outline at irrealis non-specific; the text admits either series in every
function from specific unknown to direct negation and gives *herhangi biri* as a
specific-unknown example, and the region follows the text. -/
def turkish : List Series :=
  [ ⟨"bir-", Turkish.Indefinites.biri, region [1, 2, 3, 4, 5, 6, 7]⟩,
    ⟨"hiç", Turkish.Indefinites.hiçKimse, region [4, 6, 7]⟩,
    ⟨"herhangi", Turkish.Indefinites.herhangiBiri, region [2, 3, 4, 5, 6, 7, 8, 9]⟩ ]

/-- The Hindi/Urdu series (A.22) are *koii* 1234567 and *koii bhii* 3456789. -/
def hindi : List Series :=
  [ series "koii" "koii" .special [1, 2, 3, 4, 5, 6, 7],
    series "bhii" "koii bhii" .special [3, 4, 5, 6, 7, 8, 9] ]

/-- The Italian series (A.10) are *qualche-* 123456, *nessuno* 467 (questions but not
conditionals) and *-unque* 89. -/
def italian : List Series :=
  [ series "qualche-" "qualcuno" .special [1, 2, 3, 4, 5, 6],
    series "nessuno" "nessuno" .special [4, 6, 7],
    series "-unque" "chiunque" .interrogative [8, 9] ]

/-- The Finnish series (A.27) are *eräs* 1, *-kin* 2345, *-kaan* 4678, and *hyvänsä* 589 with
the comparative only as an equative standard. -/
def finnish : List Series :=
  [ series "eräs" "eräs" .special [1],
    series "-kin" "joku" .special [2, 3, 4, 5],
    series "-kaan" "kukaan" .interrogative [4, 6, 7, 8],
    series "hyvänsä" "kuka hyvänsä" .interrogative [5, 8, 9] ]

/-- The Korean series (A.39) are the bare interrogatives and *-nka*, alike at 123456, *-to* 678,
and *-na* and *-tunci* 9. -/
def korean : List Series :=
  [ series "bare interrogative" "nwukwu" .interrogative [1, 2, 3, 4, 5, 6],
    series "-nka" "nwukwu-nka" .interrogative [1, 2, 3, 4, 5, 6],
    series "-to" "nwukwu-to / amu-to" .interrogative [6, 7, 8],
    series "-na" "nwukwu-na" .interrogative [9],
    series "-tunci" "nwukwu-tunci" .interrogative [9] ]

/-- The Hungarian series (A.26) are *vala-* 123456, *sem-* 7, and *akár-* and *bár-* 5689,
excluded from questions. The figure does not draw the marginal *né*-series. -/
def hungarian : List Series :=
  [ ⟨"vala-", Hungarian.Indefinites.valaki, region [1, 2, 3, 4, 5, 6]⟩,
    ⟨"sem-", Hungarian.Indefinites.senki, region [7]⟩,
    ⟨"akár-", Hungarian.Indefinites.akárki, region [5, 6, 8, 9]⟩,
    ⟨"bár-", Hungarian.Indefinites.bárki, region [5, 6, 8, 9]⟩ ]

/-- The Georgian series (A.34) are *-γac* 12, *-me* 34568 and *ara-* 7. The text also puts the
potential *vera-* and prohibitive *nura-* series in direct negation, where the figure does not
draw them, and free choice is expressed by the adjective *nebismieri*, not by a series. -/
def georgian : List Series :=
  [ ⟨"-γac", Georgian.Indefinites.viγac, region [1, 2]⟩,
    ⟨"-me", Georgian.Indefinites.vinMe, region [3, 4, 5, 6, 8]⟩,
    ⟨"ara-", Georgian.Indefinites.araVin, region [7]⟩ ]

/-- The Ancash Quechua series (A.37) are the bare interrogatives for the specific functions,
which the map of the language does not distinguish, and *-pis* 3456789. -/
def quechua : List Series :=
  [ series "bare interrogative" "pi" .interrogative [1, 2],
    series "-pis" "pi-pis" .interrogative [3, 4, 5, 6, 7, 8, 9] ]

/-- The Swahili series (A.33) are generic nouns 1234567 and CL-o CL-ote 456789, with the
comparative predicted. -/
def swahili : List Series :=
  [ series "generic noun" "mtu" .genericNoun [1, 2, 3, 4, 5, 6, 7],
    series "CL-o CL-ote" "mtu ye yote" .special [4, 5, 6, 7, 8, 9] ]

/-- The eighteen languages. -/
def sample : List (List Series) :=
  [ english, russian, german, latin, yakut, kannada, latvian, japanese, mandarin, turkish, hindi,
    italian, finnish, korean, hungarian, georgian, quechua, swahili ]

/-- Every series of the sample covers a connected region, as adjacency requires. -/
theorem sample_connected :
    ∀ p ∈ sample, ∀ e ∈ p, (implicationalMap.induce ↑e.functions).Connected := by
  simp only [SimpleGraph.connected_iff_exists_forall_reachable]
  decide +kernel

/-- Both principles hold of every series in the sample. -/
theorem sample_principles :
    ∀ p ∈ sample, ∀ e ∈ p, Principle1 e.functions ∧ Principle2 e.functions := by
  decide

/-- In most languages several series overlap in distribution, which the book holds against
accounts of grammatical meaning that rely on contrast, since thirteen of the eighteen
paradigms have a function expressed by more than one series. -/
theorem sample_overlap :
    ∀ p ∈ [english, russian, german, latin, yakut, mandarin, turkish, hindi, italian, finnish,
      korean, hungarian, swahili], ¬ p.Pairwise (Disjoint ·.functions ·.functions) := by
  decide

/-- The comparative's other neighbour is indirect negation, and a series may cover it with the
negation functions and without free choice, as Japanese *-mo* does. -/
theorem mo_comparative_with_negation :
    ∃ e ∈ japanese, .comparative ∈ e.functions ∧ .directNeg ∈ e.functions ∧
      .freeChoice ∉ e.functions := by
  decide

/-! ### The book's examples -/


/-- The paradigm of a language of the sample, by Glottocode; Latin, Yakut and Kannada have no
example rows. -/
def paradigm? : String → Option (List Series)
  | "stan1293" => some english
  | "russ1263" => some russian
  | "latv1249" => some latvian
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

def functionTable : List (String × HaspelmathFunction) :=
  [("specificKnown", .specificKnown), ("specificUnknown", .specificUnknown),
    ("irrealis", .irrealis), ("question", .question), ("conditional", .conditional),
    ("indirectNeg", .indirectNeg), ("directNeg", .directNeg), ("comparative", .comparative),
    ("freeChoice", .freeChoice)]

/-- The region the figure of an example's language draws for a series. -/
def region? (e : Datum) (label : String) : Option (Finset HaspelmathFunction) :=
  (paradigm? e.language).bind fun p ↦ (p.find? (·.label = label)).map (·.functions)

/-- The figure draws the series over the function the example illustrates. -/
def Covers (e : Datum) (label : String) : Prop :=
  ∃ f ∈ e.parse? "function" functionTable, ∃ r ∈ region? e label, f ∈ r

/-- The figure leaves the function the example illustrates outside the series. -/
def Excludes (e : Datum) (label : String) : Prop :=
  ∃ f ∈ e.parse? "function" functionTable, ∃ r ∈ region? e label, f ∉ r

instance (e : Datum) (label : String) : Decidable (Covers e label) :=
  inferInstanceAs (Decidable (∃ f ∈ _, ∃ r ∈ _, _))

instance (e : Datum) (label : String) : Decidable (Excludes e label) :=
  inferInstanceAs (Decidable (∃ f ∈ _, ∃ r ∈ _, _))

/-- Every acceptable example of the book lies in the region its figure draws for each of its
series; a sentence with two indefinites has two series, and an indefinite outside the series of
its language has none. -/
theorem acceptable_covers :
    ∀ e ∈ Examples.all, e.judgment = .acceptable → ∀ l ∈ e.features "series", Covers e l := by
  decide +kernel

/-- Every example the book stars out of context lies outside the region its figure draws for
each of its series. The two starred English conditionals are starred for
the speaker's expectation, which their context records, and not for the function. -/
theorem ungrammatical_excludes :
    ∀ e ∈ Examples.all, e.judgment = .ungrammatical → e.context = "" →
      ∀ l ∈ e.features "series", Excludes e l := by
  decide +kernel

end Haspelmath1997
