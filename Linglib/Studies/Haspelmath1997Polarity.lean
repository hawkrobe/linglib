/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Pronoun.IndefiniteParadigm
import Linglib.Fragments.English.PolarityItems
import Linglib.Fragments.Italian.PolarityItems
import Linglib.Fragments.Slavic.Russian.PolarityItems
import Linglib.Fragments.German.PolarityItems
import Linglib.Fragments.Japanese.PolarityItems
import Linglib.Fragments.Korean.PolarityItems
import Linglib.Fragments.Mandarin.PolarityItems
import Linglib.Fragments.Turkish.PolarityItems
import Linglib.Fragments.Hindi.PolarityItems
import Linglib.Fragments.Finnish.PolarityItems
import Linglib.Fragments.Hungarian.PolarityItems
import Linglib.Fragments.Georgian.PolarityItems
import Linglib.Fragments.Quechua.PolarityItems
import Linglib.Fragments.Yoruba.PolarityItems
import Linglib.Fragments.Thai.PolarityItems
import Linglib.Fragments.Tagalog.PolarityItems
import Linglib.Fragments.Swahili.PolarityItems

/-!
# Haspelmath (1997): polarity-side indefinite typology

[haspelmath-1997]'s implicational map arranges nine indefinite-series
functions so that every series covers a connected region (Fig. 4.4 — the
geometry of `Indefinite.HaspelmathFunction.adjacent`). This file states
the polarity-side claims over a 17-language sample of
`IndefiniteParadigm`s: contiguity, coverage, attested series overlap, and
decide-checks connecting the paradigms to the per-language
`Fragments/{Lang}/PolarityItems.lean` entries.

The German, Hungarian, Japanese, Korean, and Quechua (Ancash) paradigms
are verified against the book (appendix A.1, A.26, A.37–A.39; Table 4.1);
the rest are hand-stipulated pending the same pass. English in particular
follows a narrower polarity-view allocation than both the book's coding
(Table 4.1: *some-* 12345, *any-* 456789) and the
[degano-aloni-2025]-shaped `Fragments/English/Indefinites.lean`; the
Fragment-vs-Studies divergence is theorem-ized in `Studies/Bubnov2026.lean`
§11 ([bubnov-2026] reads coverage distributionally, net of paradigmatic
competition).

## Main results

* `all_languages_contiguous` — the map hypothesis on the sample.
* `all_languages_cover_all_functions` — every paradigm covers all nine
  functions.
* `russian_not_disjoint`, `german_not_disjoint`, `hungarian_not_disjoint`
  — series overlap is attested and normal (p. 76), not a defect.
* `freeChoice_multifunction_implies_comparative`,
  `japanese_comparative_patterns_with_negation` — free choice's only map
  neighbour is the comparative, which may instead pattern with negation.
* `bridges_negation`, `bridges_question`, `bridges_npiFci` — licensing
  checks against the polarity Fragments.

## Implementation notes

Paradigms are stipulated rather than derived from
`Fragments/{Lang}/Indefinites.lean`: the per-form `functions` field
commits to one analysis of the map partition, and this file's
contiguity-driven encoding genuinely differs from the Fragments'
competition-driven one (English, German, Russian).
`Studies/Chierchia2006.lean` consumes the `english`/`italian`/`german`/
`mandarin` paradigms. The sibling `Studies/Haspelmath1997.lean` owns the
indefinite-typology angle (Fragment-derived paradigms, WALS F46A bridge).
Substrate: `Features/Indefinite.lean` (map), and
`Syntax/Pronoun/IndefiniteParadigm.lean` (paradigms; the decidable
`AllContiguous`/`CoversAllFunctions`/`FormsDisjoint` predicates).
-/

namespace Haspelmath1997Polarity

open _root_.Indefinite

/-! ### The 17-language sample -/

/-- English: 4 generic-noun-based series in the polarity-view allocation
    (narrower than Table 4.1 — see the module docstring). -/
def english : IndefiniteParadigm :=
  { language := "English"
  , isoCode := "eng"
  , forms :=
    [ { form := "some-",
        ontology := .person,
        basis := .genericNoun,
        functions := {.specificKnown, .specificUnknown} }
    , { form := "any- (NPI)",
        ontology := .person,
        basis := .genericNoun,
        functions := {.irrealis, .question, .conditional, .indirectNeg} }
    , { form := "no-",
        ontology := .person,
        basis := .genericNoun,
        functions := {.directNeg} }
    , { form := "any- (FC)",
        ontology := .person,
        basis := .genericNoun,
        functions := {.comparative, .freeChoice} } ] }

/-- Russian: 6 interrogative-based series. Coverage follows
    [degano-aloni-2025] Table 2 (кое- SK; -то epistemic; -то and -нибудь
    both admit non-specific uses, so Russian fails `FormsDisjoint`); the
    Fragment encodes -то more narrowly per [bubnov-2026], and both
    readings coexist by design (`Studies/Bubnov2026.lean` §11). -/
def russian : IndefiniteParadigm :=
  { language := "Russian"
  , isoCode := "rus"
  , forms :=
    [ { form := "кое-кто (koe-kto)",
        ontology := .person,
        basis := .interrogative,
        functions := {.specificKnown} }
    , { form := "кто-то (kto-to)",
        ontology := .person,
        basis := .interrogative,
        functions := {.specificUnknown, .irrealis} }
    , { form := "кто-нибудь (kto-nibud')",
        ontology := .person,
        basis := .interrogative,
        functions := {.irrealis} }
    , { form := "кто-либо (kto-libo)",
        ontology := .person,
        basis := .interrogative,
        functions := {.question, .conditional, .indirectNeg} }
    , { form := "никто (nikto)",
        ontology := .person,
        basis := .interrogative,
        functions := {.directNeg} }
    , { form := "кто угодно (kto ugodno)",
        ontology := .person,
        basis := .interrogative,
        functions := {.comparative, .freeChoice} } ] }

/-- German: 4 person-form series (A.1; Table 4.1: *etwas* 123456, *irgend*
    2345689, *jeder* 689, *n-* 7). The temporal *je*-series (4568) has no
    person form; the series overlap heavily (p. 76). -/
def german : IndefiniteParadigm :=
  { language := "German"
  , isoCode := "deu"
  , forms :=
    [ { form := "jemand",
        ontology := .person,
        basis := .genericNoun,
        functions := {.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional, .indirectNeg} }
    , { form := "irgendwer",
        ontology := .person,
        basis := .special,
        functions := {.specificUnknown, .irrealis, .question, .conditional,
                      .indirectNeg, .comparative, .freeChoice} }
    , { form := "niemand",
        ontology := .person,
        basis := .genericNoun,
        functions := {.directNeg} }
    , { form := "jeder",
        ontology := .person,
        basis := .genericNoun,
        functions := {.indirectNeg, .comparative, .freeChoice} } ] }

/-- Japanese: 3 interrogative-based series (A.38): *-ka* non-negative;
    *-mo* the negations plus comparative (*dare-yori-mo*, A284), with
    verbal negation under direct negation; *-demo* free choice only
    (A287). -/
def japanese : IndefiniteParadigm :=
  { language := "Japanese"
  , isoCode := "jpn"
  , forms :=
    [ { form := "dare-ka",
        ontology := .person,
        basis := .interrogative,
        functions := {.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional} }
    , { form := "dare-mo (neg)",
        ontology := .person,
        basis := .interrogative,
        functions := {.indirectNeg, .directNeg, .comparative} }
    , { form := "dare-demo",
        ontology := .person,
        basis := .interrogative,
        functions := {.freeChoice} } ] }

/-- Mandarin: 2 series, mixed bases (*yǒu rén* existential, *shéi*
    interrogative). -/
def mandarin : IndefiniteParadigm :=
  { language := "Mandarin Chinese"
  , isoCode := "cmn"
  , forms :=
    [ { form := "yǒu rén (有人)",
        ontology := .person,
        basis := .existentialConstruction,
        functions := {.specificKnown, .specificUnknown} }
    , { form := "shéi (谁, non-interrog.)",
        ontology := .person,
        basis := .interrogative,
        functions := {.irrealis, .question, .conditional, .indirectNeg,
                      .directNeg, .comparative, .freeChoice} } ] }

/-- Turkish: 5 generic-noun-based series (*bir-* 'one'). -/
def turkish : IndefiniteParadigm :=
  { language := "Turkish"
  , isoCode := "tur"
  , forms :=
    [ { form := "birisi",
        ontology := .person,
        basis := .genericNoun,
        functions := {.specificKnown, .specificUnknown} }
    , { form := "biri",
        ontology := .person,
        basis := .genericNoun,
        functions := {.irrealis} }
    , { form := "kimse",
        ontology := .person,
        basis := .genericNoun,
        functions := {.question, .conditional, .indirectNeg} }
    , { form := "hiç kimse",
        ontology := .person,
        basis := .genericNoun,
        functions := {.directNeg} }
    , { form := "herhangi biri",
        ontology := .person,
        basis := .genericNoun,
        functions := {.comparative, .freeChoice} } ] }

/-- Hindi-Urdu: 3 series on the special base *koii*. -/
def hindi : IndefiniteParadigm :=
  { language := "Hindi-Urdu"
  , isoCode := "hin"
  , forms :=
    [ { form := "koii",
        ontology := .person,
        basis := .special,
        functions := {.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional} }
    , { form := "koii nahiiN",
        ontology := .person,
        basis := .special,
        functions := {.indirectNeg, .directNeg} }
    , { form := "koii bhii",
        ontology := .person,
        basis := .special,
        functions := {.comparative, .freeChoice} } ] }

/-- Italian: 3 generic-noun-based series. -/
def italian : IndefiniteParadigm :=
  { language := "Italian"
  , isoCode := "ita"
  , forms :=
    [ { form := "qualcuno",
        ontology := .person,
        basis := .genericNoun,
        functions := {.specificKnown, .specificUnknown, .irrealis} }
    , { form := "nessuno",
        ontology := .person,
        basis := .genericNoun,
        functions := {.question, .conditional, .indirectNeg, .directNeg} }
    , { form := "qualunque/qualsiasi",
        ontology := .person,
        basis := .genericNoun,
        functions := {.comparative, .freeChoice} } ] }

/-- Finnish: 4 series on the special *joku*/*kukaan* morphemes. -/
def finnish : IndefiniteParadigm :=
  { language := "Finnish"
  , isoCode := "fin"
  , forms :=
    [ { form := "joku",
        ontology := .person,
        basis := .special,
        functions := {.specificKnown, .specificUnknown} }
    , { form := "joku (irrealis)",
        ontology := .person,
        basis := .special,
        functions := {.irrealis} }
    , { form := "kukaan",
        ontology := .person,
        basis := .special,
        functions := {.question, .conditional, .indirectNeg, .directNeg} }
    , { form := "kuka tahansa",
        ontology := .person,
        basis := .special,
        functions := {.comparative, .freeChoice} } ] }

/-- Korean: wh + particle (A.39): bare wh and *-nka* non-negative (split
    into a specific and a non-specific row); *-to* the negations plus
    comparative (A294); *-na* free choice (A291). -/
def korean : IndefiniteParadigm :=
  { language := "Korean"
  , isoCode := "kor"
  , forms :=
    [ { form := "nwukwu-nka (누군가)",
        ontology := .person,
        basis := .interrogative,
        functions := {.specificKnown, .specificUnknown} }
    , { form := "nwukwu (누구)",
        ontology := .person,
        basis := .interrogative,
        functions := {.irrealis, .question, .conditional} }
    , { form := "nwukwu-to (누구도, neg)",
        ontology := .person,
        basis := .interrogative,
        functions := {.indirectNeg, .directNeg, .comparative} }
    , { form := "nwukwu-na (누구나)",
        ontology := .person,
        basis := .interrogative,
        functions := {.freeChoice} } ] }

/-- Hungarian: 3 interrogative-based series (A.26; Table 4.1: *akár*
    4589): *vala-* from specific through indirect negation, *sem* direct
    negation, *akár-*~*bár-* question/conditional/comparative/free choice
    — contiguous precisely via the map's question–conditional edge. -/
def hungarian : IndefiniteParadigm :=
  { language := "Hungarian"
  , isoCode := "hun"
  , forms :=
    [ { form := "valaki",
        ontology := .person,
        basis := .interrogative,
        functions := {.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional, .indirectNeg} }
    , { form := "senki",
        ontology := .person,
        basis := .interrogative,
        functions := {.directNeg} }
    , { form := "akárki / bárki",
        ontology := .person,
        basis := .interrogative,
        functions := {.question, .conditional, .comparative, .freeChoice} } ] }

/-- Georgian: 4 interrogative-based series. -/
def georgian : IndefiniteParadigm :=
  { language := "Georgian"
  , isoCode := "kat"
  , forms :=
    [ { form := "vinme (ვინმე)",
        ontology := .person,
        basis := .interrogative,
        functions := {.specificKnown, .specificUnknown, .irrealis} }
    , { form := "vinme (question context)",
        ontology := .person,
        basis := .interrogative,
        functions := {.question, .conditional} }
    , { form := "aravin (არავინ)",
        ontology := .person,
        basis := .interrogative,
        functions := {.indirectNeg, .directNeg} }
    , { form := "nebismieri (ნებისმიერი)",
        ontology := .person,
        basis := .interrogative,
        functions := {.comparative, .freeChoice} } ] }

/-- Quechua (Ancash): 2 series (A.37): bare interrogatives for the merged
    specific node, *-pis* ('also, even') for all non-specific functions
    (direct negation with *mana … -tsu*, A279). Absent from WALS F46A,
    whose Quechua datapoint is Imbabura. -/
def quechua : IndefiniteParadigm :=
  { language := "Quechua (Ancash)"
  , isoCode := "qwh"
  , forms :=
    [ { form := "pi (bare interrogative)",
        ontology := .person,
        basis := .interrogative,
        functions := {.specificKnown, .specificUnknown} }
    , { form := "pi-pis",
        ontology := .person,
        basis := .interrogative,
        functions := {.irrealis, .question, .conditional, .indirectNeg,
                      .directNeg, .comparative, .freeChoice} } ] }

/-- Yoruba: 2 generic-noun-based series (*ẹnìkan* 'person'). -/
def yoruba : IndefiniteParadigm :=
  { language := "Yoruba"
  , isoCode := "yor"
  , forms :=
    [ { form := "ẹnìkan",
        ontology := .person,
        basis := .genericNoun,
        functions := {.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional} }
    , { form := "ẹ̀nìkẹ́ni",
        ontology := .person,
        basis := .genericNoun,
        functions := {.indirectNeg, .directNeg, .comparative, .freeChoice} } ] }

/-- Thai: 3 interrogative-based series. -/
def thai : IndefiniteParadigm :=
  { language := "Thai"
  , isoCode := "tha"
  , forms :=
    [ { form := "khraj (ใคร)",
        ontology := .person,
        basis := .interrogative,
        functions := {.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional} }
    , { form := "mâj mii khraj (ไม่มีใคร)",
        ontology := .person,
        basis := .interrogative,
        functions := {.indirectNeg, .directNeg} }
    , { form := "khraj kɔ̂ (ใครก็)",
        ontology := .person,
        basis := .interrogative,
        functions := {.comparative, .freeChoice} } ] }

/-- Tagalog: 4 series built on the existential construction. -/
def tagalog : IndefiniteParadigm :=
  { language := "Tagalog"
  , isoCode := "tgl"
  , forms :=
    [ { form := "may isa",
        ontology := .person,
        basis := .existentialConstruction,
        functions := {.specificKnown, .specificUnknown, .irrealis} }
    , { form := "sinuman",
        ontology := .person,
        basis := .existentialConstruction,
        functions := {.question, .conditional, .indirectNeg} }
    , { form := "walang (tao)",
        ontology := .person,
        basis := .existentialConstruction,
        functions := {.directNeg} }
    , { form := "kahit sino",
        ontology := .person,
        basis := .existentialConstruction,
        functions := {.comparative, .freeChoice} } ] }

/-- Swahili: 3 generic-noun-based series (*mtu* 'person'). -/
def swahili : IndefiniteParadigm :=
  { language := "Swahili"
  , isoCode := "swh"
  , forms :=
    [ { form := "mtu (fulani)",
        ontology := .person,
        basis := .genericNoun,
        functions := {.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional} }
    , { form := "hakuna mtu / mtu … -si-",
        ontology := .person,
        basis := .genericNoun,
        functions := {.indirectNeg, .directNeg} }
    , { form := "mtu ye yote",
        ontology := .person,
        basis := .genericNoun,
        functions := {.comparative, .freeChoice} } ] }

/-- The polarity-typology sample. -/
def allLanguages : List IndefiniteParadigm :=
  [ english, russian, german, japanese, mandarin, turkish, hindi
  , italian, finnish, korean, hungarian, georgian, quechua, yoruba
  , thai, tagalog, swahili ]

/-! ### Contiguity and coverage -/

/-- The map hypothesis (Fig. 4.4): every form covers a contiguous region. -/
theorem all_languages_contiguous :
    ∀ p ∈ allLanguages, p.AllContiguous := by decide

/-- Every language in the sample covers all nine functions. -/
theorem all_languages_cover_all_functions :
    ∀ p ∈ allLanguages, p.CoversAllFunctions := by decide

/-- Russian fails `FormsDisjoint`: -то and -нибудь overlap on non-specific
    uses ([degano-aloni-2025] Table 2). -/
theorem russian_not_disjoint : ¬ russian.FormsDisjoint := by decide

/-- German fails `FormsDisjoint`: *jemand* and *irgendwer* overlap from SU
    through indirect negation (A.1). -/
theorem german_not_disjoint : ¬ german.FormsDisjoint := by decide

/-- Hungarian fails `FormsDisjoint`: *valaki* and *akárki* overlap on
    question and conditional (A.26). -/
theorem hungarian_not_disjoint : ¬ hungarian.FormsDisjoint := by decide

/-! ### Typological generalizations -/

/-- A form covering free choice plus anything else covers the comparative —
    free choice's only neighbour on the map. -/
theorem freeChoice_multifunction_implies_comparative :
    ∀ p ∈ allLanguages, ∀ e ∈ p.forms,
      e.covers .freeChoice → e.coverage > 1 → e.covers .comparative := by
  decide

/-- The comparative need not pattern with free choice: *-mo* covers it with
    the negations and without free choice (A.38, §4.7.1). -/
theorem japanese_comparative_patterns_with_negation :
    ∃ e ∈ japanese.forms,
      e.covers .comparative ∧ e.covers .directNeg ∧
        ¬ e.covers .freeChoice := by decide

/-! ### Map-geometry facts -/

/-- Regions skipping the map's intermediate functions are non-contiguous. -/
theorem non_contiguous_pairs :
    [[HaspelmathFunction.specificKnown, .directNeg],
     [.specificKnown, .freeChoice],
     [.specificKnown, .comparative],
     [.specificUnknown, .directNeg]].all
      (HaspelmathFunction.isContiguous · = false) := by decide

/-- The map's named regions — specific, NPI, FC, the polarity-sensitive
    span, and the whole map — are contiguous. -/
theorem named_regions_contiguous :
    [[HaspelmathFunction.specificKnown, .specificUnknown],
     [.specificKnown, .specificUnknown, .irrealis],
     [.question, .conditional, .indirectNeg],
     [.question, .conditional, .indirectNeg, .directNeg],
     [.comparative, .freeChoice],
     [.question, .conditional, .indirectNeg, .directNeg,
      .comparative, .freeChoice],
     HaspelmathFunction.all].all
      (HaspelmathFunction.isContiguous ·) := by decide

/-! ### Fragment bridges

Each paradigm's polarity-sensitive forms correspond to
`Fragments/{Lang}/PolarityItems.lean` entries licensed in the matching
contexts. -/

/-- Every direct-negation form's Fragment counterpart is licensed under
    clausal negation. -/
theorem bridges_negation :
    ∀ e ∈ [Italian.PolarityItems.nessuno, Russian.PolarityItems.nikto,
           German.PolarityItems.niemand, Japanese.PolarityItems.dareMo,
           Korean.PolarityItems.nwukwuTo, Hungarian.PolarityItems.senki,
           Georgian.PolarityItems.aravin, Quechua.PolarityItems.manaPiPash,
           Thai.PolarityItems.majMiiKhraj, Swahili.PolarityItems.hakunaMtu],
      .negation ∈ e.licensingContexts := by decide

/-- Every question-span form's Fragment counterpart is licensed in
    questions. -/
theorem bridges_question :
    ∀ e ∈ [English.PolarityItems.any, Turkish.PolarityItems.kimse,
           Finnish.PolarityItems.kukaan, Tagalog.PolarityItems.sinuman],
      .question ∈ e.licensingContexts := by decide

/-- The single-form wide-coverage items are dual NPI/FCIs in their
    Fragments. -/
theorem bridges_npiFci :
    ∀ e ∈ [German.PolarityItems.irgendein, Mandarin.PolarityItems.shei,
           Yoruba.PolarityItems.enikeni],
      e.polarityType = Semantics.Polarity.PolarityType.npiFci := by decide

end Haspelmath1997Polarity
