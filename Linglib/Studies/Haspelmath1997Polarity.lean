import Linglib.Semantics.Polarity.Item
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
# Haspelmath (1997): Polarity-Side Indefinite Typology
[haspelmath-1997] [haspelmath-2013] [kadmon-landman-1993]
[ladusaw-1979] [wals-2013]

Haspelmath, Martin (1997). *Indefinite Pronouns*. Oxford Studies in
Typology and Linguistic Theory. Oxford University Press.

Polarity-side projection of [haspelmath-1997]'s 9-function
implicational map for indefinite pronouns. Where the sibling file
`Studies/Haspelmath1997.lean` formalises the
indefinite-typology angle (Fragment-derived `IndefiniteParadigm`s for a
6-language sample, with WALS-bridge theorems checking the F46A
classification), this file owns the polarity-side claims:

- 17-language sample of `IndefiniteParadigm` instances; the German,
  Hungarian, Japanese, Korean, and Quechua paradigms are verified against
  the book's appendix A distributions (A.1, A.26, A.37, A.38, A.39) and
  Table 4.1; the rest remain hand-stipulated pending the same pass
- contiguity + coverage theorems on [haspelmath-1997]'s Fig. 4.4 map
- `FragmentBridges` decide-checks against `Fragments/{Lang}/PolarityItems.lean`
  entries (verifies that NPI items the polarity Fragments declare are
  licensed in the contexts the Haspelmath polarity-sensitive forms cover)

The substrate (`HaspelmathFunction` with the Fig. 4.4 map geometry,
`MorphologicalBasis`) lives in `Features/Indefinite.lean`;
`IndefinitePronoun`, `IndefiniteParadigm`, and the contiguity / coverage /
disjointness predicates live in `Syntax/Pronoun/IndefiniteParadigm.lean`.

## Sample

17 typologically diverse languages:
- Indo-European: English, Russian, German, Italian, Hindi-Urdu
- Uralic: Finnish, Hungarian
- Turkic: Turkish
- Sino-Tibetan: Mandarin
- Japonic / Koreanic: Japanese, Korean
- Kartvelian: Georgian
- Quechuan: Quechua (Ancash)
- Niger-Congo: Yoruba, Swahili
- Kra-Dai: Thai
- Austronesian: Tagalog

The 17 paradigms are hand-stipulated here rather than derived from
`Fragments/{Lang}/Indefinites.lean` because the per-form
`IndefinitePronoun.functions` field commits to a particular analysis of how
forms partition the 9-function map, and the polarity-side analysis
(Haspelmath 1997's contiguity-driven encoding) genuinely differs from the
existing Fragment-side analysis (Degano-Aloni 2025 / Bubnov 2026's
competition-driven encoding) on three of the 17 languages where Fragments
already exist (English, German, Russian).

Concrete disagreement: this file's polarity-view English allocation gives
`some-` `{SK, SU}` only, with `any- (NPI)` owning `{irrealis, question,
conditional, indirectNeg}`; the D&A-shape Fragment's `someEntry` covers
`{SK, SU, irrealis}` with no `any-` form. (The book's own coding is broader
still — Table 4.1: *some-* 12345, *any-* 456789, overlapping on question
and conditional — so the English rows below await the book-faithfulness
pass applied to German, Hungarian, Japanese, Korean, and Quechua.) This is
a real analytical disagreement, not a missing-data gap.

Audit history (see `project_indefinite_substrate_contested.md` memory note):
- A first-pass audit framed this as a 5-framework conflict and recommended
  substrate evolution (split `functions → attestedFunctions`). That framing
  was wrong: re-audit verified actual writers are **2** (Fragments + this
  file); other consumers (D&A, Bubnov, Dekier, Chierchia, Modal Indefinites)
  are READ-only, parallel substrate, or no contact.
- A second-pass check against the most recent canonical paper
  ([degano-aloni-2025], *How to be (non-)specific*, L&P 2025) verified
  that D&A 2025 explicitly works within Haspelmath's 9-function map
  unchanged — they do NOT split irrealis into specific/nonspecific
  sub-functions. So substrate-level function-inventory refinement would
  put linglib ahead of the field.
- D&A 2025 Table 2 also explicitly allows two forms to cover the same
  function (Russian -то and -нибудь both NS). This invalidates universal
  `FormsDisjoint` as a constraint. The Russian paradigm here now follows
  D&A 2025's classification (-то = Epistemic {SU, NS}); see
  `disjoint_languages_count` + `russian_not_disjoint`.
- `Studies/Chierchia2006.lean` already consumes this
  file's `italian`/`english`/`german`/`mandarin` paradigms as substrate.
  Hand-stipulation here is therefore a working pattern with multiple
  consumers, not an isolated stipulation.

The Fragment-vs-Studies disagreement is two published analyses, lifted
to theorem level in `Studies/Bubnov2026.lean` §11:
`fragment_polarity_disagree_on_kto_to` proves the Russian case;
`fragment_polarity_disagree_on_some` proves the English case. Both are
`decide`-checked extensional inequalities on the Haspelmath function
sets. The disagreement source is documented there: D&A read profiles
theoretically (semantic permission); Bubnov reads them distributionally
(actual coverage net of paradigmatic competition with sibling forms).
Promotion of the 14 missing-language paradigms to Fragments is deferred
on the same grounds: each promoted paradigm would have to pick a
classification, replicating the disagreement at more sites.

## Relation to Indefinites/Studies/Haspelmath1997.lean

CLAUDE.md permits placing the same paper's formalisation under multiple
phenomena when the contributions split cleanly. The split here:

- `Indefinites/Studies/Haspelmath1997.lean` — typological coverage of
  indefinites, advancing claims about `IndefiniteParadigm`'s F46A bridge
- `Studies/Haspelmath1997Polarity.lean` (this file) — polarity-
  side projection, advancing claims about NPI/FC clustering, neg-concord,
  and Fragment-PolarityItem consistency

-/

namespace Haspelmath1997Polarity

open _root_.Indefinite

/-! Helpers (`formCount`, `allFunctions`, `AllContiguous`,
    `CoversAllFunctions`, `FormsDisjoint`, `IndefinitePronoun.coverage`)
    are defined on `IndefiniteParadigm` / `IndefinitePronoun` in
    `Syntax/Pronoun/IndefiniteParadigm.lean`. The `Prop`-valued predicates
    have `Decidable` instances; theorems use them directly without
    `= true` tails (mathlib idiom). -/

-- ============================================================================
-- §1. Per-language paradigms — 17-language sample
-- ============================================================================

/-- English (Indo-European): 4 series, generic-noun-based.
    `some-` (SK+SU) / `any-` NPI (irrealis through indirectNeg) / `no-`
    (directNeg) / `any-` FC (comparative+freeChoice). -/
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

/-- Russian (Slavic): 6 series, interrogative-based. Textbook map example.

    Per [degano-aloni-2025] Table 2 (the most recent canonical
    classification): кое- = Specific Known {SK}, -то = Epistemic
    {SU, NS}, -нибудь = Non-specific {NS}. Note that -то AND -нибудь
    BOTH cover NS — D&A 2025 explicitly observe (p. 960) that "Russian
    speakers tend to select -нибудь for NS and -то for SU" but both
    forms admit NS uses. The paradigm therefore violates `FormsDisjoint`
    (which is a Prop predicate on `IndefiniteParadigm`, not a structural
    requirement; D&A's analysis treats overlapping forms as the empirical
    norm to be explained, not a violation).

    `Fragments/Slavic/Russian/Indefinites.lean` encodes -то more narrowly
    as {SU} only, following [bubnov-2026]'s subsequent argument that
    paradigmatic competition with -нибудь narrows -то's actual distribution.
    The Fragment-vs-Studies divergence here is **two published analyses**,
    not a bug: D&A 2025 (this file's encoding) vs Bubnov 2026 (Fragment's
    encoding). Both are referenced from their respective consumer chains.

    The polarity-region forms (-либо for {question, conditional,
    indirectNeg}, никто for directNeg, кто угодно for {comparative,
    freeChoice}) extend the SK/SU/NS triangle with the polarity span
    Haspelmath's map covers beyond it. -/
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

/-- German (Indo-European): 4 series, mixed bases, per [haspelmath-1997]
    appendix A.1 (Fig. A.1) and Table 4.1 (*etwas* 123456, *irgend*
    2345689, *jeder* 689, *n-* 7), using each series' person form. The
    temporal *je*-series (4568) has no person form and is omitted. The
    series overlap heavily — the book's norm (p. 76) — so German fails
    `FormsDisjoint`. -/
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

/-- Japanese (Japonic): 3 series, interrogative-based, per
    [haspelmath-1997] appendix A.38 (Fig. A.38): the *ka*-series covers
    the non-negative functions; the *mo*-series covers the negative
    functions **and the comparative** (*dare-yori-mo* 'than anyone',
    A284), co-occurring with verbal negation in direct negation; the
    *demo*-series covers free choice only (A287). -/
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

/-- Mandarin (Sino-Tibetan): 2 series, mixed (yǒu rén existential, shéi
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

/-- Turkish (Turkic): 5 series, generic-noun-based (`bir-` 'one'). -/
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

/-- Hindi-Urdu (Indo-Aryan): 3 series, special (`koii`). -/
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

/-- Italian (Romance): 3 series, generic-noun-based. -/
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

/-- Finnish (Uralic): 5 series, special (`joku`/`kukaan` morphemes). -/
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

/-- Korean (Koreanic): 4 series, interrogative-based (wh + particle), per
    [haspelmath-1997] appendix A.39 (Fig. A.39): the bare-wh and *-nka*
    series cover the non-negative span (split here into a specific and a
    non-specific row); the *-to*-series covers both negations **and the
    standard of comparison** (A294), co-occurring with verbal negation in
    direct negation; *-na* (with *-tunci*) covers free choice only
    (A291). -/
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

/-- Hungarian (Uralic): 3 series, interrogative-based, per
    [haspelmath-1997] appendix A.26 (Fig. A.26) and Table 4.1 (*akár*
    4589): the *vala*-series "is used in all functions from 'specific' to
    'indirect negation'"; *sem* covers direct negation; the *akár*- and
    *bár*- series cover question, conditional, comparative, and free
    choice — contiguous precisely via the map's question–conditional edge.
    *valaki* and *akárki* overlap on question/conditional, so Hungarian
    fails `FormsDisjoint`. -/
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

/-- Georgian (Kartvelian): 4 series, interrogative-based. -/
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

/-- Quechua (Ancash): 2 series, per [haspelmath-1997] appendix A.37
    (Fig. A.37): bare interrogatives for the specific functions (the
    figure's merged 'specific' node — the SK/SU distinction is not
    documented), and the *-pis* series ('also, even') for all
    non-specific functions, including both negations (direct negation
    with the discontinuous negator *mana … -tsu*, A279), comparative
    (A277), and free choice (A278). Not in WALS F46A (the WALS Quechua
    datapoint is Imbabura, a different variety). -/
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

/-- Yoruba (Niger-Congo): 2 series, generic-noun-based (`ẹnìkan` 'person'). -/
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

/-- Thai (Kra-Dai): 3 series, interrogative-based. -/
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

/-- Tagalog (Austronesian): 4 series, existential construction. -/
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

/-- Swahili (Bantu): 3 series, generic-noun-based (`mtu` 'person'). -/
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

-- ============================================================================
-- §2. Aggregate sample
-- ============================================================================

/-- All language paradigms in the polarity-typology sample (17 languages). -/
def allLanguages : List IndefiniteParadigm :=
  [ english, russian, german, japanese, mandarin, turkish, hindi
  , italian, finnish, korean, hungarian, georgian, quechua, yoruba
  , thai, tagalog, swahili ]

-- ============================================================================
-- §3. Contiguity verification
-- ============================================================================

/-- [haspelmath-1997]'s key constraint: every form covers a contiguous
    region on the implicational map. -/
theorem all_languages_contiguous :
    ∀ p ∈ allLanguages, p.AllContiguous := by decide

-- ============================================================================
-- §4. Coverage + overlap verification
-- ============================================================================

/-- Every language in the sample covers all nine functions on the map. -/
theorem all_languages_cover_all_functions :
    ∀ p ∈ allLanguages, p.CoversAllFunctions := by decide

/-- 14 of 17 languages in the sample have disjoint forms (no function
    appears in two different forms). Russian fails per [degano-aloni-2025]
    Table 2 (-то and -нибудь both cover NS); German and Hungarian fail per
    [haspelmath-1997]'s own distributions (A.1, A.26) — the book treats
    massive series overlap as the cross-linguistic norm (p. 76).
    `FormsDisjoint` is a Prop predicate on `IndefiniteParadigm`, not a
    structural requirement, so paradigms failing it are well-formed; we
    just enumerate the witnesses. -/
theorem disjoint_languages_count :
    (allLanguages.filter (·.FormsDisjoint)).length = 14 := by decide

/-- Russian fails `FormsDisjoint` per D&A 2025: -то ({SU, NS}) and
    -нибудь ({NS}) overlap on NS. -/
theorem russian_not_disjoint : ¬ russian.FormsDisjoint := by decide

/-- German fails `FormsDisjoint`: *jemand* and *irgendwer* overlap from
    SU through indirect negation ([haspelmath-1997] A.1). -/
theorem german_not_disjoint : ¬ german.FormsDisjoint := by decide

/-- Hungarian fails `FormsDisjoint`: *valaki* and *akárki* overlap on
    question and conditional ([haspelmath-1997] A.26). -/
theorem hungarian_not_disjoint : ¬ hungarian.FormsDisjoint := by decide

-- ============================================================================
-- §5. Typological generalizations
-- ============================================================================

/-- A multi-function form covering free choice always covers the
    comparative — free choice's only map neighbour ([haspelmath-1997]
    Fig. 4.4). Single-function FC forms (Japanese *dare-demo*, Korean
    *nwukwu-na*) are the trivial exception. -/
theorem freeChoice_multifunction_implies_comparative :
    ∀ p ∈ allLanguages, ∀ e ∈ p.forms,
      e.covers .freeChoice → e.coverage > 1 → e.covers .comparative := by
  decide

/-- The comparative need not pattern with free choice: Japanese *-mo*
    covers comparative together with the negation functions and without
    free choice ([haspelmath-1997] A.38; the *dare-yori-mo* pattern,
    §4.7.1). -/
theorem japanese_comparative_patterns_with_negation :
    ∃ e ∈ japanese.forms,
      e.covers .comparative ∧ e.covers .directNeg ∧
        ¬ e.covers .freeChoice := by decide

-- ============================================================================
-- §6. Non-contiguous sets are impossible (negative tests)
-- ============================================================================

/-- {specificKnown, directNeg} skipping intermediates is non-contiguous. -/
theorem specKnown_directNeg_not_contiguous :
    HaspelmathFunction.isContiguous [.specificKnown, .directNeg] = false := by decide

/-- {specificKnown, freeChoice} is non-contiguous. -/
theorem specKnown_freeChoice_not_contiguous :
    HaspelmathFunction.isContiguous [.specificKnown, .freeChoice] = false := by decide

/-- {specificKnown, comparative} is non-contiguous. -/
theorem specKnown_comparative_not_contiguous :
    HaspelmathFunction.isContiguous [.specificKnown, .comparative] = false := by decide

/-- {specificUnknown, directNeg} skipping intermediates is non-contiguous. -/
theorem specUnknown_directNeg_not_contiguous :
    HaspelmathFunction.isContiguous [.specificUnknown, .directNeg] = false := by decide

/-- {specificKnown, specificUnknown} IS contiguous (adjacent). -/
theorem specKnown_specUnknown_contiguous :
    HaspelmathFunction.isContiguous [.specificKnown, .specificUnknown] = true := by decide

/-- {question, conditional, indirectNeg} IS contiguous (a path). -/
theorem polarity_triple_contiguous :
    HaspelmathFunction.isContiguous [.question, .conditional, .indirectNeg] = true := by decide

/-- The full set of all nine functions is contiguous (the map is connected). -/
theorem all_nine_contiguous :
    HaspelmathFunction.isContiguous HaspelmathFunction.all = true := by decide

-- ============================================================================
-- §7. NPI / FC region structure
-- ============================================================================

/-- The NPI region (question through directNeg) is contiguous. -/
theorem npi_region_contiguous :
    HaspelmathFunction.isContiguous
      [.question, .conditional, .indirectNeg, .directNeg] = true := by decide

/-- The FC region (comparative, freeChoice) is contiguous. -/
theorem fc_region_contiguous :
    HaspelmathFunction.isContiguous [.comparative, .freeChoice] = true := by decide

/-- The specific/irrealis region is contiguous. -/
theorem specific_region_contiguous :
    HaspelmathFunction.isContiguous
      [.specificKnown, .specificUnknown, .irrealis] = true := by decide

/-- The full polarity-sensitive span (question through freeChoice) is contiguous. -/
theorem polarity_sensitive_region_contiguous :
    HaspelmathFunction.isContiguous
      [.question, .conditional, .indirectNeg, .directNeg,
       .comparative, .freeChoice] = true := by decide

-- §8. Fragment bridges (PolarityItems consistency)
-- ============================================================================

/-! Verify that each language's `Fragments/{Lang}/PolarityItems.lean` NPI
    entries are licensed in contexts corresponding to the polarity-typology
    profile's polarity-sensitive forms. -/

section FragmentBridges

theorem english_any_covers_question :
    English.PolarityItems.any.licensingContexts.contains .question = true := by
  decide

theorem italian_nessuno_covers_negation :
    Italian.PolarityItems.nessuno.licensingContexts.contains .negation = true := by
  decide

theorem russian_nikto_covers_negation :
    Russian.PolarityItems.nikto.licensingContexts.contains .negation = true := by
  decide

theorem german_irgendein_is_npi_fci :
    German.PolarityItems.irgendein.polarityType = .npiFci := rfl

theorem german_niemand_covers_negation :
    German.PolarityItems.niemand.licensingContexts.contains .negation = true := by
  decide

theorem japanese_dareMo_covers_negation :
    Japanese.PolarityItems.dareMo.licensingContexts.contains .negation = true := by
  decide

theorem korean_nwukwuTo_covers_negation :
    Korean.PolarityItems.nwukwuTo.licensingContexts.contains .negation = true := by
  decide

theorem mandarin_shei_is_npi_fci :
    Mandarin.PolarityItems.shei.polarityType = .npiFci := rfl

theorem turkish_kimse_covers_question :
    Turkish.PolarityItems.kimse.licensingContexts.contains .question = true := by
  decide

theorem finnish_kukaan_covers_question :
    Finnish.PolarityItems.kukaan.licensingContexts.contains .question = true := by
  decide

theorem hungarian_senki_covers_negation :
    Hungarian.PolarityItems.senki.licensingContexts.contains .negation = true := by
  decide

theorem georgian_aravin_covers_negation :
    Georgian.PolarityItems.aravin.licensingContexts.contains .negation = true := by
  decide

theorem quechua_manaPiPash_covers_negation :
    Quechua.PolarityItems.manaPiPash.licensingContexts.contains .negation = true := by
  decide

theorem yoruba_enikeni_is_npi_fci :
    Yoruba.PolarityItems.enikeni.polarityType = .npiFci := rfl

theorem thai_majMiiKhraj_covers_negation :
    Thai.PolarityItems.majMiiKhraj.licensingContexts.contains .negation = true := by
  decide

theorem tagalog_sinuman_covers_question :
    Tagalog.PolarityItems.sinuman.licensingContexts.contains .question = true := by
  decide

theorem swahili_hakunaMtu_covers_negation :
    Swahili.PolarityItems.hakunaMtu.licensingContexts.contains .negation = true := by
  decide

end FragmentBridges

end Haspelmath1997Polarity
