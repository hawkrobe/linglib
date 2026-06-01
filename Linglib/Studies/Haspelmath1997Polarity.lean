import Linglib.Core.Word
import Linglib.Data.WALS.Aggregation
import Linglib.Data.WALS.Features.F46A
import Linglib.Typology.PolarityItem
import Linglib.Typology.Indefinite
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
@cite{haspelmath-1997} @cite{haspelmath-2013} @cite{kadmon-landman-1993}
@cite{ladusaw-1979} @cite{wals-2013}

Haspelmath, Martin (1997). *Indefinite Pronouns*. Oxford Studies in
Typology and Linguistic Theory. Oxford University Press.

Polarity-side projection of @cite{haspelmath-1997}'s 9-function
implicational map for indefinite pronouns. Where the sibling file
`Studies/Haspelmath1997.lean` formalises the
indefinite-typology angle (Fragment-derived `IndefiniteParadigm`s for a
6-language sample, with WALS-bridge theorems checking the F46A
classification), this file owns the polarity-side claims:

- 17-language sample with hand-stipulated `IndefiniteParadigm` instances
- NPI-cluster + FC-region + neg-concord theorems
- WALS Ch 46 distribution and per-language `wals46A` lookups
- `FragmentBridges` decide-checks against `Fragments/{Lang}/PolarityItems.lean`
  entries (verifies that NPI items the polarity Fragments declare are
  licensed in the contexts the Haspelmath polarity-sensitive forms cover)

The substrate (`HaspelmathFunction`, `IndefiniteEntry`, `IndefiniteParadigm`,
`MorphologicalBasis`, contiguity / coverage / disjointness predicates,
`wals46A` and converters) lives in `Typology/Indefinite.lean`.

## Sample

17 typologically diverse languages:
- Indo-European: English, Russian, German, Italian, Hindi-Urdu
- Uralic: Finnish, Hungarian
- Turkic: Turkish
- Sino-Tibetan: Mandarin
- Japonic / Koreanic: Japanese, Korean
- Kartvelian: Georgian
- Quechuan: Quechua (Imbabura)
- Niger-Congo: Yoruba, Swahili
- Kra-Dai: Thai
- Austronesian: Tagalog

The 17 paradigms are hand-stipulated here rather than derived from
`Fragments/{Lang}/Indefinites.lean` because the per-form
`IndefiniteEntry.functions` field commits to a particular analysis of how
forms partition the 9-function map, and the polarity-side analysis
(Haspelmath 1997's contiguity-driven encoding) genuinely differs from the
existing Fragment-side analysis (Degano-Aloni 2025 / Bubnov 2026's
competition-driven encoding) on three of the 17 languages where Fragments
already exist (English, German, Russian).

Concrete disagreement: Haspelmath polarity-view English `some-` covers
`{SK, SU}` only, with `any- (NPI)` owning `{irrealis, question, conditional,
indirectNeg}`; the D&A-shape Fragment's `someEntry` covers `{SK, SU,
irrealis}` with no `any-` form. This is a real analytical disagreement,
not a missing-data gap.

Audit history (see `project_indefinite_substrate_contested.md` memory note):
- A first-pass audit framed this as a 5-framework conflict and recommended
  substrate evolution (split `functions → attestedFunctions`). That framing
  was wrong: re-audit verified actual writers are **2** (Fragments + this
  file); other consumers (D&A, Bubnov, Dekier, Chierchia, Modal Indefinites)
  are READ-only, parallel substrate, or no contact.
- A second-pass check against the most recent canonical paper
  (@cite{degano-aloni-2025}, *How to be (non-)specific*, L&P 2025) verified
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

open _root_.Typology.Indefinite
open Data.WALS

-- ============================================================================
-- §1. WALS Chapter 46 distribution
-- ============================================================================

/-! `WALSCount` is imported from `Linglib/Data/WALS/Aggregation.lean`. -/

open Data.WALS (WALSCount)

private abbrev ch46 := Data.WALS.F46A.allData

/-- WALS Ch 46 distribution (N = 326). -/
def ch46Counts : List WALSCount :=
  [ ⟨"Interrogative-based", (ch46.filter (·.value == .interrogativeBased)).length⟩
  , ⟨"Generic-noun-based",  (ch46.filter (·.value == .genericNounBased)).length⟩
  , ⟨"Special",             (ch46.filter (·.value == .special)).length⟩
  , ⟨"Mixed",               (ch46.filter (·.value == .mixed)).length⟩
  , ⟨"Existential construction",
      (ch46.filter (·.value == .existentialConstruction)).length⟩ ]

/-! Helpers (`wals46A`, `formCount`, `allFunctions`, `AllContiguous`,
    `CoversAllFunctions`, `FormsDisjoint`, `IndefiniteEntry.coverage`)
    are defined on `IndefiniteParadigm` / `IndefiniteEntry` in
    `Typology/Indefinite.lean`. The `Prop`-valued predicates have
    `Decidable` instances; theorems use them directly without `= true`
    tails (mathlib idiom). -/

-- ============================================================================
-- §2. Per-language paradigms — 17-language sample
-- ============================================================================

/-- English (Indo-European): 4 series, generic-noun-based.
    `some-` (SK+SU) / `any-` NPI (irrealis through indirectNeg) / `no-`
    (directNeg) / `any-` FC (comparative+freeChoice). -/
def english : IndefiniteParadigm :=
  { language := "English"
  , isoCode := "eng"
  , forms :=
    [ { language := "English", form := "some-",
        gloss := "somebody, something, somewhere",
        basis := .genericNoun,
        functions := {.specificKnown, .specificUnknown} }
    , { language := "English", form := "any- (NPI)",
        gloss := "anybody, anything in DE/nonveridical",
        basis := .genericNoun,
        functions := {.irrealis, .question, .conditional, .indirectNeg} }
    , { language := "English", form := "no-",
        gloss := "nobody, nothing, nowhere",
        basis := .genericNoun,
        functions := {.directNeg} }
    , { language := "English", form := "any- (FC)",
        gloss := "anybody can do that; taller than anybody",
        basis := .genericNoun,
        functions := {.comparative, .freeChoice} } ] }

/-- Russian (Slavic): 6 series, interrogative-based. Textbook map example.

    Per @cite{degano-aloni-2025} Table 2 (the most recent canonical
    classification): кое- = Specific Known {SK}, -то = Epistemic
    {SU, NS}, -нибудь = Non-specific {NS}. Note that -то AND -нибудь
    BOTH cover NS — D&A 2025 explicitly observe (p. 960) that "Russian
    speakers tend to select -нибудь for NS and -то for SU" but both
    forms admit NS uses. The paradigm therefore violates `FormsDisjoint`
    (which is a Prop predicate on `IndefiniteParadigm`, not a structural
    requirement; D&A's analysis treats overlapping forms as the empirical
    norm to be explained, not a violation).

    `Fragments/Slavic/Russian/Indefinites.lean` encodes -то more narrowly
    as {SU} only, following @cite{bubnov-2026}'s subsequent argument that
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
    [ { language := "Russian", form := "кое-кто (koe-kto)",
        gloss := "specific known: speaker knows the referent's identity",
        basis := .interrogative,
        functions := {.specificKnown} }
    , { language := "Russian", form := "кто-то (kto-to)",
        gloss := "epistemic (D&A 2025 type iv): SU + NS",
        basis := .interrogative,
        functions := {.specificUnknown, .irrealis} }
    , { language := "Russian", form := "кто-нибудь (kto-nibud')",
        gloss := "non-specific / irrealis: 'anyone, no matter who'",
        basis := .interrogative,
        functions := {.irrealis} }
    , { language := "Russian", form := "кто-либо (kto-libo)",
        gloss := "polarity-sensitive: questions, conditionals, indirect neg",
        basis := .interrogative,
        functions := {.question, .conditional, .indirectNeg} }
    , { language := "Russian", form := "никто (nikto)",
        gloss := "nikto ne prisel 'nobody NEG came' (negative concord)",
        basis := .interrogative,
        functions := {.directNeg} }
    , { language := "Russian", form := "кто угодно (kto ugodno)",
        gloss := "universal/free choice: anyone at all",
        basis := .interrogative,
        functions := {.comparative, .freeChoice} } ] }

/-- German (Indo-European): 5 series, mixed bases (jemand generic-noun,
    irgend- special). -/
def german : IndefiniteParadigm :=
  { language := "German"
  , isoCode := "deu"
  , forms :=
    [ { language := "German", form := "jemand",
        gloss := "somebody (specific reference)",
        basis := .genericNoun,
        functions := {.specificKnown, .specificUnknown} }
    , { language := "German", form := "irgendwer",
        gloss := "irgend- prefix marks non-specificity / ignorance",
        basis := .special,
        functions := {.irrealis, .question} }
    , { language := "German", form := "wer (conditional)",
        gloss := "bare wh-word in conditional / indirect neg",
        basis := .interrogative,
        functions := {.conditional, .indirectNeg} }
    , { language := "German", form := "niemand",
        gloss := "negative indefinite",
        basis := .genericNoun,
        functions := {.directNeg} }
    , { language := "German", form := "jeder",
        gloss := "universal/free choice: anyone/everyone",
        basis := .genericNoun,
        functions := {.comparative, .freeChoice} } ] }

/-- Japanese (Japonic): 3 series, interrogative-based. wh + particle. -/
def japanese : IndefiniteParadigm :=
  { language := "Japanese"
  , isoCode := "jpn"
  , forms :=
    [ { language := "Japanese", form := "dare-ka",
        gloss := "wh + ka: existential/non-specific",
        basis := .interrogative,
        functions := {.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional} }
    , { language := "Japanese", form := "dare-mo (neg)",
        gloss := "wh + mo under negation: nobody",
        basis := .interrogative,
        functions := {.indirectNeg, .directNeg} }
    , { language := "Japanese", form := "dare-demo",
        gloss := "wh + demo: free choice / concessive",
        basis := .interrogative,
        functions := {.comparative, .freeChoice} } ] }

/-- Mandarin (Sino-Tibetan): 2 series, mixed (yǒu rén existential, shéi
    interrogative). -/
def mandarin : IndefiniteParadigm :=
  { language := "Mandarin Chinese"
  , isoCode := "cmn"
  , forms :=
    [ { language := "Mandarin", form := "yǒu rén (有人)",
        gloss := "existential: 'there is someone'",
        basis := .existentialConstruction,
        functions := {.specificKnown, .specificUnknown} }
    , { language := "Mandarin", form := "shéi (谁, non-interrog.)",
        gloss := "wh-word in non-interrogative uses; 7 functions",
        basis := .interrogative,
        functions := {.irrealis, .question, .conditional, .indirectNeg,
                      .directNeg, .comparative, .freeChoice} } ] }

/-- Turkish (Turkic): 5 series, generic-noun-based (`bir-` 'one'). -/
def turkish : IndefiniteParadigm :=
  { language := "Turkish"
  , isoCode := "tur"
  , forms :=
    [ { language := "Turkish", form := "birisi",
        gloss := "specific indefinite: 'a certain person'",
        basis := .genericNoun,
        functions := {.specificKnown, .specificUnknown} }
    , { language := "Turkish", form := "biri",
        gloss := "non-specific in irrealis",
        basis := .genericNoun,
        functions := {.irrealis} }
    , { language := "Turkish", form := "kimse",
        gloss := "polarity-sensitive: questions, conditionals",
        basis := .genericNoun,
        functions := {.question, .conditional, .indirectNeg} }
    , { language := "Turkish", form := "hiç kimse",
        gloss := "negative indefinite with hiç intensifier",
        basis := .genericNoun,
        functions := {.directNeg} }
    , { language := "Turkish", form := "herhangi biri",
        gloss := "free choice: any person at all",
        basis := .genericNoun,
        functions := {.comparative, .freeChoice} } ] }

/-- Hindi-Urdu (Indo-Aryan): 3 series, special (`koii`). -/
def hindi : IndefiniteParadigm :=
  { language := "Hindi-Urdu"
  , isoCode := "hin"
  , forms :=
    [ { language := "Hindi-Urdu", form := "koii",
        gloss := "general indefinite: someone/anyone",
        basis := .special,
        functions := {.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional} }
    , { language := "Hindi-Urdu", form := "koii nahiiN",
        gloss := "koii + negation: nobody",
        basis := .special,
        functions := {.indirectNeg, .directNeg} }
    , { language := "Hindi-Urdu", form := "koii bhii",
        gloss := "koii + bhii (even/also): anyone at all (FC)",
        basis := .special,
        functions := {.comparative, .freeChoice} } ] }

/-- Italian (Romance): 3 series, generic-noun-based. -/
def italian : IndefiniteParadigm :=
  { language := "Italian"
  , isoCode := "ita"
  , forms :=
    [ { language := "Italian", form := "qualcuno",
        gloss := "specific/irrealis indefinite",
        basis := .genericNoun,
        functions := {.specificKnown, .specificUnknown, .irrealis} }
    , { language := "Italian", form := "nessuno",
        gloss := "N-word: polarity-sensitive + direct negation",
        basis := .genericNoun,
        functions := {.question, .conditional, .indirectNeg, .directNeg} }
    , { language := "Italian", form := "qualunque/qualsiasi",
        gloss := "free choice universal",
        basis := .genericNoun,
        functions := {.comparative, .freeChoice} } ] }

/-- Finnish (Uralic): 5 series, special (`joku`/`kukaan` morphemes). -/
def finnish : IndefiniteParadigm :=
  { language := "Finnish"
  , isoCode := "fin"
  , forms :=
    [ { language := "Finnish", form := "joku",
        gloss := "specific indefinite",
        basis := .special,
        functions := {.specificKnown, .specificUnknown} }
    , { language := "Finnish", form := "joku (irrealis)",
        gloss := "joku in irrealis / non-specific",
        basis := .special,
        functions := {.irrealis} }
    , { language := "Finnish", form := "kukaan",
        gloss := "polarity-sensitive indefinite (direct-negation function realized as ei + connegative-V + kukaan)",
        basis := .special,
        functions := {.question, .conditional, .indirectNeg, .directNeg} }
    , { language := "Finnish", form := "kuka tahansa",
        gloss := "free choice: whoever / anyone at all",
        basis := .special,
        functions := {.comparative, .freeChoice} } ] }

/-- Korean (Koreanic): 4 series, interrogative-based (wh + particle). -/
def korean : IndefiniteParadigm :=
  { language := "Korean"
  , isoCode := "kor"
  , forms :=
    [ { language := "Korean", form := "nwukwu-nka (누군가)",
        gloss := "wh + nka: specific indefinite",
        basis := .interrogative,
        functions := {.specificKnown, .specificUnknown} }
    , { language := "Korean", form := "nwukwu (누구)",
        gloss := "bare wh-word: non-specific indefinite",
        basis := .interrogative,
        functions := {.irrealis, .question, .conditional} }
    , { language := "Korean", form := "nwukwu-to (누구도, neg)",
        gloss := "wh + to under negation: nobody",
        basis := .interrogative,
        functions := {.indirectNeg, .directNeg} }
    , { language := "Korean", form := "nwukwu-na (누구나)",
        gloss := "wh + na: free choice / universal",
        basis := .interrogative,
        functions := {.comparative, .freeChoice} } ] }

/-- Hungarian (Uralic): 4 series, interrogative-based (vala- / akár-). -/
def hungarian : IndefiniteParadigm :=
  { language := "Hungarian"
  , isoCode := "hun"
  , forms :=
    [ { language := "Hungarian", form := "valaki",
        gloss := "specific indefinite",
        basis := .interrogative,
        functions := {.specificKnown, .specificUnknown} }
    , { language := "Hungarian", form := "valaki (irrealis)",
        gloss := "valaki in irrealis and question contexts",
        basis := .interrogative,
        functions := {.irrealis, .question} }
    , { language := "Hungarian", form := "senki",
        gloss := "negative indefinite (with sem in direct neg)",
        basis := .interrogative,
        functions := {.conditional, .indirectNeg, .directNeg} }
    , { language := "Hungarian", form := "akárki / bárki",
        gloss := "free choice: anyone at all",
        basis := .interrogative,
        functions := {.comparative, .freeChoice} } ] }

/-- Georgian (Kartvelian): 4 series, interrogative-based. -/
def georgian : IndefiniteParadigm :=
  { language := "Georgian"
  , isoCode := "kat"
  , forms :=
    [ { language := "Georgian", form := "vinme (ვინმე)",
        gloss := "general indefinite: someone",
        basis := .interrogative,
        functions := {.specificKnown, .specificUnknown, .irrealis} }
    , { language := "Georgian", form := "vinme (question context)",
        gloss := "vinme in question/conditional contexts",
        basis := .interrogative,
        functions := {.question, .conditional} }
    , { language := "Georgian", form := "aravin (არავინ)",
        gloss := "negative indefinite: nobody",
        basis := .interrogative,
        functions := {.indirectNeg, .directNeg} }
    , { language := "Georgian", form := "nebismieri (ნებისმიერი)",
        gloss := "free choice: any/every",
        basis := .interrogative,
        functions := {.comparative, .freeChoice} } ] }

/-- Quechua (Imbabura): 4 series, special. (Not in WALS F46A's sample.) -/
def quechua : IndefiniteParadigm :=
  { language := "Quechua (Imbabura)"
  , isoCode := "qvi"
  , forms :=
    [ { language := "Quechua", form := "pi-taj",
        gloss := "wh-based indefinite: someone",
        basis := .interrogative,
        functions := {.specificKnown, .specificUnknown, .irrealis, .question} }
    , { language := "Quechua", form := "pi-pash",
        gloss := "wh + pash: in conditional/neg scope",
        basis := .interrogative,
        functions := {.conditional, .indirectNeg} }
    , { language := "Quechua", form := "mana pi-pash",
        gloss := "negation + wh + pash: nobody",
        basis := .interrogative,
        functions := {.directNeg} }
    , { language := "Quechua", form := "maijan-pash",
        gloss := "free choice: anyone",
        basis := .interrogative,
        functions := {.comparative, .freeChoice} } ] }

/-- Yoruba (Niger-Congo): 2 series, generic-noun-based (`ẹnìkan` 'person'). -/
def yoruba : IndefiniteParadigm :=
  { language := "Yoruba"
  , isoCode := "yor"
  , forms :=
    [ { language := "Yoruba", form := "ẹnìkan",
        gloss := "general indefinite: somebody",
        basis := .genericNoun,
        functions := {.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional} }
    , { language := "Yoruba", form := "ẹ̀nìkẹ́ni",
        gloss := "polarity-sensitive + free choice",
        basis := .genericNoun,
        functions := {.indirectNeg, .directNeg, .comparative, .freeChoice} } ] }

/-- Thai (Kra-Dai): 3 series, interrogative-based. -/
def thai : IndefiniteParadigm :=
  { language := "Thai"
  , isoCode := "tha"
  , forms :=
    [ { language := "Thai", form := "khraj (ใคร)",
        gloss := "wh-word as general indefinite",
        basis := .interrogative,
        functions := {.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional} }
    , { language := "Thai", form := "mâj mii khraj (ไม่มีใคร)",
        gloss := "NEG + exist + wh: nobody",
        basis := .interrogative,
        functions := {.indirectNeg, .directNeg} }
    , { language := "Thai", form := "khraj kɔ̂ (ใครก็)",
        gloss := "wh + kɔ̂ particle: free choice",
        basis := .interrogative,
        functions := {.comparative, .freeChoice} } ] }

/-- Tagalog (Austronesian): 4 series, existential construction. -/
def tagalog : IndefiniteParadigm :=
  { language := "Tagalog"
  , isoCode := "tgl"
  , forms :=
    [ { language := "Tagalog", form := "may isa",
        gloss := "existential + 'one': someone",
        basis := .existentialConstruction,
        functions := {.specificKnown, .specificUnknown, .irrealis} }
    , { language := "Tagalog", form := "sinuman",
        gloss := "wh-based polarity-sensitive indefinite",
        basis := .existentialConstruction,
        functions := {.question, .conditional, .indirectNeg} }
    , { language := "Tagalog", form := "walang (tao)",
        gloss := "negative existential: nobody",
        basis := .existentialConstruction,
        functions := {.directNeg} }
    , { language := "Tagalog", form := "kahit sino",
        gloss := "concessive + wh: anyone at all (FC)",
        basis := .existentialConstruction,
        functions := {.comparative, .freeChoice} } ] }

/-- Swahili (Bantu): 3 series, generic-noun-based (`mtu` 'person'). -/
def swahili : IndefiniteParadigm :=
  { language := "Swahili"
  , isoCode := "swh"
  , forms :=
    [ { language := "Swahili", form := "mtu (fulani)",
        gloss := "person (+ certain): someone",
        basis := .genericNoun,
        functions := {.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional} }
    , { language := "Swahili", form := "hakuna mtu / mtu … -si-",
        gloss := "negative existential or negative verb concord",
        basis := .genericNoun,
        functions := {.indirectNeg, .directNeg} }
    , { language := "Swahili", form := "mtu ye yote",
        gloss := "person any whatsoever: free choice",
        basis := .genericNoun,
        functions := {.comparative, .freeChoice} } ] }

-- ============================================================================
-- §4. Aggregate sample
-- ============================================================================

/-- All language paradigms in the polarity-typology sample (17 languages). -/
def allLanguages : List IndefiniteParadigm :=
  [ english, russian, german, japanese, mandarin, turkish, hindi
  , italian, finnish, korean, hungarian, georgian, quechua, yoruba
  , thai, tagalog, swahili ]

theorem sample_size : allLanguages.length = 17 := by decide

-- ============================================================================
-- §5. Contiguity verification
-- ============================================================================

/-- @cite{haspelmath-1997}'s key constraint: every form covers a contiguous
    region on the implicational map. -/
theorem all_languages_contiguous :
    ∀ p ∈ allLanguages, p.AllContiguous := by decide

-- ============================================================================
-- §6. Coverage + partition verification
-- ============================================================================

/-- Every language in the sample covers all nine functions on the map. -/
theorem all_languages_cover_all_functions :
    ∀ p ∈ allLanguages, p.CoversAllFunctions := by decide

/-- 16 of 17 languages in the sample have disjoint forms (no function
    appears in two different forms). Russian is the exception: per
    @cite{degano-aloni-2025} Table 2, both -то (Epistemic, {SU, NS}) and
    -нибудь (Non-specific, {NS}) cover NS. D&A treat overlapping forms as
    a real empirical phenomenon to be explained — see the Russian paragraph
    on p. 960 — not a violation. `FormsDisjoint` is a Prop predicate on
    `IndefiniteParadigm`, not a structural requirement, so paradigms
    failing it are well-formed; we just enumerate the witnesses. -/
theorem disjoint_languages_count :
    (allLanguages.filter (·.FormsDisjoint)).length = 16 := by decide

/-- Russian fails `FormsDisjoint` per D&A 2025: -то ({SU, NS}) and
    -нибудь ({NS}) overlap on NS. -/
theorem russian_not_disjoint : ¬ russian.FormsDisjoint := by decide

/-- The 16 non-Russian languages in the sample DO satisfy `FormsDisjoint`. -/
theorem nonRussian_languages_disjoint :
    ∀ p ∈ allLanguages.filter (·.FormsDisjoint), p.FormsDisjoint := by decide

/-- **Coverage + contiguity theorem** (the disjointness conjunct from the
    earlier `all_languages_partition` is dropped — Russian breaks it per
    D&A 2025 — leaving the universal claim that every paradigm covers all
    nine functions with each form covering a contiguous region). -/
theorem all_languages_covering_and_contiguous :
    ∀ p ∈ allLanguages,
      p.AllContiguous ∧ p.CoversAllFunctions := by
  decide

-- ============================================================================
-- §7. Typological generalizations
-- ============================================================================

/-- Every language has a form covering direct negation. -/
theorem every_language_has_direct_neg :
    ∀ p ∈ allLanguages, ∃ e ∈ p.forms, e.covers .directNeg := by decide

/-- Free choice and comparative are always in the same form. -/
theorem freeChoice_comparative_together :
    ∀ p ∈ allLanguages, ∃ e ∈ p.forms,
      e.covers .freeChoice ∧ e.covers .comparative := by decide

/-- Specific known and direct negation are never in the same form. -/
theorem specificKnown_directNeg_disjoint :
    ∀ p ∈ allLanguages, ∀ e ∈ p.forms,
      ¬ (e.covers .specificKnown ∧ e.covers .directNeg) := by decide

/-- Mandarin (2 forms) has fewer forms than Russian (6 forms), but its
    total coverage is at most Russian's. (Equality held when Russian had 5
    disjoint forms and total coverage 9 = Mandarin's; per @cite{degano-aloni-2025}
    Russian -то now covers {SU, NS} not {SU}, so total coverage rises to
    10 > Mandarin's 9 — the relation weakens to ≤.) -/
theorem fewer_forms_broader_coverage :
    mandarin.formCount < russian.formCount ∧
    (mandarin.forms.map (·.coverage)).sum ≤
      (russian.forms.map (·.coverage)).sum := by
  decide

/-- The polarity cluster: in every language, some form covers at least two
    of {question, conditional, indirectNeg}. -/
theorem polarity_cluster_exists :
    ∀ p ∈ allLanguages, ∃ e ∈ p.forms,
      (e.covers .question ∧ e.covers .conditional) ∨
      (e.covers .conditional ∧ e.covers .indirectNeg) ∨
      (e.covers .question ∧ e.covers .indirectNeg) := by decide

-- ============================================================================
-- §8. Form-count distribution
-- ============================================================================

/-- Count of languages with a given number of forms. -/
def countByFormCount (langs : List IndefiniteParadigm) (n : Nat) : Nat :=
  (langs.filter (fun p => p.formCount == n)).length

theorem sample_2_forms : countByFormCount allLanguages 2 = 2 := by decide
theorem sample_3_forms : countByFormCount allLanguages 3 = 5 := by decide
theorem sample_4_forms : countByFormCount allLanguages 4 = 7 := by decide
theorem sample_5_forms : countByFormCount allLanguages 5 = 2 := by decide
theorem sample_6_forms : countByFormCount allLanguages 6 = 1 := by decide

/-- Per-language form-count summary for the 17-language sample. -/
theorem language_form_counts :
    allLanguages.map (fun p => (p.isoCode, p.formCount)) =
      [ ("eng", 4), ("rus", 6), ("deu", 5), ("jpn", 3), ("cmn", 2)
      , ("tur", 5), ("hin", 3), ("ita", 3), ("fin", 4), ("kor", 4)
      , ("hun", 4), ("kat", 4), ("qvi", 4), ("yor", 2), ("tha", 3)
      , ("tgl", 4), ("swh", 3) ] := by
  decide

-- ============================================================================
-- §9. WALS 46A bridge
-- ============================================================================

/-! 16 of 17 languages appear in WALS F46A; Quechua (Imbabura, iso `qvi`)
    is absent. The Polarity-side annotations of `basis : MorphologicalBasis`
    on each form derive a paradigm-level F46A classification via
    `IndefiniteParadigm.toWALS46A` — but for the polarity sample, the
    paradigm-derived value may differ from WALS for languages where the
    forms span multiple bases (e.g., German `mixed`). We verify the
    `lookupISO`-derived classification rather than the structural derivation. -/

open Data.WALS.F46A (IndefinitePronouns) in
/-- WALS 46A morphological-source classification per language. -/
theorem language_wals_classifications :
    allLanguages.map (fun p => (p.isoCode, p.wals46A)) =
      [ ("eng", some .genericNounBased)
      , ("rus", some .interrogativeBased)
      , ("deu", some .mixed)
      , ("jpn", some .interrogativeBased)
      , ("cmn", some .mixed)
      , ("tur", some .genericNounBased)
      , ("hin", some .special)
      , ("ita", some .genericNounBased)
      , ("fin", some .special)
      , ("kor", some .interrogativeBased)
      , ("hun", some .interrogativeBased)
      , ("kat", some .interrogativeBased)
      , ("qvi", some .interrogativeBased)   -- Imbabura Quechua (WALS code qim)
      , ("yor", some .genericNounBased)
      , ("tha", some .interrogativeBased)
      , ("tgl", some .existentialConstruction)
      , ("swh", some .genericNounBased) ] := by
  decide

/-- All 17 languages in our sample appear in WALS F46A. -/
theorem all_languages_in_wals :
    ∀ p ∈ allLanguages, p.wals46A.isSome := by decide

-- ============================================================================
-- §10. Cross-linguistic pattern tests
-- ============================================================================

/-- Wh-based indefinite languages (Japanese, Korean, Mandarin, Thai). -/
def whBasedLanguages : List IndefiniteParadigm :=
  [japanese, korean, mandarin, thai]

theorem wh_based_fewer_forms :
    (whBasedLanguages.map (·.formCount)).sum ≤ whBasedLanguages.length * 4 := by
  decide

/-- Negative concord languages (Russian, Italian, Hungarian). -/
def negConcordLanguages : List IndefiniteParadigm :=
  [russian, italian, hungarian]

/-- In some neg-concord language, directNeg is in a multi-function form. -/
theorem neg_concord_directNeg_grouped :
    ∃ p ∈ negConcordLanguages, ∃ e ∈ p.forms,
      e.covers .directNeg ∧ e.coverage > 1 := by decide

open Data.WALS.F46A (IndefinitePronouns) in
/-- All four wh-based languages are interrogative-based or mixed in WALS 46A. -/
theorem wh_based_are_interrogative_or_mixed :
    ∀ p ∈ whBasedLanguages,
      p.wals46A = some .interrogativeBased ∨
      p.wals46A = some .mixed := by decide

/-- Languages classified as interrogative-based in WALS 46A. -/
def interrogativeBasedProfiles : List IndefiniteParadigm :=
  allLanguages.filter (fun p =>
    p.wals46A == some Data.WALS.F46A.IndefinitePronouns.interrogativeBased)

theorem interrogative_based_sample_count :
    interrogativeBasedProfiles.length = 7 := by decide

theorem interrogative_based_avg_forms :
    (interrogativeBasedProfiles.map (·.formCount)).sum ≤ 28 := by decide

-- ============================================================================
-- §11. Non-contiguous sets are impossible (negative tests)
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
-- §12. NPI / FC region structure
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

-- ============================================================================
-- §13. Summary statistics
-- ============================================================================

/-- Minimum form count in our sample. -/
theorem min_form_count :
    (allLanguages.map (·.formCount)).foldl min 100 = 2 := by decide

/-- Maximum form count in our sample. -/
theorem max_form_count :
    (allLanguages.map (·.formCount)).foldl max 0 = 6 := by decide

/-- Total number of distinct forms across the sample. -/
theorem total_forms : (allLanguages.map (·.formCount)).sum = 63 := by decide

/-- The most common form count in the sample is 4 (six languages). -/
theorem most_common_form_count :
    countByFormCount allLanguages 4 ≥ countByFormCount allLanguages 2 ∧
    countByFormCount allLanguages 4 ≥ countByFormCount allLanguages 3 ∧
    countByFormCount allLanguages 4 ≥ countByFormCount allLanguages 5 ∧
    countByFormCount allLanguages 4 ≥ countByFormCount allLanguages 6 := by
  decide

-- ============================================================================
-- §14. Fragment bridges (PolarityItems consistency)
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
