import Linglib.Typology.Indefinite

/-!
# Yakut (Sakha) Indefinite Pronouns
@cite{stachowski-menz-1998} @cite{haspelmath-1997} @cite{wals-2013}

Yakut indefinites are uniformly built from interrogative pronouns + an
enclitic particle. Per @cite{stachowski-menz-1998} p. 423, four series:

| Form         | Gloss                       | Coverage                       |
|--------------|-----------------------------|--------------------------------|
| `kim ere`    | 'somebody (specific)'       | SK + SU                        |
| `kim eme`    | 'somebody, anybody'         | NS                             |
| `kim bayarar`| 'whoever, every'            | FC + conditional               |
| `kim da`     | 'anybody (polarity)'        | Q + Cond + Comp + IndNeg + DirNeg |

`-dayanï` is a phonological variant of `da` (S&M p. 423, "kim da or kim
dayanï 'anybody'"); not formalized as a separate entry.

Since all four series use the interrogative `kim` 'who' as their host, the
paradigm derives to @cite{wals-2013} F46A `.interrogativeBased` —
matching WALS's classification for `iso = "sah"` (verified in
`Phenomena/Indefinites/Typology.lean`).

The Degano & Aloni 7-type classification of `ere` and `eme` (types ii and
iii respectively, after @cite{bubnov-2026} Table 1) is theory-side
projection — see `Theories/Semantics/Quantification/DeganoAloni2025.lean`.
The free-choice and polarity-sensitive series (`bayarar`, `da`) fall
outside D&A's SK/SU/NS subdivision; their D&A surface-classification is
`none` by design.
-/

set_option autoImplicit false

namespace Fragments.Yakut.Indefinites

open Typology.Indefinite

/-- Yakut *kim ere*: enclitic particle for specific indefinites; covers
    both specific-known and specific-unknown functions (ABB syncretism).
    @cite{stachowski-menz-1998} p. 423; @cite{bubnov-2026} Table 1
    (D&A type ii). -/
def ereEntry : IndefiniteEntry where
  language := "Yakut"
  form := "kim ere"
  gloss := "somebody (specific)"
  basis := .interrogative
  functions := {.specificKnown, .specificUnknown}

/-- Yakut *kim eme*: enclitic particle for irrealis non-specific
    indefinites; `kim eme` 'somebody, anybody'.
    @cite{stachowski-menz-1998} p. 423; @cite{bubnov-2026} Table 1
    (D&A type iii). -/
def emeEntry : IndefiniteEntry where
  language := "Yakut"
  form := "kim eme"
  gloss := "somebody, anybody (non-specific)"
  basis := .interrogative
  functions := {.irrealis}

/-- Yakut *kim bayarar*: generalizing/free-choice indefinite,
    `kim bayarar` 'whoever (s)he may be, every'. Outside D&A's SK/SU/NS
    subdivision — its surface D&A classification is `none`.
    @cite{stachowski-menz-1998} p. 423. -/
def bayararEntry : IndefiniteEntry where
  language := "Yakut"
  form := "kim bayarar"
  gloss := "whoever, every (free choice)"
  basis := .interrogative
  functions := {.freeChoice, .conditional}

/-- Yakut *kim da* (~ *kim dayanï*): polarity-sensitive indefinite,
    used in both affirmative and negative environments
    (@cite{stachowski-menz-1998} p. 423: 'anybody'). Covers questions,
    conditionals, comparatives, and both negation regions. Outside D&A's
    SK/SU/NS subdivision. -/
def daEntry : IndefiniteEntry where
  language := "Yakut"
  form := "kim da"
  gloss := "anybody (polarity-sensitive)"
  basis := .interrogative
  functions := {.question, .conditional, .comparative,
                .indirectNeg, .directNeg}

/-- The Yakut indefinite paradigm: four interrogative-based series. -/
def paradigm : IndefiniteParadigm where
  language := "Yakut"
  isoCode := "sah"
  forms := [ereEntry, emeEntry, bayararEntry, daEntry]

/-- The SK/SU/NS portion of the paradigm exhibits Haspelmath's ABB
    syncretism: NS distinct (`kim eme`), SU + SK coexpressed (`kim ere`).
    Derived from the entry forms via `classifyTriple`. -/
theorem yakut_paradigm_is_ABB :
    paradigm.syncretism = some .ABB := rfl

/-- Yakut's paradigm uses a single morphological basis (interrogative
    `kim`) across all four forms, deriving the WALS F46A classification
    `.interrogativeBased`. The cross-check against @cite{wals-2013}
    F46A.allData lives in `Phenomena/Indefinites/Typology.lean`. -/
theorem yakut_paradigm_is_interrogativeBased :
    paradigm.toWALS46A = some .interrogativeBased := rfl

end Fragments.Yakut.Indefinites
