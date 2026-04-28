import Linglib.Typology.Indefinite

/-!
# Latin Indefinite Pronouns
@cite{haspelmath-1997} @cite{bubnov-2026}

Latin has a two-way split in the SK–SU–NS region of @cite{haspelmath-1997}'s
map: *aliquis* (`ali-` + interrogative `quis`) covers non-specific and
specific-unknown (AAB pattern); *quidam* (interrogative `qui` + `-dam`)
covers specific-known. Both forms are interrogative-based.

Latin is not in @cite{wals-2013} F46A's 326-language sample, so no WALS
bridge theorem is stated for Latin in `Phenomena/Indefinites/Typology.lean`.
The morphological-basis encoding is recorded for cross-linguistic
comparison anyway.
-/

set_option autoImplicit false

namespace Fragments.Latin.Indefinites

open Typology.Indefinite

/-- Latin *aliquis*: non-specific + specific-unknown (AAB pattern).
    Interrogative-based: `ali-` + interrogative `quis`. D&A type iv
    epistemic (`var(∅,x)`); distribution matches profile.
    @cite{haspelmath-1997}, @cite{bubnov-2026} Table 1. -/
def aliEntry : IndefiniteEntry where
  language := "Latin"
  form := "aliquis"
  gloss := "someone (non-specific/unknown)"
  basis := .interrogative
  functions := {.specificUnknown, .irrealis}

/-- Latin *quidam*: specific-known indefinite (interrogative `qui` + `-dam`).
    D&A type v `dep(∅,x)`.
    @cite{haspelmath-1997}, @cite{bubnov-2026} Table 1. -/
def damEntry : IndefiniteEntry where
  language := "Latin"
  form := "quidam"
  gloss := "a certain (one)"
  basis := .interrogative
  functions := {.specificKnown}

/-- The Latin indefinite paradigm: AAB pattern, both forms
    interrogative-based. -/
def paradigm : IndefiniteParadigm where
  language := "Latin"
  isoCode := "lat"
  forms := [aliEntry, damEntry]

/-- Latin paradigm exhibits Haspelmath's AAB syncretism: NS+SU
    coexpressed (`aliquis`), SK distinct (`quidam`). -/
theorem latin_paradigm_is_AAB : paradigm.syncretism = some .AAB := rfl

end Fragments.Latin.Indefinites
