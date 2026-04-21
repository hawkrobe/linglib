import Linglib.Core.Typology.WordOrder
import Linglib.Core.Typology.Adposition
import Linglib.Core.Morphology.MorphProfile

/-!
# Per-language typological profile

`LanguageProfile` is the single per-language aggregate of WALS-style
typological data. Per-language `Fragments/{Lang}/Typology.lean` files
define one `def typology : LanguageProfile := ...` value bundling each
typological domain (word order, adposition, morphology, ...) into one
record.

## Schema discipline

Fields are **append-only** and (apart from `iso`/`name`/`wordOrder`) all
optional. Adding a domain doesn't break consumers — missing data
defaults to `none`. A new field only lands when the same PR uses it in
at least one stated universal/theorem; no speculative fields.

## Composable builders

Two construction styles:

* `LanguageProfile.ofWALS iso name` — pulls every WALS-derivable field
  in one call. Use when no overrides are needed.
* `LanguageProfile.empty iso name |>.withWordOrderFromWALS |>.withAdpositionFromWALS |>.withMorph m`
  — pipeline composition, override per-domain. Use when a Fragment needs
  to substitute hand-coded values for WALS data.

## Fragment policy

A `Fragments/{Lang}/Typology.lean` file exists iff it carries at least
one of: a field overriding WALS, a hand-coded value WALS lacks, or a
citation backing a hand classification. Pure-WALS languages get inlined
as `LanguageProfile.ofWALS "iso" "Name"` directly in their consuming
`Phenomena/X/Typology.lean` — no stub Fragment file needed.
-/

namespace Core.Typology

/-- A bundle of WALS-style typological profiles for a single language.
    Per-domain fields are populated by per-language Fragments; absent
    domains default to `none` (or the domain's own fallback value).

    `iso` is the ISO 639-3 code keying WALS lookups; `name` is a
    human-readable label. -/
structure LanguageProfile where
  /-- ISO 639-3 code. -/
  iso : String
  /-- Human-readable language name. -/
  name : String
  /-- Word-order profile (WALS Ch 81/82/83). -/
  wordOrder : WordOrder.WordOrderProfile
  /-- Adposition order (WALS Ch 85); `none` if WALS has no entry. -/
  adposition : Option Adposition.AdpositionOrder := none
  /-- Morphological profile (WALS Ch 20--29 etc); `none` until a Fragment
      populates it. -/
  morph : Option Core.Morphology.MorphProfile := none
  /-- Free-text commentary, including `@cite{...}` keys for hand-coded
      values that override or supplement WALS. -/
  notes : String := ""
  deriving Repr, DecidableEq

namespace LanguageProfile

/-- Empty profile with only ISO and name set; all WALS-derivable fields
    default to fallback values. Use as the seed for the composable
    pipeline (`empty iso name |>.withWordOrderFromWALS |>. ...`). -/
def empty (iso name : String) : LanguageProfile :=
  { iso := iso
    name := name
    wordOrder := { basicOrder := .noDominant, svOrder := .noDominant, ovOrder := .noDominant } }

/-- Populate `wordOrder` by ISO lookup against WALS Ch 81/82/83. -/
def withWordOrderFromWALS (p : LanguageProfile) : LanguageProfile :=
  { p with wordOrder := WordOrder.WordOrderProfile.ofWALS p.iso }

/-- Populate `adposition` by ISO lookup against WALS Ch 85. -/
def withAdpositionFromWALS (p : LanguageProfile) : LanguageProfile :=
  { p with adposition := Adposition.adpositionOfWALS p.iso }

/-- Populate `morph` with a hand-supplied `MorphProfile` (typically the
    Fragment's `morphProfile`, which itself does WALS lookup with
    field-by-field overrides). -/
def withMorph (p : LanguageProfile) (m : Core.Morphology.MorphProfile) : LanguageProfile :=
  { p with morph := some m }

/-- Attach free-text notes (including `@cite{...}` keys). -/
def withNotes (p : LanguageProfile) (n : String) : LanguageProfile :=
  { p with notes := n }

/-- Pull every WALS-derivable field in one call. Use for languages with
    no overrides; equivalent to
    `empty iso name |>.withWordOrderFromWALS |>.withAdpositionFromWALS`. -/
def ofWALS (iso name : String) : LanguageProfile :=
  empty iso name |>.withWordOrderFromWALS |>.withAdpositionFromWALS

end LanguageProfile

end Core.Typology
