import Linglib.Typology.WordOrder
import Linglib.Typology.Adposition
import Linglib.Typology.ClassifierSystem
import Linglib.Typology.Indefinite
import Linglib.Typology.Plurals
import Linglib.Typology.Possession
import Linglib.Typology.Pronouns
import Linglib.Typology.Question
import Linglib.Core.Morphology.MorphProfile
import Linglib.Core.Relativization.Profile

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

## Theory-ladenness

Per-domain field types use cross-linguistic typological vocabulary
(`SVO`/`SOV` from `WordOrder`, `numeralNP`/`headModifierNP` from
`NounCategorization`, etc.). This vocabulary is broadly framework-neutral
within mainstream syntactic typology, but is not strictly theory-free —
even calling something an "NP" or "subject" picks a side. Per-language
`Fragments/{Lang}/Typology.lean` files therefore inherit a thin
typological commitment by populating these fields.

This is distinct from the lexicon files (`Fragments/{Lang}/Classifier.lean`,
`Nouns.lean`, etc.), which carry typed lexical inventories and are kept
theory-light. The Typology aggregator is explicitly a typological object;
the lexicons are not.

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

namespace Typology

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
  /-- Relativization profile (WALS Chs 122/123 + AH cut-off + areal flag);
      `none` until a Fragment populates it. -/
  relativization : Option Core.Relativization.RelativizationProfile := none
  /-- Noun categorization system (@cite{aikhenvald-2000} 7 properties);
      `none` until a Fragment populates it. Hand-coded; no WALS source
      covers the full schema. -/
  classifierSystem : Option NounCategorizationSystem := none
  /-- Indefinite-pronoun paradigm (@cite{haspelmath-1997}, WALS Ch 46);
      `none` until a Fragment populates it. WALS gives only the F46A
      morphological-basis category, not the full paradigm — so there is
      no `withIndefinitesFromWALS`. The Fragment's paradigm derives F46A
      via `IndefiniteParadigm.toWALS46A`; consistency with WALS is then
      a theorem in `Phenomena/Indefinites/Typology.lean`. -/
  indefinites : Option Typology.Indefinite.IndefiniteParadigm := none
  /-- Possession profile (@cite{wals-2013} Chs 57–59 + @cite{stassen-2009}
      predicative + @cite{nichols-1986} adnominal); `none` until a Fragment
      populates it. -/
  possession : Option Typology.Possession.PossessionProfile := none
  /-- Plurality profile (@cite{wals-2013} Chs 33-36); `none` until a
      Fragment populates it. -/
  plurality : Option Typology.PluralityProfile := none
  /-- Pronoun-system profile (@cite{wals-2013} Chs 39-40, 44-48);
      `none` until a Fragment populates it. -/
  pronouns : Option Typology.PronounProfile := none
  /-- Question-formation profile (@cite{wals-2013} Chs 92A, 93A, 116A);
      `none` until a Fragment populates it. -/
  questions : Option Typology.Question.QuestionProfile := none
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

/-- Populate `relativization` with a hand-supplied
    `RelativizationProfile`. WALS Chs 122/123 do not cover the full
    profile (`.mixed`, `lowestRelativizable`, `isEuropean` need
    hand-coding), so there is no `withRelativizationFromWALS`. -/
def withRelativization
    (p : LanguageProfile) (r : Core.Relativization.RelativizationProfile) :
    LanguageProfile :=
  { p with relativization := some r }

/-- Populate `classifierSystem` with a hand-supplied
    `NounCategorizationSystem`. WALS does not cover the full
    @cite{aikhenvald-2000} 7-property schema, so there is no
    `withClassifierSystemFromWALS`. -/
def withClassifierSystem (p : LanguageProfile)
    (cs : NounCategorizationSystem) : LanguageProfile :=
  { p with classifierSystem := some cs }

/-- Populate `indefinites` with a hand-supplied `IndefiniteParadigm`
    (typically the per-language `Fragments/{Lang}/Indefinites.lean::paradigm`).
    WALS F46A covers only the morphological-basis category, not the full
    paradigm, so there is no `withIndefinitesFromWALS`. -/
def withIndefinites (p : LanguageProfile)
    (ip : Typology.Indefinite.IndefiniteParadigm) : LanguageProfile :=
  { p with indefinites := some ip }

/-- Populate `possession` with a hand-supplied `PossessionProfile`. WALS
    Chs 57/58/58B/59 are joined per-domain by `Phenomena/Possession/Typology.lean`'s
    converter functions — composing the profile is a Fragment-level decision. -/
def withPossession (p : LanguageProfile)
    (pp : Typology.Possession.PossessionProfile) : LanguageProfile :=
  { p with possession := some pp }

/-- Populate `plurality` with a hand-supplied `PluralityProfile`
    (@cite{wals-2013} Chs 33-36). -/
def withPlurality (p : LanguageProfile)
    (pp : Typology.PluralityProfile) : LanguageProfile :=
  { p with plurality := some pp }

/-- Populate `pronouns` with a hand-supplied `PronounProfile`
    (@cite{wals-2013} Chs 39-40, 44-48). -/
def withPronouns (p : LanguageProfile)
    (pp : Typology.PronounProfile) : LanguageProfile :=
  { p with pronouns := some pp }

/-- Populate `questions` with a hand-supplied `QuestionProfile`
    (@cite{wals-2013} Chs 92A, 93A, 116A). -/
def withQuestions (p : LanguageProfile)
    (qp : Typology.Question.QuestionProfile) : LanguageProfile :=
  { p with questions := some qp }

/-- Attach free-text notes (including `@cite{...}` keys). -/
def withNotes (p : LanguageProfile) (n : String) : LanguageProfile :=
  { p with notes := n }

/-- Pull every WALS-derivable field in one call. Use for languages with
    no overrides; equivalent to
    `empty iso name |>.withWordOrderFromWALS |>.withAdpositionFromWALS`. -/
def ofWALS (iso name : String) : LanguageProfile :=
  empty iso name |>.withWordOrderFromWALS |>.withAdpositionFromWALS

/-- The language has an obligatory classifier system (`classifierSystem`
    populated with `isObligatory := true`). Any classifier-semantic
    framework that presupposes obligatory classifier morphology in the
    lexicon (Chierchia 1998, Sudo 2016, etc.) requires this predicate
    to hold. Useful as the input-shape requirement for cross-paper
    framework-applicability theorems. -/
def hasObligatoryClassifierSystem (p : LanguageProfile) : Prop :=
  ∃ cs : NounCategorizationSystem,
    p.classifierSystem = some cs ∧ cs.isObligatory = true

instance (p : LanguageProfile) : Decidable p.hasObligatoryClassifierSystem :=
  match h : p.classifierSystem with
  | none => isFalse fun ⟨_, h', _⟩ => by rw [h] at h'; nomatch h'
  | some cs =>
    if hb : cs.isObligatory = true then
      isTrue ⟨cs, h, hb⟩
    else
      isFalse fun ⟨cs', h', hb'⟩ => by
        rw [h] at h'
        exact hb (Option.some.inj h' ▸ hb')

end LanguageProfile

end Typology
