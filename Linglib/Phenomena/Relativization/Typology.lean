import Linglib.Core.Relativization.Profile
import Linglib.Core.Typology.LanguageProfile
import Linglib.Core.WALS.Features.F122A
import Linglib.Core.WALS.Features.F123A
import Linglib.Fragments.English.Typology
import Linglib.Fragments.German.Typology
import Linglib.Fragments.French.Typology
import Linglib.Fragments.Russian.Typology
import Linglib.Fragments.Arabic.Typology
import Linglib.Fragments.Hebrew.Typology
import Linglib.Fragments.Japanese.Typology
import Linglib.Fragments.Korean.Typology
import Linglib.Fragments.Mandarin.Typology
import Linglib.Fragments.Turkish.Typology
import Linglib.Fragments.HindiUrdu.Typology
import Linglib.Fragments.Bambara.Typology
import Linglib.Fragments.Swahili.Typology
import Linglib.Fragments.Tagalog.Typology
import Linglib.Fragments.Malagasy.Typology
import Linglib.Fragments.Finnish.Typology
import Linglib.Fragments.Welsh.Typology
import Linglib.Fragments.Navajo.Typology
import Linglib.Fragments.Yoruba.Typology
import Linglib.Fragments.Mayan.Mam.Typology

/-!
# Cross-Linguistic Typology of Relativization (WALS Chapters 122--123)
@cite{comrie-1989} @cite{keenan-comrie-1977} @cite{comrie-2013}

Cross-linguistic data on relative clause formation strategies from two WALS
chapters by @cite{comrie-2013}, supplemented with the
@cite{keenan-comrie-1977} Accessibility Hierarchy.

The `RelativizationProfile` struct lives in `Core/Relativization/Profile.lean`
and is one of the optional fields on `Core.Typology.LanguageProfile`.
Per-language profiles are defined inside each `Fragments/{Lang}/Typology.lean`
file. This file aggregates 20 of those Fragment profiles into a sample for
cross-linguistic generalizations.

## Ch 122: Relativization on Subjects

How languages form relative clauses on subject position. The main strategies
are: gap (the relativized position is simply empty), pronoun retention (a
resumptive pronoun fills the relativized position), and relative pronoun
(a dedicated wh-element or relative pronoun fills the position and typically
fronts). Additional types include non-reduction (the head noun is repeated
inside the relative clause).

Sample: 166 languages (WALS v2020.4). Gap strategy is the most common for
subject relativization, reflecting the high accessibility of the subject
position on the @cite{keenan-comrie-1977} hierarchy.

## Ch 123: Relativization on Obliques

Whether oblique positions (instrumentals, locatives, etc.) can be relativized,
and if so by what strategy. Many languages that use the gap strategy on
subjects switch to pronoun retention or relative pronouns for obliques, or
cannot relativize obliques at all.

Sample: 112 languages (WALS v2020.4). Gap remains the most common strategy,
but pronoun retention is much more common than for subjects, and a sizeable
minority of languages cannot relativize obliques at all.

## @cite{keenan-comrie-1977} Accessibility Hierarchy

The Accessibility Hierarchy ranks grammatical positions by their
accessibility to relativization:

  Subject > Direct Object > Indirect Object > Oblique > Genitive > Object of Comparison

The paper states three Hierarchy Constraints:

1. **HC₁**: A language must be able to relativize subjects.
2. **HC₂ (Continuity)**: Any RC-forming strategy must apply to a continuous
   segment of the AH.
3. **HC₃ (Cut-off)**: Strategies that apply at one point may cease at any
   lower point.

From these, the **Primary Relativization Constraint** follows: if a
language's primary strategy can apply to a low position, it can also apply
to all higher positions.

## Relative Clause Position

Cross-linguistically, post-nominal relative clauses are more common than
pre-nominal ones, and internally-headed relative clauses are rare. This
correlates with basic word order: VO languages strongly prefer post-nominal,
while OV languages may use pre-nominal.

-/

namespace Phenomena.Relativization.Typology

open Core
open Core.Relativization

-- ============================================================================
-- WALS Data Abbreviations
-- ============================================================================

private abbrev ch122 := Core.WALS.F122A.allData
private abbrev ch123 := Core.WALS.F123A.allData

-- ============================================================================
-- Cross-Linguistic Sample
-- ============================================================================

/-- The 20 `LanguageProfile` aggregates that make up the cross-linguistic
    relativization sample. Each profile is sourced from
    `Fragments/{Lang}/Typology.lean`, where the language's
    `RelativizationProfile` is defined alongside its word order, adposition,
    and morphology profiles.

    Every language in this list must have its `relativization` field
    populated; the convenience accessors below use `Option.get!`, which
    panics at `decide`-time if the field is missing. -/
def allLanguages : List Core.Typology.LanguageProfile :=
  [ Fragments.English.typology
  , Fragments.German.typology
  , Fragments.French.typology
  , Fragments.Russian.typology
  , Fragments.Arabic.typology
  , Fragments.Hebrew.typology
  , Fragments.Japanese.typology
  , Fragments.Korean.typology
  , Fragments.Mandarin.typology
  , Fragments.Turkish.typology
  , Fragments.HindiUrdu.typology
  , Fragments.Bambara.typology
  , Fragments.Swahili.typology
  , Fragments.Tagalog.typology
  , Fragments.Malagasy.typology
  , Fragments.Finnish.typology
  , Fragments.Welsh.typology
  , Fragments.Navajo.typology
  , Fragments.Yoruba.typology
  , Fragments.Mayan.Mam.typology ]

-- ============================================================================
-- Convenience accessors
-- ============================================================================

/-! Per-language convenience accessors that surface the
`RelativizationProfile` from each Fragment's `LanguageProfile`. The
`getD` fallback is `.mixed` for both strategies — values that no WALS
lookup can produce, so every per-language WALS-grounding theorem below
fails loudly if a Fragment ever drops its `relativization` field
(`Option.get!` was tried first but doesn't reduce through `decide`). -/

private def relOf (p : Core.Typology.LanguageProfile) : RelativizationProfile :=
  p.relativization.getD
    { subjStrategy := .mixed, oblStrategy := .mixed,
      rcPosition := .postNominal, lowestRelativizable := .subject }

abbrev english   := relOf Fragments.English.typology
abbrev german    := relOf Fragments.German.typology
abbrev french    := relOf Fragments.French.typology
abbrev russian   := relOf Fragments.Russian.typology
abbrev arabic    := relOf Fragments.Arabic.typology
abbrev hebrew    := relOf Fragments.Hebrew.typology
abbrev japanese  := relOf Fragments.Japanese.typology
abbrev korean    := relOf Fragments.Korean.typology
abbrev mandarin  := relOf Fragments.Mandarin.typology
abbrev turkish   := relOf Fragments.Turkish.typology
abbrev hindiUrdu := relOf Fragments.HindiUrdu.typology
abbrev bambara   := relOf Fragments.Bambara.typology
abbrev swahili   := relOf Fragments.Swahili.typology
abbrev tagalog   := relOf Fragments.Tagalog.typology
abbrev malagasy  := relOf Fragments.Malagasy.typology
abbrev finnish   := relOf Fragments.Finnish.typology
abbrev welsh     := relOf Fragments.Welsh.typology
abbrev navajo    := relOf Fragments.Navajo.typology
abbrev yoruba    := relOf Fragments.Yoruba.typology
abbrev mam       := relOf Fragments.Mayan.Mam.typology

-- ============================================================================
-- WALS aggregate findings
-- ============================================================================

set_option maxRecDepth 2000 in
/-- WALS Ch 122: gap is the most common subject relativization strategy,
    followed by non-reduction, relative pronoun, and pronoun retention. -/
theorem gap_most_common_for_subjects :
    (ch122.filter (·.value == .gap)).length >
    (ch122.filter (·.value == .nonReduction)).length ∧
    (ch122.filter (·.value == .nonReduction)).length >
    (ch122.filter (·.value == .relativePronoun)).length ∧
    (ch122.filter (·.value == .relativePronoun)).length >
    (ch122.filter (·.value == .pronounRetention)).length := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 2000 in
/-- WALS Chs 122/123: pronoun retention is more common for obliques than
    for subjects — a key Accessibility-Hierarchy prediction
    (@cite{keenan-comrie-1977}). -/
theorem retention_increases_for_obliques :
    (ch123.filter (·.value == .pronounRetention)).length >
    (ch122.filter (·.value == .pronounRetention)).length := by decide

set_option maxRecDepth 2000 in
/-- WALS Ch 123: some languages cannot relativize obliques at all,
    contrasting with subjects, where the Ch 122 enum has no "not
    possible" value. -/
theorem obliques_sometimes_not_relativizable :
    (ch123.filter (·.value == .notPossible)).length > 0 := by decide

-- ============================================================================
-- WALS grounding: Fragment ↔ WALS Chs 122/123
-- ============================================================================

/-! Each `LanguageProfile` carries an `iso` field; WALS chapters are
keyed by ISO via `lookupISO`. The two theorems below quantify over an
explicit list of "groundable" languages — those where the Fragment
provides a hand-coded `subjStrategy`/`oblStrategy` *and* WALS has an
entry under the Fragment's ISO *and* both sides agree. Adding a
language to the sample means: (1) populate `relativization` in
`Fragments/{Lang}/Typology.lean`, (2) add it to the relevant grounding
list below.

Languages excluded from grounding:

* **English, Arabic, Yoruba** (subject) — Fragment uses `.mixed`, which
  WALS has no category for.
* **English, Hindi-Urdu, Bambara, Swahili** (oblique) — Fragment and
  WALS disagree on the strategy, recorded in the per-language `notes`.
* **Arabic (`arb`), Malagasy (`mlg`)** — WALS only has rows for the
  Egyptian Arabic / Plateau Malagasy *dialects* (iso `arz` / `plt`);
  our Fragments use the macrolanguage iso codes, so there is no
  matching WALS row to ground against. -/

/-- Languages whose Fragment subject strategy can be grounded against WALS Ch 122. -/
def groundedSubjLanguages : List Core.Typology.LanguageProfile :=
  [ Fragments.German.typology
  , Fragments.French.typology
  , Fragments.Russian.typology
  , Fragments.Hebrew.typology
  , Fragments.Japanese.typology
  , Fragments.Korean.typology
  , Fragments.Mandarin.typology
  , Fragments.Turkish.typology
  , Fragments.Bambara.typology
  , Fragments.Swahili.typology
  , Fragments.Tagalog.typology
  , Fragments.Finnish.typology ]

/-- Languages whose Fragment oblique strategy can be grounded against WALS Ch 123. -/
def groundedOblLanguages : List Core.Typology.LanguageProfile :=
  [ Fragments.German.typology
  , Fragments.French.typology
  , Fragments.Russian.typology
  , Fragments.Hebrew.typology
  , Fragments.Japanese.typology
  , Fragments.Korean.typology
  , Fragments.Mandarin.typology
  , Fragments.Turkish.typology
  , Fragments.Tagalog.typology
  , Fragments.Finnish.typology ]

/-- For every language in `groundedSubjLanguages`, the Fragment's
    hand-coded subject strategy agrees with WALS Ch 122 looked up by
    ISO. Failing this means either WALS data drifted or a Fragment was
    edited inconsistently. -/
theorem subj_strategy_consistent_with_WALS :
    groundedSubjLanguages.all (fun p =>
      (Core.WALS.F122A.lookupISO p.iso).map (fromWALS122A ·.value) =
        p.relativization.map (·.subjStrategy)) = true := by
  decide

/-- For every language in `groundedOblLanguages`, the Fragment's
    hand-coded oblique strategy agrees with WALS Ch 123 looked up by
    ISO. -/
theorem obl_strategy_consistent_with_WALS :
    groundedOblLanguages.all (fun p =>
      (Core.WALS.F123A.lookupISO p.iso).map (fromWALS123A ·.value) =
        p.relativization.map (·.oblStrategy)) = true := by
  decide

end Phenomena.Relativization.Typology
