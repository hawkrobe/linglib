import Linglib.Core.Typology.LanguageProfile

/-!
# Western Armenian typological profile
@cite{bale-khanjian-2014} @cite{bale-khanjian-2008}

Aggregate WALS-style typological profile for Western Armenian
(ISO 639-3 `hyw`).

WALS Ch 55 does *not* have a direct entry for Western Armenian.
The two Armenian-related WALS entries are:
- walsCode `arm`, iso `hye` — Armenian (Eastern), tagged `absent`
- walsCode `arz`, iso `hye` — Armenian (Iranian), tagged `optional`

Neither of these is the diaspora Western Armenian (`hyw`) that
@cite{bale-khanjian-2014} study (a Lebanese-speaker dialect). The
non-obligatory classifier status recorded below is therefore *not*
inherited from WALS — it follows directly from BK 2014's data: numerals
combine with bare nouns (eq. 10a *yergu dəgha vaze-ts* "two boys ran")
and also with the plural form (eq. 10b *yergu dəgha-ner vaze-ts-in*,
same meaning). Plural nouns are additionally *incompatible* with
classifiers (footnote 3, citing @cite{borer-2005} and
@cite{bale-khanjian-2008}).

The Aikhenvald `numeralClassifier` category is a misfit for WA: with
`isObligatory := false` and an essentially empty inventory, WA arguably
has no classifier system in Aikhenvald's sense at all. We retain the
`.numeralClassifier` tag pragmatically (so cross-language theorems can
filter on `classifierType`), but flag the misclassification in the
docstring.
-/

namespace Fragments.Armenian

open Core.Typology in
/-- Western Armenian: SOV→SVO transitional. Classifier system marked
    non-obligatory per @cite{bale-khanjian-2014}'s data (numerals combine
    with bare nouns), not per any WALS entry. -/
def typology : LanguageProfile :=
  LanguageProfile.empty "hyw" "Western Armenian"
    |>.withClassifierSystem
        { family := "Indo-European"
        , classifierType := .numeralClassifier  -- Aikhenvald misfit, see docstring
        , scopes := [.numeralNP]
        , assignment := .semantic
        , realizations := [.freeForm]
        , hasAgreement := false
        , inventorySize := 0  -- no real classifier inventory; cf. docstring
        , isObligatory := false  -- KEY: numerals combine with bare nouns (BK 2014 eq. 10a)
        , hasUnmarkedDefault := false
        , preferredSemantics := []
        , hasObligatoryNumber := false  -- general-number singular per BK 2014
        , pluralClfCooccur := false  -- plurals incompatible with CLs (BK 2014 fn 3)
        , source := "@cite{bale-khanjian-2014} eq. 10; @cite{bale-khanjian-2008}" }
    |>.withNotes ("Western Armenian per @cite{bale-khanjian-2014}: "
               ++ "general-number singular, strict plural, syntactic-complexity "
               ++ "competition à la @cite{katzir-2007}. WALS Ch 55 has no "
               ++ "direct hyw entry; the related arz/hye entry is Iranian "
               ++ "Armenian, not Western Armenian.")

end Fragments.Armenian
