/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Pronoun.IndefiniteParadigm
import Linglib.Data.WALS.Features.F46A
import Linglib.Fragments.English.Indefinites
import Linglib.Fragments.German.Indefinites
import Linglib.Fragments.Yakut.Indefinites
import Linglib.Fragments.Latin.Indefinites
import Linglib.Fragments.Kannada.Indefinites
import Linglib.Fragments.Slavic.Russian.Indefinites

/-!
# Haspelmath (1997): indefinite pronoun typology

Fragment-derived `IndefiniteParadigm`s for a six-language sample (English,
German, Yakut, Latin, Kannada, Russian), following [haspelmath-1997]'s
nine-function semantic map: per-language bridge theorems verify that each
Fragment's morphological-basis encoding derives the [wals-2013] F46A
classification of the same language (ISO 639-3 join), and per-paradigm
SK/SU/NS syncretism witnesses record the attested patterns. Latin is
absent from F46A's 326-language sample, so it has no bridge theorem;
German and Kannada have gaps in the SK/SU/NS region, so their
`syncretism` is `none` and they have no witness.

The polarity-side projection of the map lives in the sibling
`Studies/Haspelmath1997Polarity.lean`. Substrate:
`Features/Indefinite.lean` (map, morphological bases) and
`Syntax/Pronoun/IndefiniteParadigm.lean` (paradigms, WALS converters).

## Main results

* `english_matches_wals_F46A`, `german_matches_wals_F46A`,
  `yakut_matches_wals_F46A`, `russian_matches_wals_F46A`,
  `kannada_matches_wals_F46A` — Fragment-derived F46A classification
  agrees with WALS.
* `english_paradigm_AAA`, `yakut_paradigm_ABB`, `latin_paradigm_AAB`,
  `russian_paradigm_ABC` — syncretism witnesses.
-/

namespace Haspelmath1997

open _root_.Indefinite
open Data.WALS

/-! ### WALS F46A bridges -/

/-- All four Yakut forms host on interrogative *kim*, deriving
    `.interrogativeBased`, matching WALS for iso "sah". -/
theorem yakut_matches_wals_F46A :
    Yakut.Indefinites.paradigm.toWALS46A =
      (Datapoint.lookupISO F46A.allData "sah").map (·.value) := by decide

/-- *some-* on generic-noun stems derives `.genericNounBased`, matching
    WALS for iso "eng". -/
theorem english_matches_wals_F46A :
    English.Indefinites.paradigm.toWALS46A =
      (Datapoint.lookupISO F46A.allData "eng").map (·.value) := by decide

/-- Special *irgend-* plus generic-noun *jemand*/*etwas* derives `.mixed`,
    matching WALS for iso "deu". -/
theorem german_matches_wals_F46A :
    German.Indefinites.paradigm.toWALS46A =
      (Datapoint.lookupISO F46A.allData "deu").map (·.value) := by decide

/-- All three Russian forms attach to interrogative bases, deriving
    `.interrogativeBased`, matching WALS for iso "rus". -/
theorem russian_matches_wals_F46A :
    Russian.Indefinites.paradigm.toWALS46A =
      (Datapoint.lookupISO F46A.allData "rus").map (·.value) := by decide

/-- Both Kannada forms attach to interrogative *yāru*, deriving
    `.interrogativeBased`, matching WALS for iso "kan". -/
theorem kannada_matches_wals_F46A :
    Kannada.Indefinites.paradigm.toWALS46A =
      (Datapoint.lookupISO F46A.allData "kan").map (·.value) := by decide

/-! ### Syncretism witnesses -/

theorem english_paradigm_AAA :
    English.Indefinites.paradigm.syncretism = some .AAA := rfl

theorem yakut_paradigm_ABB :
    Yakut.Indefinites.paradigm.syncretism = some .ABB := rfl

theorem latin_paradigm_AAB :
    Latin.Indefinites.paradigm.syncretism = some .AAB := rfl

theorem russian_paradigm_ABC :
    Russian.Indefinites.paradigm.syncretism = some .ABC := rfl

end Haspelmath1997
