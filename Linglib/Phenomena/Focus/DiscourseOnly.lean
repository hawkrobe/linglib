/-!
# Discourse *only*: Cross-Linguistic Data @cite{ippolito-kiss-williams-2025}

Theory-neutral empirical data on discourse *only* — a clausal connective
that conjoins two propositions while signaling that the second undermines
the evidential direction of the first.

## Cross-linguistic forms

| Language  | Form       | Example              |
|-----------|------------|----------------------|
| Italian   | *solo che* | §3 ex. 8–10, §7 ex. 29a |
| Russian   | *tol'ko*   | §3 ex. 11, §7 ex. 29b–30 |
| Hungarian | *csak*     | §3 ex. 12–13, §7 ex. 29c–31 |
| Mandarin  | *zhǐshì*  | §3 ex. 14, §7 ex. 29d–32 |
| English   | *only*     | §1–2 (paraphrases)  |

## Key Distributional Generalizations

1. The left argument S must be a declarative or exclamative (not an
   info-seeking interrogative) — §5.2
2. The prejacent S' is typically declarative but can vary cross-linguistically
3. S and S' must be relevant to the same QUD
4. S must support some answer α that S' fails to support

## References

- Ippolito, M., Kiss, A. & Williams, W. (2025). Discourse *only*. WCCFL 41.
-/

namespace Phenomena.Focus.DiscourseOnly

/-- A discourse *only* datum. -/
structure DiscourseOnlyDatum where
  /-- Language of the example -/
  language : String
  /-- Surface form of the discourse *only* particle -/
  form : String
  /-- The left clausal argument S (English gloss) -/
  sClause : String
  /-- The right clausal argument S' (English gloss) -/
  sPrimeClause : String
  /-- The QUD addressed (informal description) -/
  qud : String
  /-- Whether the sentence is felicitous in context -/
  felicitous : Bool
  /-- Source reference (section/example number) -/
  source : String
  /-- Notes on distributional properties -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- Italian: *solo che* (§3, ex. 8–10; §7, ex. 29a)
-- ============================================================================

/-- Italian (8): "La casa è bella, solo che è costosissima" -/
def italian_house : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := "solo che"
  , sClause := "The house is beautiful"
  , sPrimeClause := "it is very expensive"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §3 ex. 8"
  , notes := "Canonical discourse only: S supports 'yes', S' undermines it"
  }

/-- Italian (9): "Il film non era male, solo che era un po' lungo" -/
def italian_film : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := "solo che"
  , sClause := "The movie was not bad"
  , sPrimeClause := "it was a bit long"
  , qud := "Was the movie good?"
  , felicitous := true
  , source := "IKW 2025, §3 ex. 9"
  }

/-- Italian (10): "Sarei venuto, solo che non mi hanno invitato" -/
def italian_wouldHaveCome : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := "solo che"
  , sClause := "I would have come"
  , sPrimeClause := "they didn't invite me"
  , qud := "Why didn't you come?"
  , felicitous := true
  , source := "IKW 2025, §3 ex. 10"
  , notes := "Counterfactual left argument"
  }

-- ============================================================================
-- Russian: *tol'ko* (§3, ex. 11; §7, ex. 29b, 30)
-- ============================================================================

/-- Russian (11): "Kvartira bol'šaja, tol'ko kuxnja malen'kaja" -/
def russian_apartment : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := "tol'ko"
  , sClause := "The apartment is big"
  , sPrimeClause := "the kitchen is small"
  , qud := "Is the apartment good?"
  , felicitous := true
  , source := "IKW 2025, §3 ex. 11"
  }

/-- Russian (29b): declarative left arg -/
def russian_decl : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := "tol'ko"
  , sClause := "declarative S"
  , sPrimeClause := "declarative S'"
  , qud := "contextual QUD"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 29b"
  , notes := "Russian tol'ko allows declarative left arguments"
  }

/-- Russian (30): exclamative left arg -/
def russian_excl : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := "tol'ko"
  , sClause := "exclamative S"
  , sPrimeClause := "declarative S'"
  , qud := "contextual QUD"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 30"
  , notes := "Russian tol'ko allows exclamative left arguments"
  }

-- ============================================================================
-- Hungarian: *csak* (§3, ex. 12–13; §7, ex. 29c, 31)
-- ============================================================================

/-- Hungarian (12): "A ház szép, csak drága" -/
def hungarian_house : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := "csak"
  , sClause := "The house is beautiful"
  , sPrimeClause := "it is expensive"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §3 ex. 12"
  }

/-- Hungarian (13): "Szép a ház, csak a kert kicsi" -/
def hungarian_garden : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := "csak"
  , sClause := "The house is beautiful"
  , sPrimeClause := "the garden is small"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §3 ex. 13"
  }

/-- Hungarian (31): exclamative left arg -/
def hungarian_excl : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := "csak"
  , sClause := "exclamative S"
  , sPrimeClause := "declarative S'"
  , qud := "contextual QUD"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 31"
  , notes := "Hungarian csak allows exclamative left arguments"
  }

-- ============================================================================
-- Mandarin: *zhǐshì* (§3, ex. 14; §7, ex. 29d, 32)
-- ============================================================================

/-- Mandarin (14): "Fángzi hěn hǎo, zhǐshì tài guìle" -/
def mandarin_house : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := "zhǐshì"
  , sClause := "The house is very good"
  , sPrimeClause := "it is too expensive"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §3 ex. 14"
  }

/-- Mandarin (32): exclamative prejacent is infelicitous -/
def mandarin_exclPrejacent : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := "zhǐshì"
  , sClause := "declarative S"
  , sPrimeClause := "exclamative S'"
  , qud := "contextual QUD"
  , felicitous := false
  , source := "IKW 2025, §7 ex. 32"
  , notes := "Mandarin zhǐshì disallows exclamative prejacents (S')"
  }

-- ============================================================================
-- English: paraphrases (§1–2)
-- ============================================================================

/-- English (1): "The house is beautiful, only it is too expensive" -/
def english_house : DiscourseOnlyDatum :=
  { language := "English"
  , form := "only"
  , sClause := "The house is beautiful"
  , sPrimeClause := "it is too expensive"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §1 ex. 1"
  }

-- ============================================================================
-- Aggregation
-- ============================================================================

/-- All discourse *only* data from IKW (2025). -/
def allDiscourseOnlyData : List DiscourseOnlyDatum :=
  [ italian_house, italian_film, italian_wouldHaveCome
  , russian_apartment, russian_decl, russian_excl
  , hungarian_house, hungarian_garden, hungarian_excl
  , mandarin_house, mandarin_exclPrejacent
  , english_house
  ]

-- Per-datum verification

theorem italian_house_felicitous : italian_house.felicitous = true := rfl
theorem italian_film_felicitous : italian_film.felicitous = true := rfl
theorem italian_wouldHaveCome_felicitous :
    italian_wouldHaveCome.felicitous = true := rfl
theorem russian_apartment_felicitous :
    russian_apartment.felicitous = true := rfl
theorem hungarian_house_felicitous :
    hungarian_house.felicitous = true := rfl
theorem hungarian_garden_felicitous :
    hungarian_garden.felicitous = true := rfl
theorem mandarin_house_felicitous :
    mandarin_house.felicitous = true := rfl
theorem mandarin_exclPrejacent_infelicitous :
    mandarin_exclPrejacent.felicitous = false := rfl
theorem english_house_felicitous : english_house.felicitous = true := rfl

theorem data_count : allDiscourseOnlyData.length = 12 := rfl

end Phenomena.Focus.DiscourseOnly
