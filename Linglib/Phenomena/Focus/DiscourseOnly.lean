/-!
# Discourse *only*: Cross-Linguistic Data @cite{ippolito-kiss-williams-2025}

Theory-neutral empirical data on discourse *only* — a clausal connective
that conjoins two propositions while signaling that the second undermines
the evidential direction of the first.

## Cross-linguistic forms

| Language  | Form       | Example              |
|-----------|------------|----------------------|
| Italian   | *solo che* | §3 ex. 8–10, §7 ex. 29a, 33 |
| Russian   | *tol'ko*   | §3 ex. 11, §7 ex. 29b, 30 |
| Hungarian | *csak*     | §3 ex. 12–13, §7 ex. 29c, 31 |
| Mandarin  | *zhǐshì*  | §3 ex. 14, §7 ex. 29d, 32 |
| English   | *only*     | §1–2 (paraphrases)  |

## Key Distributional Generalizations

1. The left argument S must be a declarative or exclamative (not an
   info-seeking interrogative) — §5.2
2. The prejacent S' is typically declarative but can vary cross-linguistically
3. S and S' must be relevant to the same QUD
4. S must support some answer α that S' fails to support

## §7 Clause-Type Matrix (Table equivalent)

The paper's main typological result: clause-type restrictions on S' vary
cross-linguistically. Italian *solo che* restricts S' to declaratives.
Russian *tol'ko* and Hungarian *csak* allow all types except canonical
wh-questions. Mandarin *zhǐshì* additionally blocks exclamative S'.

## References

- Ippolito, M., Kiss, A. & Williams, W. (2025). Discourse *only*. WCCFL 41.
-/

namespace Phenomena.Focus.DiscourseOnly

-- Clause Type Classification

/-- Clause types relevant to discourse *only*'s distributional restrictions.

Fine-grained enough to capture the key contrasts in IKW §5.2 and §7:
- Canonical info-seeking questions fail the doxastic condition (DOX_sp ⊄ q)
- Biased/rhetorical questions satisfy it (DOX_sp ⊆ q for some q)
- High-negation polar questions pattern with biased questions -/
inductive ClauseType where
  | declarative
  | canonicalPolarQ
  | highNegPolarQ
  | canonicalWhQ
  | negRhetoricalWhQ
  | imperative
  | exclamative
  deriving DecidableEq, Repr, BEq

/-- Position of the clause in the discourse *only* construction. -/
inductive ArgPosition where
  | left   -- S (establishes evidential direction)
  | right  -- S' (fails to support direction)
  deriving DecidableEq, Repr, BEq

-- Data Structure

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
  /-- Clause type of the tested argument -/
  clauseType : Option ClauseType := none
  /-- Which argument position is being tested -/
  position : Option ArgPosition := none
  /-- Notes on distributional properties -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- §3: Core Examples (canonical declarative-declarative)
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
  , clauseType := some .declarative
  , position := some .right
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
  , clauseType := some .declarative
  , position := some .right
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
  , clauseType := some .declarative
  , position := some .right
  , notes := "Counterfactual left argument"
  }

/-- Russian (11): "Kvartira bol'šaja, tol'ko kuxnja malen'kaja" -/
def russian_apartment : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := "tol'ko"
  , sClause := "The apartment is big"
  , sPrimeClause := "the kitchen is small"
  , qud := "Is the apartment good?"
  , felicitous := true
  , source := "IKW 2025, §3 ex. 11"
  , clauseType := some .declarative
  , position := some .right
  }

/-- Hungarian (12): "A ház szép, csak drága" -/
def hungarian_house : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := "csak"
  , sClause := "The house is beautiful"
  , sPrimeClause := "it is expensive"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §3 ex. 12"
  , clauseType := some .declarative
  , position := some .right
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
  , clauseType := some .declarative
  , position := some .right
  }

/-- Mandarin (14): "Fángzi hěn hǎo, zhǐshì tài guìle" -/
def mandarin_house : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := "zhǐshì"
  , sClause := "The house is very good"
  , sPrimeClause := "it is too expensive"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §3 ex. 14"
  , clauseType := some .declarative
  , position := some .right
  }

/-- English (1): "The house is beautiful, only it is too expensive" -/
def english_house : DiscourseOnlyDatum :=
  { language := "English"
  , form := "only"
  , sClause := "The house is beautiful"
  , sPrimeClause := "it is too expensive"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §1 ex. 1"
  , clauseType := some .declarative
  , position := some .right
  }

-- ============================================================================
-- §7: Russian *tol'ko* — S' clause-type variation (ex. 30a–f)
-- ============================================================================

/-- Russian (30a): canonical polar Q as S' — felicitous -/
def russian_s'_polarQ : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := "tol'ko"
  , sClause := "The house is beautiful"
  , sPrimeClause := "has it been renovated? [polar Q]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 30a"
  , clauseType := some .canonicalPolarQ
  , position := some .right
  }

/-- Russian (30b): high-negation polar Q as S' — felicitous -/
def russian_s'_highNegQ : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := "tol'ko"
  , sClause := "The house is beautiful"
  , sPrimeClause := "hasn't it been renovated? [high-neg polar Q]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 30b"
  , clauseType := some .highNegPolarQ
  , position := some .right
  }

/-- Russian (30c): canonical wh-Q as S' — infelicitous -/
def russian_s'_whQ : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := "tol'ko"
  , sClause := "The house is beautiful"
  , sPrimeClause := "when was it renovated? [wh-Q]"
  , qud := "Should we buy the house?"
  , felicitous := false
  , source := "IKW 2025, §7 ex. 30c"
  , clauseType := some .canonicalWhQ
  , position := some .right
  }

/-- Russian (30d): negative rhetorical wh-Q as S' — felicitous -/
def russian_s'_negRhetWhQ : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := "tol'ko"
  , sClause := "The house is beautiful"
  , sPrimeClause := "who would renovate it? [neg-rhet wh-Q]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 30d"
  , clauseType := some .negRhetoricalWhQ
  , position := some .right
  , notes := "Rhetorical Q: speaker believes answer (nobody), DOX_sp ⊆ q"
  }

/-- Russian (30e): imperative as S' — felicitous -/
def russian_s'_imperative : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := "tol'ko"
  , sClause := "The house is beautiful"
  , sPrimeClause := "don't buy it just now [imperative]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 30e"
  , clauseType := some .imperative
  , position := some .right
  }

/-- Russian (30f): exclamative as S' — felicitous -/
def russian_s'_exclamative : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := "tol'ko"
  , sClause := "The house is beautiful"
  , sPrimeClause := "what neighbours! [exclamative]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 30f"
  , clauseType := some .exclamative
  , position := some .right
  }

-- ============================================================================
-- §7: Hungarian *csak* — S' clause-type variation (ex. 31a–f)
-- ============================================================================

/-- Hungarian (31a): canonical polar Q as S' — felicitous -/
def hungarian_s'_polarQ : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := "csak"
  , sClause := "The house is beautiful"
  , sPrimeClause := "has it been renovated? [polar Q]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 31a"
  , clauseType := some .canonicalPolarQ
  , position := some .right
  }

/-- Hungarian (31b): high-negation polar Q as S' — felicitous -/
def hungarian_s'_highNegQ : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := "csak"
  , sClause := "The house is beautiful"
  , sPrimeClause := "hasn't it been renovated? [high-neg polar Q]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 31b"
  , clauseType := some .highNegPolarQ
  , position := some .right
  }

/-- Hungarian (31c): canonical wh-Q as S' — infelicitous -/
def hungarian_s'_whQ : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := "csak"
  , sClause := "The house is beautiful"
  , sPrimeClause := "when was it renovated? [wh-Q]"
  , qud := "Should we buy the house?"
  , felicitous := false
  , source := "IKW 2025, §7 ex. 31c"
  , clauseType := some .canonicalWhQ
  , position := some .right
  }

/-- Hungarian (31d): negative rhetorical wh-Q as S' — felicitous -/
def hungarian_s'_negRhetWhQ : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := "csak"
  , sClause := "The house is beautiful"
  , sPrimeClause := "who would renovate it? [neg-rhet wh-Q]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 31d"
  , clauseType := some .negRhetoricalWhQ
  , position := some .right
  , notes := "Rhetorical Q: speaker believes answer (nobody), DOX_sp ⊆ q"
  }

/-- Hungarian (31e): imperative as S' — felicitous -/
def hungarian_s'_imperative : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := "csak"
  , sClause := "The house is beautiful"
  , sPrimeClause := "don't buy it just now [imperative]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 31e"
  , clauseType := some .imperative
  , position := some .right
  }

/-- Hungarian (31f): exclamative as S' — felicitous -/
def hungarian_s'_exclamative : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := "csak"
  , sClause := "The house is beautiful"
  , sPrimeClause := "what neighbours! [exclamative]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 31f"
  , clauseType := some .exclamative
  , position := some .right
  }

-- ============================================================================
-- §7: Mandarin *zhǐshì* — S' clause-type variation (ex. 32a–f)
-- ============================================================================

/-- Mandarin (32a): canonical polar Q as S' — felicitous -/
def mandarin_s'_polarQ : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := "zhǐshì"
  , sClause := "The house is very good"
  , sPrimeClause := "has it been renovated? [polar Q]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 32a"
  , clauseType := some .canonicalPolarQ
  , position := some .right
  }

/-- Mandarin (32b): high-negation polar Q as S' — felicitous -/
def mandarin_s'_highNegQ : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := "zhǐshì"
  , sClause := "The house is very good"
  , sPrimeClause := "hasn't it been renovated? [high-neg polar Q]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 32b"
  , clauseType := some .highNegPolarQ
  , position := some .right
  }

/-- Mandarin (32c): canonical wh-Q as S' — infelicitous -/
def mandarin_s'_whQ : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := "zhǐshì"
  , sClause := "The house is very good"
  , sPrimeClause := "when was it renovated? [wh-Q]"
  , qud := "Should we buy the house?"
  , felicitous := false
  , source := "IKW 2025, §7 ex. 32c"
  , clauseType := some .canonicalWhQ
  , position := some .right
  }

/-- Mandarin (32d): negative rhetorical wh-Q as S' — felicitous -/
def mandarin_s'_negRhetWhQ : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := "zhǐshì"
  , sClause := "The house is very good"
  , sPrimeClause := "who would renovate it? [neg-rhet wh-Q]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 32d"
  , clauseType := some .negRhetoricalWhQ
  , position := some .right
  , notes := "Rhetorical Q: speaker believes answer (nobody), DOX_sp ⊆ q"
  }

/-- Mandarin (32e): imperative as S' — felicitous -/
def mandarin_s'_imperative : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := "zhǐshì"
  , sClause := "The house is very good"
  , sPrimeClause := "don't buy it just now [imperative]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 32e"
  , clauseType := some .imperative
  , position := some .right
  }

/-- Mandarin (32f): exclamative as S' — INFELICITOUS (Mandarin-specific) -/
def mandarin_s'_exclamative : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := "zhǐshì"
  , sClause := "The house is very good"
  , sPrimeClause := "what neighbours! [exclamative]"
  , qud := "Should we buy the house?"
  , felicitous := false
  , source := "IKW 2025, §7 ex. 32f"
  , clauseType := some .exclamative
  , position := some .right
  , notes := "Mandarin zhǐshì uniquely blocks exclamative S'"
  }

-- ============================================================================
-- §7: Italian *solo che* — S' clause-type variation (ex. 33a–e)
-- Italian uniquely restricts S' to declaratives only.
-- ============================================================================

/-- Italian (33a): declarative as S' — felicitous -/
def italian_s'_declarative : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := "solo che"
  , sClause := "The house is beautiful"
  , sPrimeClause := "it is very expensive [declarative]"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 33a"
  , clauseType := some .declarative
  , position := some .right
  }

/-- Italian (33b): polar Q as S' — infelicitous -/
def italian_s'_polarQ : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := "solo che"
  , sClause := "The house is beautiful"
  , sPrimeClause := "has it been renovated? [polar Q]"
  , qud := "Should we buy the house?"
  , felicitous := false
  , source := "IKW 2025, §7 ex. 33b"
  , clauseType := some .canonicalPolarQ
  , position := some .right
  , notes := "Italian solo che blocks non-declarative S'"
  }

/-- Italian (33c): wh-Q as S' — infelicitous -/
def italian_s'_whQ : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := "solo che"
  , sClause := "The house is beautiful"
  , sPrimeClause := "when was it renovated? [wh-Q]"
  , qud := "Should we buy the house?"
  , felicitous := false
  , source := "IKW 2025, §7 ex. 33c"
  , clauseType := some .canonicalWhQ
  , position := some .right
  , notes := "Italian solo che blocks non-declarative S'"
  }

/-- Italian (33d): imperative as S' — infelicitous -/
def italian_s'_imperative : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := "solo che"
  , sClause := "The house is beautiful"
  , sPrimeClause := "don't buy it just now [imperative]"
  , qud := "Should we buy the house?"
  , felicitous := false
  , source := "IKW 2025, §7 ex. 33d"
  , clauseType := some .imperative
  , position := some .right
  , notes := "Italian solo che blocks non-declarative S'"
  }

/-- Italian (33e): exclamative as S' — infelicitous -/
def italian_s'_exclamative : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := "solo che"
  , sClause := "The house is beautiful"
  , sPrimeClause := "what neighbours! [exclamative]"
  , qud := "Should we buy the house?"
  , felicitous := false
  , source := "IKW 2025, §7 ex. 33e"
  , clauseType := some .exclamative
  , position := some .right
  , notes := "Italian solo che blocks non-declarative S'"
  }

-- ============================================================================
-- Aggregation
-- ============================================================================

/-- Core discourse *only* examples from §3. -/
def coreExamples : List DiscourseOnlyDatum :=
  [ italian_house, italian_film, italian_wouldHaveCome
  , russian_apartment
  , hungarian_house, hungarian_garden
  , mandarin_house
  , english_house
  ]

/-- §7 clause-type variation data: S' restrictions. -/
def clauseTypeData : List DiscourseOnlyDatum :=
  [ -- Russian S' (30a–f)
    russian_s'_polarQ, russian_s'_highNegQ, russian_s'_whQ
  , russian_s'_negRhetWhQ, russian_s'_imperative, russian_s'_exclamative
  -- Hungarian S' (31a–f)
  , hungarian_s'_polarQ, hungarian_s'_highNegQ, hungarian_s'_whQ
  , hungarian_s'_negRhetWhQ, hungarian_s'_imperative, hungarian_s'_exclamative
  -- Mandarin S' (32a–f)
  , mandarin_s'_polarQ, mandarin_s'_highNegQ, mandarin_s'_whQ
  , mandarin_s'_negRhetWhQ, mandarin_s'_imperative, mandarin_s'_exclamative
  -- Italian S' (33a–e)
  , italian_s'_declarative, italian_s'_polarQ, italian_s'_whQ
  , italian_s'_imperative, italian_s'_exclamative
  ]

/-- All discourse *only* data from IKW (2025). -/
def allDiscourseOnlyData : List DiscourseOnlyDatum :=
  coreExamples ++ clauseTypeData

-- Per-datum verification: core examples

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
theorem english_house_felicitous : english_house.felicitous = true := rfl

-- Per-datum verification: §7 clause-type variation

-- Russian: ✓ polar Q, ✓ high-neg Q, ✗ wh-Q, ✓ neg-rhet wh-Q, ✓ imperative, ✓ exclamative
theorem russian_s'_polarQ_ok : russian_s'_polarQ.felicitous = true := rfl
theorem russian_s'_highNegQ_ok : russian_s'_highNegQ.felicitous = true := rfl
theorem russian_s'_whQ_bad : russian_s'_whQ.felicitous = false := rfl
theorem russian_s'_negRhetWhQ_ok : russian_s'_negRhetWhQ.felicitous = true := rfl
theorem russian_s'_imperative_ok : russian_s'_imperative.felicitous = true := rfl
theorem russian_s'_exclamative_ok : russian_s'_exclamative.felicitous = true := rfl

-- Hungarian: ✓ polar Q, ✓ high-neg Q, ✗ wh-Q, ✓ neg-rhet wh-Q, ✓ imperative, ✓ exclamative
theorem hungarian_s'_polarQ_ok : hungarian_s'_polarQ.felicitous = true := rfl
theorem hungarian_s'_highNegQ_ok : hungarian_s'_highNegQ.felicitous = true := rfl
theorem hungarian_s'_whQ_bad : hungarian_s'_whQ.felicitous = false := rfl
theorem hungarian_s'_negRhetWhQ_ok : hungarian_s'_negRhetWhQ.felicitous = true := rfl
theorem hungarian_s'_imperative_ok : hungarian_s'_imperative.felicitous = true := rfl
theorem hungarian_s'_exclamative_ok : hungarian_s'_exclamative.felicitous = true := rfl

-- Mandarin: ✓ polar Q, ✓ high-neg Q, ✗ wh-Q, ✓ neg-rhet wh-Q, ✓ imperative, ✗ exclamative
theorem mandarin_s'_polarQ_ok : mandarin_s'_polarQ.felicitous = true := rfl
theorem mandarin_s'_highNegQ_ok : mandarin_s'_highNegQ.felicitous = true := rfl
theorem mandarin_s'_whQ_bad : mandarin_s'_whQ.felicitous = false := rfl
theorem mandarin_s'_negRhetWhQ_ok : mandarin_s'_negRhetWhQ.felicitous = true := rfl
theorem mandarin_s'_imperative_ok : mandarin_s'_imperative.felicitous = true := rfl
theorem mandarin_s'_exclamative_bad : mandarin_s'_exclamative.felicitous = false := rfl

-- Italian S': ✓ declarative, ✗ polar Q, ✗ wh-Q, ✗ imperative, ✗ exclamative
theorem italian_s'_declarative_ok : italian_s'_declarative.felicitous = true := rfl
theorem italian_s'_polarQ_bad : italian_s'_polarQ.felicitous = false := rfl
theorem italian_s'_whQ_bad : italian_s'_whQ.felicitous = false := rfl
theorem italian_s'_imperative_bad : italian_s'_imperative.felicitous = false := rfl
theorem italian_s'_exclamative_bad : italian_s'_exclamative.felicitous = false := rfl

-- Cross-linguistic generalizations

/-- Canonical wh-Q as S' is blocked in all four languages. -/
theorem whQ_s'_universally_blocked :
    russian_s'_whQ.felicitous = false ∧
    hungarian_s'_whQ.felicitous = false ∧
    mandarin_s'_whQ.felicitous = false ∧
    italian_s'_whQ.felicitous = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Negative rhetorical wh-Q as S' is allowed in all languages that allow
non-declarative S'. The doxastic condition explains this: the speaker believes
the answer to a rhetorical question (DOX_sp ⊆ q). -/
theorem negRhetWhQ_s'_allowed_where_nonDecl_ok :
    russian_s'_negRhetWhQ.felicitous = true ∧
    hungarian_s'_negRhetWhQ.felicitous = true ∧
    mandarin_s'_negRhetWhQ.felicitous = true := ⟨rfl, rfl, rfl⟩

/-- Italian *solo che* restricts S' to declaratives — the most restrictive
pattern in the sample. -/
theorem italian_s'_only_declarative :
    italian_s'_declarative.felicitous = true ∧
    italian_s'_polarQ.felicitous = false ∧
    italian_s'_whQ.felicitous = false ∧
    italian_s'_imperative.felicitous = false ∧
    italian_s'_exclamative.felicitous = false := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Mandarin *zhǐshì* uniquely blocks exclamative S' among the languages
that otherwise allow non-declarative S'. -/
theorem mandarin_blocks_exclamative_s' :
    mandarin_s'_exclamative.felicitous = false ∧
    russian_s'_exclamative.felicitous = true ∧
    hungarian_s'_exclamative.felicitous = true := ⟨rfl, rfl, rfl⟩

-- Counts

theorem core_count : coreExamples.length = 8 := rfl
theorem clauseType_count : clauseTypeData.length = 23 := rfl
theorem total_count : allDiscourseOnlyData.length = 31 := rfl

end Phenomena.Focus.DiscourseOnly
