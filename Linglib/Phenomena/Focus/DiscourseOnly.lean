import Linglib.Fragments.Italian.DiscourseParticles
import Linglib.Fragments.Russian.DiscourseParticles
import Linglib.Fragments.Hungarian.DiscourseParticles
import Linglib.Fragments.Mandarin.DiscourseParticles

/-!
# Discourse *only*: Cross-Linguistic Data @cite{ippolito-kiss-williams-2025}

Theory-neutral empirical data on discourse *only* — a clausal connective
that conjoins two propositions while signaling that the second undermines
the evidential direction of the first.

## Cross-linguistic forms

| Language  | Form       | Example              |
|-----------|------------|----------------------|
| Italian   | *solo che* | §7 ex. 29a, 33      |
| Russian   | *tol'ko*   | §7 ex. 29b, 30      |
| Hungarian | *csak*     | §7 ex. 29c, 31      |
| Mandarin  | *zhǐshì*  | §7 ex. 29d, 32      |
| English   | *only*     | §1 ex. 2             |

## Key Distributional Generalizations

1. The left argument S cannot be a canonical info-seeking interrogative
   (§5.2); declaratives, imperatives, exclamatives, and biased/rhetorical
   questions are all attested as S
2. The prejacent S' varies cross-linguistically: Russian and Hungarian
   allow all types; Mandarin blocks exclamatives; Italian restricts S' to
   declaratives only (§7)
3. S and S' must be relevant to the same QUD
4. S must support some answer α that S' fails to support

## §7 Clause-Type Matrix (Table equivalent)

The paper's main typological result: clause-type restrictions on S' vary
cross-linguistically. Italian *solo che* restricts S' to declaratives only.
Russian *tol'ko* and Hungarian *csak* allow all clause types as S'.
Mandarin *zhǐshì* allows all types except exclamatives.

## References

- Ippolito, M., Kiss, A. & Williams, W. (2025). Discourse *only*. WCCFL 41.
-/

namespace Phenomena.Focus.DiscourseOnly

open Fragments.Italian.DiscourseParticles (soloChe)
open Fragments.Russian.DiscourseParticles (tolko)
open Fragments.Hungarian.DiscourseParticles (csak)
open Fragments.Mandarin.DiscourseParticles (zhishi)

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

/-- A discourse *only* datum with original language text and English glosses. -/
structure DiscourseOnlyDatum where
  /-- Language of the example -/
  language : String
  /-- Surface form of the discourse *only* particle -/
  form : String
  /-- The left clausal argument S (original language text) -/
  sClause : String
  /-- The right clausal argument S' (original language text) -/
  sPrimeClause : String
  /-- English gloss of S (empty for English examples) -/
  sGloss : String := ""
  /-- English gloss of S' (empty for English examples) -/
  sPrimeGloss : String := ""
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
-- §7 ex. 29: Core Examples (cross-linguistic declarative-declarative)
-- ============================================================================

/-- Italian (29a): "La casa è bella, solo che è costosissima" -/
def italian_house : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := soloChe.form
  , sClause := "La casa è bella"
  , sPrimeClause := "è costosissima"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "it's very expensive"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 29a"
  , clauseType := some .declarative
  , position := some .right
  , notes := "Canonical discourse only: S supports 'yes', S' undermines it"
  }

/-- Russian (29b): "Dom krasivyj, tol'ko ochen' dorogoj" -/
def russian_house : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := tolko.form
  , sClause := "Dom krasivyj"
  , sPrimeClause := "ochen' dorogoj"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "it's very expensive"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 29b"
  , clauseType := some .declarative
  , position := some .right
  }

/-- Hungarian (29c): "Szép ez a ház, csak nagyon drága" -/
def hungarian_house : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := csak.form
  , sClause := "Szép ez a ház"
  , sPrimeClause := "nagyon drága"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "it's very expensive"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 29c"
  , clauseType := some .declarative
  , position := some .right
  }

/-- Mandarin (29d): "Zhège fángzì hěn piàoliang, zhǐshì yǒudiǎr guì" -/
def mandarin_house : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := zhishi.form
  , sClause := "Zhège fángzì hěn piàoliang"
  , sPrimeClause := "yǒudiǎr guì"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "it's a bit expensive"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 29d"
  , clauseType := some .declarative
  , position := some .right
  }

/-- English (2): "The house is beautiful, only it's too expensive" -/
def english_house : DiscourseOnlyDatum :=
  { language := "English"
  , form := "only"
  , sClause := "The house is beautiful"
  , sPrimeClause := "it's too expensive"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §1 ex. 2"
  , clauseType := some .declarative
  , position := some .right
  }

-- ============================================================================
-- §7: Russian *tol'ko* — S' clause-type variation (ex. 30a–f)
-- All felicitous: Russian allows all clause types as S'.
-- ============================================================================

/-- Russian (30a): "Dom krasivyj, tol'ko byl li on otremontirovan?" -/
def russian_s'_polarQ : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := tolko.form
  , sClause := "Dom krasivyj"
  , sPrimeClause := "byl li on otremontirovan?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "has it been renovated?"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 30a"
  , clauseType := some .canonicalPolarQ
  , position := some .right
  }

/-- Russian (30b): "Dom krasivyj, tol'ko ne bylo li tam problemy s kryshoj?" -/
def russian_s'_highNegQ : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := tolko.form
  , sClause := "Dom krasivyj"
  , sPrimeClause := "ne bylo li tam problemy s kryshoj?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "didn't it have problems with the roof?"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 30b"
  , clauseType := some .highNegPolarQ
  , position := some .right
  }

/-- Russian (30c): "Dom krasivyj, tol'ko kogda on byl otremontirovan?" -/
def russian_s'_whQ : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := tolko.form
  , sClause := "Dom krasivyj"
  , sPrimeClause := "kogda on byl otremontirovan?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "when was it renovated?"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 30c"
  , clauseType := some .canonicalWhQ
  , position := some .right
  }

/-- Russian (30d): "Dom krasivyj, tol'ko kto za nego zaplatit dva milliona?" -/
def russian_s'_negRhetWhQ : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := tolko.form
  , sClause := "Dom krasivyj"
  , sPrimeClause := "kto za nego zaplatit dva milliona?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "who will pay two millions for it?"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 30d"
  , clauseType := some .negRhetoricalWhQ
  , position := some .right
  , notes := "Rhetorical Q: speaker believes answer is 'nobody', DOX_sp ⊆ q"
  }

/-- Russian (30e): "Voz'mi moj proezdnoj na metro, tol'ko ne poterjaj ego" -/
def russian_s'_imperative : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := tolko.form
  , sClause := "Voz'mi moj proezdnoj na metro"
  , sPrimeClause := "ne poterjaj ego"
  , sGloss := "Take my metro pass"
  , sPrimeGloss := "don't lose it"
  , qud := "Is the addressee allowed to take the speaker's metro pass?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 30e"
  , clauseType := some .imperative
  , position := some .right
  }

/-- Russian (30f): "Kakoj krasivyj dom! Tol'ko vot rajon uzhasnyj!" -/
def russian_s'_exclamative : DiscourseOnlyDatum :=
  { language := "Russian"
  , form := tolko.form
  , sClause := "Kakoj krasivyj dom!"
  , sPrimeClause := "vot rajon uzhasnyj!"
  , sGloss := "What a beautiful house!"
  , sPrimeGloss := "what a terrible neighborhood!"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 30f"
  , clauseType := some .exclamative
  , position := some .right
  }

-- ============================================================================
-- §7: Hungarian *csak* — S' clause-type variation (ex. 31a–f)
-- All felicitous: Hungarian allows all clause types as S'.
-- ============================================================================

/-- Hungarian (31a): "Szép ez a ház, csak fel van újítva?" -/
def hungarian_s'_polarQ : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := csak.form
  , sClause := "Szép ez a ház"
  , sPrimeClause := "fel van újítva?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "has it been renovated?"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 31a"
  , clauseType := some .canonicalPolarQ
  , position := some .right
  }

/-- Hungarian (31b): "Szép ez a ház, csak nem ezt adták el az előbb?" -/
def hungarian_s'_highNegQ : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := csak.form
  , sClause := "Szép ez a ház"
  , sPrimeClause := "nem ezt adták el az előbb?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "wasn't it sold just now?"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 31b"
  , clauseType := some .highNegPolarQ
  , position := some .right
  }

/-- Hungarian (31c): "Szép ez a ház, csak mikor lett felújítva?" -/
def hungarian_s'_whQ : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := csak.form
  , sClause := "Szép ez a ház"
  , sPrimeClause := "mikor lett felújítva?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "when has it been renovated?"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 31c"
  , clauseType := some .canonicalWhQ
  , position := some .right
  }

/-- Hungarian (31d): "Szép ez a ház, csak ki fizetne érte 2 milliót?" -/
def hungarian_s'_negRhetWhQ : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := csak.form
  , sClause := "Szép ez a ház"
  , sPrimeClause := "ki fizetne érte 2 milliót?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "who would pay 2 million for it?"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 31d"
  , clauseType := some .negRhetoricalWhQ
  , position := some .right
  , notes := "Rhetorical Q: speaker believes answer is 'nobody', DOX_sp ⊆ q"
  }

/-- Hungarian (31e): "Vidd el a bérletem, csak ne hagyd el!" -/
def hungarian_s'_imperative : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := csak.form
  , sClause := "Vidd el a bérletem"
  , sPrimeClause := "ne hagyd el!"
  , sGloss := "Take my metro pass"
  , sPrimeGloss := "don't lose it"
  , qud := "Is the addressee allowed to take the speaker's metro pass?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 31e"
  , clauseType := some .imperative
  , position := some .right
  }

/-- Hungarian (31f): "Milyen szép ház! Csak micsoda környék!" -/
def hungarian_s'_exclamative : DiscourseOnlyDatum :=
  { language := "Hungarian"
  , form := csak.form
  , sClause := "Milyen szép ház!"
  , sPrimeClause := "micsoda környék!"
  , sGloss := "What a beautiful house!"
  , sPrimeGloss := "what a terrible neighborhood!"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 31f"
  , clauseType := some .exclamative
  , position := some .right
  }

-- ============================================================================
-- §7: Mandarin *zhǐshì* — S' clause-type variation (ex. 32a–f)
-- All felicitous except 32f (exclamative): Mandarin uniquely blocks
-- exclamative S'.
-- ============================================================================

/-- Mandarin (32a): "Zhège fángzì hěn piàoliang, zhǐshì zhuāngxīu le ma?" -/
def mandarin_s'_polarQ : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := zhishi.form
  , sClause := "Zhège fángzì hěn piàoliang"
  , sPrimeClause := "zhuāngxīu le ma?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "has it been renovated?"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 32a"
  , clauseType := some .canonicalPolarQ
  , position := some .right
  , notes := "Marked % (marginal) in the paper"
  }

/-- Mandarin (32b): "Zhège fángzì hěn piàoliang, zhǐshì tā bú shì diànlì xìtǒng chū le wèntí ma?" -/
def mandarin_s'_highNegQ : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := zhishi.form
  , sClause := "Zhège fángzì hěn piàoliang"
  , sPrimeClause := "tā bú shì diànlì xìtǒng chū le wèntí ma?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "didn't it have a problem with the electric system?"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 32b"
  , clauseType := some .highNegPolarQ
  , position := some .right
  }

/-- Mandarin (32c): "Zhège fángzì hěn piàoliang, zhǐshì tā shénme shíhou zhuāngxīu de?" -/
def mandarin_s'_whQ : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := zhishi.form
  , sClause := "Zhège fángzì hěn piàoliang"
  , sPrimeClause := "tā shénme shíhou zhuāngxīu de?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "when has it been renovated?"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 32c"
  , clauseType := some .canonicalWhQ
  , position := some .right
  , notes := "Paper has optional elements: tā (shì) shénme shíhou zhuāngxīu de (ne)?"
  }

/-- Mandarin (32d): "Zhège fángzì hěn piàoliang, zhǐshì shéi huì fù liǎngbǎiwàn mǎi ne?" -/
def mandarin_s'_negRhetWhQ : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := zhishi.form
  , sClause := "Zhège fángzì hěn piàoliang"
  , sPrimeClause := "shéi huì fù liǎngbǎiwàn mǎi ne?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "who would pay 2 millions for it?"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 32d"
  , clauseType := some .negRhetoricalWhQ
  , position := some .right
  , notes := "Rhetorical Q: speaker believes answer is 'nobody', DOX_sp ⊆ q. Paper has optional (yǒu)."
  }

/-- Mandarin (32e): "Yòng wǒ de jiāotōngkǎ ba, zhǐshì bié diū le" -/
def mandarin_s'_imperative : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := zhishi.form
  , sClause := "Yòng wǒ de jiāotōngkǎ ba"
  , sPrimeClause := "bié diū le"
  , sGloss := "Use my metro pass"
  , sPrimeGloss := "don't lose it"
  , qud := "Is the addressee allowed to take the speaker's metro pass?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 32e"
  , clauseType := some .imperative
  , position := some .right
  }

/-- Mandarin (32f): "Duōme piàoliang de fángzi a! #Zhǐshì nàme chà de shèqū huánjìng!" -/
def mandarin_s'_exclamative : DiscourseOnlyDatum :=
  { language := "Mandarin"
  , form := zhishi.form
  , sClause := "Duōme piàoliang de fángzi a!"
  , sPrimeClause := "nàme chà de shèqū huánjìng!"
  , sGloss := "What a beautiful house!"
  , sPrimeGloss := "what a terrible neighborhood!"
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

/-- Italian (33a): "La casa è bella, solo che è costosissima" -/
def italian_s'_declarative : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := soloChe.form
  , sClause := "La casa è bella"
  , sPrimeClause := "è costosissima"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "it's very expensive"
  , qud := "Should we buy the house?"
  , felicitous := true
  , source := "IKW 2025, §7 ex. 33a"
  , clauseType := some .declarative
  , position := some .right
  }

/-- Italian (33b): "La casa è bella, solo che *è stata ristrutturata?" -/
def italian_s'_polarQ : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := soloChe.form
  , sClause := "La casa è bella"
  , sPrimeClause := "è stata ristrutturata?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "has it been renovated?"
  , qud := "Should we buy the house?"
  , felicitous := false
  , source := "IKW 2025, §7 ex. 33b"
  , clauseType := some .canonicalPolarQ
  , position := some .right
  , notes := "Italian solo che blocks non-declarative S'"
  }

/-- Italian (33c): "La casa è bella, solo che *quando è stata ristrutturata?" -/
def italian_s'_whQ : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := soloChe.form
  , sClause := "La casa è bella"
  , sPrimeClause := "quando è stata ristrutturata?"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "when has it been renovated?"
  , qud := "Should we buy the house?"
  , felicitous := false
  , source := "IKW 2025, §7 ex. 33c"
  , clauseType := some .canonicalWhQ
  , position := some .right
  , notes := "Italian solo che blocks non-declarative S'"
  }

/-- Italian (33d): "La casa è bella, solo che *non comprarla adesso" -/
def italian_s'_imperative : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := soloChe.form
  , sClause := "La casa è bella"
  , sPrimeClause := "non comprarla adesso"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "don't buy it just now"
  , qud := "Should we buy the house?"
  , felicitous := false
  , source := "IKW 2025, §7 ex. 33d"
  , clauseType := some .imperative
  , position := some .right
  , notes := "Italian solo che blocks non-declarative S'"
  }

/-- Italian (33e): "La casa è bella, solo che *che vicini!" -/
def italian_s'_exclamative : DiscourseOnlyDatum :=
  { language := "Italian"
  , form := soloChe.form
  , sClause := "La casa è bella"
  , sPrimeClause := "che vicini!"
  , sGloss := "The house is beautiful"
  , sPrimeGloss := "what neighbours!"
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

/-- Core discourse *only* examples from §7 ex. 29 + §1 ex. 2. -/
def coreExamples : List DiscourseOnlyDatum :=
  [ italian_house, russian_house, hungarian_house, mandarin_house
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
theorem russian_house_felicitous : russian_house.felicitous = true := rfl
theorem hungarian_house_felicitous : hungarian_house.felicitous = true := rfl
theorem mandarin_house_felicitous : mandarin_house.felicitous = true := rfl
theorem english_house_felicitous : english_house.felicitous = true := rfl

-- Per-datum verification: §7 clause-type variation

-- Russian: ✓ polar Q, ✓ high-neg Q, ✓ wh-Q, ✓ neg-rhet wh-Q, ✓ imperative, ✓ exclamative
theorem russian_s'_polarQ_ok : russian_s'_polarQ.felicitous = true := rfl
theorem russian_s'_highNegQ_ok : russian_s'_highNegQ.felicitous = true := rfl
theorem russian_s'_whQ_ok : russian_s'_whQ.felicitous = true := rfl
theorem russian_s'_negRhetWhQ_ok : russian_s'_negRhetWhQ.felicitous = true := rfl
theorem russian_s'_imperative_ok : russian_s'_imperative.felicitous = true := rfl
theorem russian_s'_exclamative_ok : russian_s'_exclamative.felicitous = true := rfl

-- Hungarian: ✓ polar Q, ✓ high-neg Q, ✓ wh-Q, ✓ neg-rhet wh-Q, ✓ imperative, ✓ exclamative
theorem hungarian_s'_polarQ_ok : hungarian_s'_polarQ.felicitous = true := rfl
theorem hungarian_s'_highNegQ_ok : hungarian_s'_highNegQ.felicitous = true := rfl
theorem hungarian_s'_whQ_ok : hungarian_s'_whQ.felicitous = true := rfl
theorem hungarian_s'_negRhetWhQ_ok : hungarian_s'_negRhetWhQ.felicitous = true := rfl
theorem hungarian_s'_imperative_ok : hungarian_s'_imperative.felicitous = true := rfl
theorem hungarian_s'_exclamative_ok : hungarian_s'_exclamative.felicitous = true := rfl

-- Mandarin: ✓ polar Q, ✓ high-neg Q, ✓ wh-Q, ✓ neg-rhet wh-Q, ✓ imperative, ✗ exclamative
theorem mandarin_s'_polarQ_ok : mandarin_s'_polarQ.felicitous = true := rfl
theorem mandarin_s'_highNegQ_ok : mandarin_s'_highNegQ.felicitous = true := rfl
theorem mandarin_s'_whQ_ok : mandarin_s'_whQ.felicitous = true := rfl
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

/-- Canonical wh-Q as S' is allowed in Russian, Hungarian, and Mandarin.
The restriction on canonical info-seeking questions (§5.2) applies to the
LEFT argument S, not the prejacent S'. Only Italian blocks wh-Q as S', but
Italian blocks ALL non-declarative S'. -/
theorem whQ_s'_allowed_except_italian :
    russian_s'_whQ.felicitous = true ∧
    hungarian_s'_whQ.felicitous = true ∧
    mandarin_s'_whQ.felicitous = true ∧
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

theorem core_count : coreExamples.length = 5 := rfl
theorem clauseType_count : clauseTypeData.length = 23 := rfl
theorem total_count : allDiscourseOnlyData.length = 28 := rfl

end Phenomena.Focus.DiscourseOnly
