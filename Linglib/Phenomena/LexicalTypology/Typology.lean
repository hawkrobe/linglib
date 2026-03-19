import Linglib.Core.WALS.Features.F129A
import Linglib.Core.WALS.Features.F130A
import Linglib.Core.WALS.Features.F130B
import Linglib.Core.WALS.Features.F132A
import Linglib.Core.WALS.Features.F133A
import Linglib.Core.WALS.Features.F134A
import Linglib.Core.WALS.Features.F135A
import Linglib.Core.WALS.Features.F136A
import Linglib.Core.WALS.Features.F136B
import Linglib.Core.WALS.Features.F137A
import Linglib.Core.WALS.Features.F137B
import Linglib.Core.WALS.Features.F138A
import Linglib.Core.WALS.Features.F139A
import Linglib.Core.WALS.Features.F140A
import Linglib.Core.WALS.Features.F141A
import Linglib.Core.WALS.Features.F142A

/-!
# Lexical Typology (WALS Chapters 129--142)
@cite{dryer-haspelmath-2013}

Cross-linguistic data on lexical categorization from 16 WALS features spanning
body-part terminology (Ch 129--130), colour terminology (Ch 132--135),
pronominal root patterns (Ch 136--137), the Wanderwort "tea" (Ch 138),
sign language features (Ch 139--140), writing systems (Ch 141), and
para-linguistic click usage (Ch 142).

These chapters address a question that sits at the intersection of lexical
semantics and anthropological linguistics: *how do languages carve up
conceptual space into words?* The body-part and colour chapters are classic
case studies in the universals-vs-relativity debate. The pronoun chapters
probe whether certain phonological shapes are universally associated with
person reference. The tea chapter traces a single Wanderwort across the
globe, providing a window into contact history through lexical borrowing.

## Body-Part Terms (Ch 129--130)

- **F129A: Hand and Arm** -- whether a language uses the same or different
  words for 'hand' and 'arm'. Identical forms (228/617 = 37%) vs distinct
  forms (389/617 = 63%).
- **F130A: Finger and Hand** -- whether a language uses the same or different
  words for 'finger' and 'hand'. Identical forms are rare (72/593 = 12%).
- **F130B: Cultural Categories** -- among languages with finger=hand identity,
  the cultural type: hunter-gatherers (46/72), farmer-foragers (18/72),
  full-fledged farmers (8/72).

## Colour Terms (Ch 132--135)

- **F132A: Non-Derived Basic Colour Categories** -- how many non-derived
  basic colour categories a language has (3 to 6).
- **F133A: Basic Colour Categories** -- total number of basic colour
  categories including derived ones (3--4 to 11).
- **F134A: Green and Blue** -- whether a language distinguishes green from
  blue, merges them (grue), or has other patterns.
- **F135A: Red and Yellow** -- whether a language distinguishes red from
  yellow or merges them.

## Pronominal Roots (Ch 136--137)

- **F136A: M-T Pronouns** -- whether the language has an m/t pattern
  in 1SG/2SG pronouns (paradigmatic or non-paradigmatic).
- **F136B: M in 1SG** -- whether 1SG has an m-initial form.
- **F137A: N-M Pronouns** -- whether the language has an n/m pattern
  in 1SG/2SG pronouns.
- **F137B: M in 2SG** -- whether 2SG has an m-initial form.

## Tea (Ch 138)

- **F138A: Tea** -- whether the word for 'tea' derives from Sinitic *cha*,
  Min Nan *te*, or is an independent form.

## Sign Language Features (Ch 139--140)

- **F139A: Irregular Negatives** -- how many irregular negative signs
  a sign language has.
- **F140A: Question Particles** -- whether a sign language uses
  question particles.

## Writing Systems (Ch 141) and Clicks (Ch 142)

- **F141A: Writing Systems** -- type of writing system (only 6 languages
  in WALS sample; highly incomplete).
- **F142A: Para-Linguistic Usages of Clicks** -- whether clicks are used
  for logical meanings (negation/affirmation) or affective meanings
  (disgust/annoyance).
-/

namespace Phenomena.LexicalTypology.Typology

-- ============================================================================
-- Body-Part Term Relations (Ch 129--130)
-- ============================================================================

/-- Whether a language uses the same or different lexemes for 'hand' and 'arm'.
    Many languages worldwide use a single term covering both concepts
    (e.g., Japanese *te*, Russian *ruka*), while others lexically distinguish
    them (e.g., English *hand* vs *arm*). -/
inductive HandArmRelation where
  /-- The same word covers both 'hand' and 'arm'. -/
  | identical
  /-- Distinct words for 'hand' and 'arm'. -/
  | different
  deriving DecidableEq, BEq, Repr

/-- Whether a language uses the same or different lexemes for 'finger' and 'hand'.
    Identity of 'finger' and 'hand' is cross-linguistically rare (12% of sample)
    and correlates with subsistence type. -/
inductive FingerHandRelation where
  /-- The same word covers both 'finger' and 'hand'. -/
  | identical
  /-- Distinct words for 'finger' and 'hand'. -/
  | different
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Colour Term Systems (Ch 132--135)
-- ============================================================================

/-- Number of non-derived basic colour categories (F132A).
    Follows the Berlin & Kay hierarchy: languages range from 3 to 6
    non-derived basic colour terms. -/
inductive NonDerivedColourCount where
  | three       -- 3 non-derived categories
  | threeHalf   -- 3.5 (transitional)
  | four        -- 4 non-derived categories
  | fourHalf    -- 4.5 (transitional)
  | five        -- 5 non-derived categories
  | fiveHalf    -- 5.5 (transitional)
  | six         -- 6 non-derived categories
  deriving DecidableEq, BEq, Repr

/-- Total number of basic colour categories including derived ones (F133A).
    Ranges from 3--4 (minimal systems) to 11 (maximal, e.g., English, Russian). -/
inductive BasicColourCount where
  | v3to4       -- 3--4 basic colour categories
  | v4to5       -- 4.5--5.5 basic colour categories
  | v6to6h      -- 6--6.5 basic colour categories
  | v7to7h      -- 7--7.5 basic colour categories
  | v8to8h      -- 8--8.5 basic colour categories
  | v9to10      -- 9--10 basic colour categories
  | v11         -- 11 basic colour categories (maximal)
  deriving DecidableEq, BEq, Repr

/-- How a language treats the green-blue region of colour space (F134A).
    The classic grue/green-blue distinction. -/
inductive GreenBlueRelation where
  /-- Separate terms for green and blue. -/
  | distinct
  /-- A single 'grue' term covering both green and blue. -/
  | merged
  /-- A single term covering black, green, and blue. -/
  | blackGreenBlue
  /-- Black/blue merged, green separate. -/
  | blackBlueVsGreen
  /-- Yellow, green, blue all merged. -/
  | yellowGreenBlue
  /-- Yellow/green merged, blue separate. -/
  | yellowGreenVsBlue
  /-- No green or blue term at all. -/
  | noTerm
  deriving DecidableEq, BEq, Repr

/-- How a language treats the red-yellow region of colour space (F135A). -/
inductive RedYellowRelation where
  /-- Separate terms for red and yellow. -/
  | distinct
  /-- A single term covering both red and yellow. -/
  | merged
  /-- Yellow/green/blue merged, vs red. -/
  | yellowGreenBlueVsRed
  /-- Yellow/green merged, vs red. -/
  | yellowGreenVsRed
  /-- No red or yellow term at all. -/
  | noTerm
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Pronominal Root Patterns (Ch 136--137)
-- ============================================================================

/-- M-T pronoun pattern (F136A): whether 1SG has /m/ and 2SG has /t/,
    a widespread cross-linguistic pattern noted by many typologists. -/
inductive MTPronounPattern where
  /-- No M-T pattern in the pronoun paradigm. -/
  | absent
  /-- M-T pattern is paradigmatic (systematic across forms). -/
  | paradigmatic
  /-- M-T pattern is non-paradigmatic (sporadic). -/
  | nonParadigmatic
  deriving DecidableEq, BEq, Repr

/-- Whether 1SG has an m-initial or m-containing form (F136B). -/
inductive MIn1SG where
  | absent
  | present
  deriving DecidableEq, BEq, Repr

/-- N-M pronoun pattern (F137A): whether 1SG has /n/ and 2SG has /m/. -/
inductive NMPronounPattern where
  /-- No N-M pattern. -/
  | absent
  /-- N-M pattern is paradigmatic. -/
  | paradigmatic
  /-- N-M pattern is non-paradigmatic. -/
  | nonParadigmatic
  deriving DecidableEq, BEq, Repr

/-- Whether 2SG has an m-initial or m-containing form (F137B). -/
inductive MIn2SG where
  | absent
  | present
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Tea Wanderwort (Ch 138)
-- ============================================================================

/-- Origin of the word for 'tea' (F138A). One of the most striking
    Wanderworter: nearly all words for tea worldwide derive from either
    Sinitic *cha* (spread overland via the Silk Road) or Min Nan *te*
    (spread by sea via Dutch trade). -/
inductive TeaWordOrigin where
  /-- Derived from Sinitic *cha* (e.g., Hindi *chai*, Russian *chaj*,
      Turkish *cay*, Japanese *cha*, Arabic *shay*). -/
  | cha
  /-- Derived from Min Nan Chinese *te* (e.g., English *tea*, French *the*,
      German *Tee*, Spanish *te*, Finnish *tee*). -/
  | te
  /-- Independent form, not from either source. -/
  | other
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Sign Language Features (Ch 139--140)
-- ============================================================================

/-- Number of irregular negative signs in a sign language (F139A). -/
inductive IrregularNegativeCount where
  | none
  | one
  | some    -- 2 to 5
  | many    -- more than 5
  deriving DecidableEq, BEq, Repr

/-- Question particle usage in sign languages (F140A). -/
inductive SignQuestionParticle where
  | none
  | one
  | moreThanOne
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Writing Systems (Ch 141) and Clicks (Ch 142)
-- ============================================================================

/-- Type of writing system (F141A). Note: WALS sample is tiny (6 languages)
    and only covers non-alphabetic systems in the Americas and West Africa. -/
inductive WritingSystemType where
  | alphabetic
  | consonantal
  | alphasyllabic
  | syllabic
  | logographic
  | mixedLogographicSyllabic
  deriving DecidableEq, BEq, Repr

/-- Para-linguistic usage of clicks (F142A). Click sounds are used
    para-linguistically even in languages that lack phonemic clicks. -/
inductive ClickUsage where
  /-- Clicks used for logical meanings: negation ("tsk-tsk" = no),
      affirmation, or other propositional functions. -/
  | logical
  /-- Clicks used for affective/expressive meanings: annoyance,
      disapproval, sympathy, or attention-getting. -/
  | affective
  /-- Other usage or no para-linguistic clicks attested. -/
  | otherOrNone
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- WALS Converter Functions
-- ============================================================================

private def fromWALS129A : Core.WALS.F129A.HandAndArm → HandArmRelation
  | .identical => .identical
  | .different => .different

private def fromWALS130A : Core.WALS.F130A.FingerAndHand → FingerHandRelation
  | .identical => .identical
  | .different => .different

private def fromWALS132A : Core.WALS.F132A.NumberOfNonDerivedBasicColourCategories → NonDerivedColourCount
  | .v3  => .three
  | .v35 => .threeHalf
  | .v4  => .four
  | .v45 => .fourHalf
  | .v5  => .five
  | .v55 => .fiveHalf
  | .v6  => .six

private def fromWALS133A : Core.WALS.F133A.NumberOfBasicColourCategories → BasicColourCount
  | .v34   => .v3to4
  | .v4555 => .v4to5
  | .v665  => .v6to6h
  | .v775  => .v7to7h
  | .v885  => .v8to8h
  | .v910  => .v9to10
  | .v11   => .v11

private def fromWALS134A : Core.WALS.F134A.GreenAndBlue → GreenBlueRelation
  | .greenVsBlue       => .distinct
  | .greenBlue         => .merged
  | .blackGreenBlue    => .blackGreenBlue
  | .blackBlueVsGreen  => .blackBlueVsGreen
  | .yellowGreenBlue   => .yellowGreenBlue
  | .yellowGreenVsBlue => .yellowGreenVsBlue
  | .none              => .noTerm

private def fromWALS135A : Core.WALS.F135A.RedAndYellow → RedYellowRelation
  | .redVsYellow          => .distinct
  | .redYellow            => .merged
  | .yellowGreenBlueVsRed => .yellowGreenBlueVsRed
  | .yellowGreenVsRed     => .yellowGreenVsRed
  | .none                 => .noTerm

private def fromWALS136A : Core.WALS.F136A.MTPronouns → MTPronounPattern
  | .noMTPronouns              => .absent
  | .mTPronounsParadigmatic    => .paradigmatic
  | .mTPronounsNonParadigmatic => .nonParadigmatic

private def fromWALS136B : Core.WALS.F136B.MInFirstPersonSingular → MIn1SG
  | .noMInFirstPersonSingular => .absent
  | .mInFirstPersonSingular   => .present

private def fromWALS137A : Core.WALS.F137A.NMPronouns → NMPronounPattern
  | .noNMPronouns              => .absent
  | .nMPronounsParadigmatic    => .paradigmatic
  | .nMPronounsNonParadigmatic => .nonParadigmatic

private def fromWALS137B : Core.WALS.F137B.MInSecondPersonSingular → MIn2SG
  | .noMInSecondPersonSingular => .absent
  | .mInSecondPersonSingular   => .present

private def fromWALS138A : Core.WALS.F138A.Tea → TeaWordOrigin
  | .wordsDerivedFromSiniticCha       => .cha
  | .wordsDerivedFromMinNanChineseTe  => .te
  | .others                           => .other

private def fromWALS139A : Core.WALS.F139A.IrregularNegativesInSignLanguages → IrregularNegativeCount
  | .none => .none
  | .one  => .one
  | .some => .some
  | .many => .many

private def fromWALS140A : Core.WALS.F140A.QuestionParticlesInSignLanguages → SignQuestionParticle
  | .none        => .none
  | .one         => .one
  | .moreThanOne => .moreThanOne

private def fromWALS141A : Core.WALS.F141A.WritingSystems → WritingSystemType
  | .alphabetic                => .alphabetic
  | .consonantal               => .consonantal
  | .alphasyllabic             => .alphasyllabic
  | .syllabic                  => .syllabic
  | .logographic               => .logographic
  | .mixedLogographicSyllabic  => .mixedLogographicSyllabic

private def fromWALS142A : Core.WALS.F142A.ParaLinguisticUsagesOfClicks → ClickUsage
  | .logicalMeanings   => .logical
  | .affectiveMeanings => .affective
  | .otherOrNone       => .otherOrNone

-- ============================================================================
-- Language Profile Structure
-- ============================================================================

/-- A language's lexical typology profile across WALS Chapters 129--142.
    Fields are `Option` because coverage varies enormously across features:
    the body-part chapters cover ~600 languages, the pronoun/tea chapters
    cover ~230, the colour chapters ~120, and writing systems only 6. -/
structure LexicalProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Language family. -/
  family : String := ""
  -- Body-part terms (Ch 129--130)
  /-- F129A: Whether 'hand' and 'arm' are the same word. -/
  handArm : Option HandArmRelation := .none
  /-- F130A: Whether 'finger' and 'hand' are the same word. -/
  fingerHand : Option FingerHandRelation := .none
  -- Colour terms (Ch 132--135)
  /-- F132A: Number of non-derived basic colour categories. -/
  nonDerivedColours : Option NonDerivedColourCount := .none
  /-- F133A: Total number of basic colour categories. -/
  basicColours : Option BasicColourCount := .none
  /-- F134A: Green-blue distinction. -/
  greenBlue : Option GreenBlueRelation := .none
  /-- F135A: Red-yellow distinction. -/
  redYellow : Option RedYellowRelation := .none
  -- Pronominal roots (Ch 136--137)
  /-- F136A: M-T pronoun pattern. -/
  mtPronouns : Option MTPronounPattern := .none
  /-- F136B: M in 1SG. -/
  mIn1sg : Option MIn1SG := .none
  /-- F137A: N-M pronoun pattern. -/
  nmPronouns : Option NMPronounPattern := .none
  /-- F137B: M in 2SG. -/
  mIn2sg : Option MIn2SG := .none
  -- Tea (Ch 138)
  /-- F138A: Origin of the word for 'tea'. -/
  tea : Option TeaWordOrigin := .none
  -- Para-linguistic clicks (Ch 142)
  /-- F142A: Para-linguistic click usage. -/
  clicks : Option ClickUsage := .none
  deriving Repr

-- ============================================================================
-- Language Data
-- ============================================================================

/-- English (Indo-European, Germanic).
    Distinct hand/arm and finger/hand. 6 non-derived colour categories,
    11 total basic colours (the Berlin-Kay maximum). Green and blue are
    distinct; red and yellow are distinct. No M-T pronoun pattern but
    1SG "me/my" has /m/. Tea from Min Nan *te*. Clicks used affectively
    (tut-tut for disapproval). -/
def english : LexicalProfile :=
  { language := "English"
  , iso := "eng"
  , family := "Indo-European"
  , handArm := some .different
  , fingerHand := some .different
  , nonDerivedColours := some .six
  , basicColours := some .v11
  , greenBlue := some .distinct
  , redYellow := some .distinct
  , mtPronouns := some .absent
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent
  , tea := some .te
  , clicks := some .affective }

/-- French (Indo-European, Romance).
    Distinct hand/arm (*main* vs *bras*) and finger/hand (*doigt* vs *main*).
    6 non-derived, 11 total colour categories. Green (*vert*) and blue (*bleu*)
    distinct. M-T paradigmatic (*moi/toi*). Tea from *te* (*the*). -/
def french : LexicalProfile :=
  { language := "French"
  , iso := "fra"
  , family := "Indo-European"
  , handArm := some .different
  , fingerHand := some .different
  , nonDerivedColours := some .six
  , basicColours := some .v11
  , greenBlue := some .distinct
  , redYellow := some .distinct
  , mtPronouns := some .paradigmatic
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent
  , tea := some .te
  , clicks := .none }

/-- German (Indo-European, Germanic).
    Distinct hand/arm (*Hand* vs *Arm*) and finger/hand (*Finger* vs *Hand*).
    6 non-derived, 11 total colour categories. Green (*grun*) and blue (*blau*)
    distinct. M-T paradigmatic (*mich/dich*). Tea from *te* (*Tee*).
    Clicks used affectively. -/
def german : LexicalProfile :=
  { language := "German"
  , iso := "deu"
  , family := "Indo-European"
  , handArm := some .different
  , fingerHand := some .different
  , nonDerivedColours := some .six
  , basicColours := some .v11
  , greenBlue := some .distinct
  , redYellow := some .distinct
  , mtPronouns := some .paradigmatic
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent
  , tea := some .te
  , clicks := some .affective }

/-- Spanish (Indo-European, Romance).
    Distinct hand/arm (*mano* vs *brazo*) and finger/hand (*dedo* vs *mano*).
    6 non-derived, 11 total colour categories. Green (*verde*) and blue (*azul*)
    distinct. M-T paradigmatic (*me/te*). Tea from *te*. Clicks affective. -/
def spanish : LexicalProfile :=
  { language := "Spanish"
  , iso := "spa"
  , family := "Indo-European"
  , handArm := some .different
  , fingerHand := some .different
  , nonDerivedColours := some .six
  , basicColours := some .v11
  , greenBlue := some .distinct
  , redYellow := some .distinct
  , mtPronouns := some .paradigmatic
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent
  , tea := some .te
  , clicks := some .affective }

/-- Russian (Indo-European, Slavic).
    *Ruka* covers both 'hand' and 'arm' (identical). Distinct finger (*palec*)
    and hand (*ruka*). 6 non-derived colour categories; 11 total basic colours
    (Russian famously distinguishes *sinij* 'dark blue' from *goluboj* 'light
    blue', but WALS counts both). Green (*zelenyj*) and blue (*sinij*) distinct.
    M-T paradigmatic (*menja/tebja*). Tea from *cha* (*chaj*).
    Clicks affective. -/
def russian : LexicalProfile :=
  { language := "Russian"
  , iso := "rus"
  , family := "Indo-European"
  , handArm := some .identical
  , fingerHand := some .different
  , nonDerivedColours := some .six
  , basicColours := some .v11
  , greenBlue := some .distinct
  , redYellow := some .distinct
  , mtPronouns := some .paradigmatic
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent
  , tea := some .cha
  , clicks := some .affective }

/-- Japanese (Japonic).
    *Te* covers both 'hand' and 'arm' (identical). Distinct finger (*yubi*)
    and hand (*te*). 6 non-derived, 11 total colour categories. Green (*midori*)
    and blue (*ao*) are distinct in modern Japanese (though *ao* historically
    covered both). Red (*aka*) and yellow (*kiiro*) distinct. No M-T pattern.
    Tea from *cha*. Clicks affective. -/
def japanese : LexicalProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , family := "Japonic"
  , handArm := some .identical
  , fingerHand := some .different
  , nonDerivedColours := some .six
  , basicColours := some .v11
  , greenBlue := some .distinct
  , redYellow := some .distinct
  , mtPronouns := some .absent
  , mIn1sg := some .absent
  , nmPronouns := some .absent
  , mIn2sg := some .present
  , tea := some .cha
  , clicks := some .affective }

/-- Mandarin Chinese (Sino-Tibetan).
    Distinct hand/arm (*shou* vs *bei/gebo*) and finger/hand.
    6 non-derived colour categories; 8--8.5 total basic colours.
    Green (*lu*) and blue (*lan*) distinct. Red (*hong*) and yellow
    (*huang*) distinct. No M-T pattern; no /m/ in 1SG (*wo*).
    Tea from *cha*. -/
def mandarin : LexicalProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , family := "Sino-Tibetan"
  , handArm := some .different
  , fingerHand := some .different
  , nonDerivedColours := some .six
  , basicColours := some .v8to8h
  , greenBlue := some .distinct
  , redYellow := some .distinct
  , mtPronouns := some .absent
  , mIn1sg := some .absent
  , nmPronouns := some .absent
  , mIn2sg := some .absent
  , tea := some .cha
  , clicks := .none }

/-- Korean (Koreanic).
    Distinct hand/arm and finger/hand. 6 non-derived, 11 total colour
    categories. Green and blue distinct. No M-T pattern.
    Tea from *cha*. Clicks affective. -/
def korean : LexicalProfile :=
  { language := "Korean"
  , iso := "kor"
  , family := "Koreanic"
  , handArm := some .different
  , fingerHand := some .different
  , nonDerivedColours := some .six
  , basicColours := some .v11
  , greenBlue := some .distinct
  , redYellow := some .distinct
  , mtPronouns := some .absent
  , mIn1sg := some .absent
  , nmPronouns := some .absent
  , mIn2sg := some .absent
  , tea := some .cha
  , clicks := some .affective }

/-- Turkish (Turkic).
    Distinct hand/arm (*el* vs *kol*) and finger/hand (*parmak* vs *el*).
    M-T paradigmatic (*ben/sen* with older forms showing m/t).
    Tea from *cha* (*cay*). Clicks used for logical meanings
    (tongue-click for negation). -/
def turkish : LexicalProfile :=
  { language := "Turkish"
  , iso := "tur"
  , family := "Turkic"
  , handArm := some .different
  , fingerHand := some .different
  , nonDerivedColours := .none
  , basicColours := .none
  , greenBlue := .none
  , redYellow := .none
  , mtPronouns := some .paradigmatic
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent
  , tea := some .cha
  , clicks := some .logical }

/-- Finnish (Uralic).
    Distinct hand/arm (*kasi* vs *kasivarsi*) and finger/hand
    (*sormi* vs *kasi*). M-T paradigmatic (*mina/sina*).
    Tea from *te* (*tee*). Clicks affective. -/
def finnish : LexicalProfile :=
  { language := "Finnish"
  , iso := "fin"
  , family := "Uralic"
  , handArm := some .different
  , fingerHand := some .different
  , nonDerivedColours := .none
  , basicColours := .none
  , greenBlue := .none
  , redYellow := .none
  , mtPronouns := some .paradigmatic
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent
  , tea := some .te
  , clicks := some .affective }

/-- Hungarian (Uralic).
    Distinct hand/arm (*kez* vs *kar*) and finger/hand (*ujj* vs *kez*).
    M-T paradigmatic (like Finnish). Tea from *te*.
    Clicks affective. -/
def hungarian : LexicalProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , family := "Uralic"
  , handArm := some .different
  , fingerHand := some .different
  , nonDerivedColours := .none
  , basicColours := .none
  , greenBlue := .none
  , redYellow := .none
  , mtPronouns := some .paradigmatic
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent
  , tea := some .te
  , clicks := some .affective }

/-- Hindi (Indo-European, Indo-Aryan).
    M-T paradigmatic (*main/tum* show m/t). 1SG has /m/ (*main*).
    Tea from *cha* (*chai*). Clicks used for logical meanings
    (tongue-click for negation in many South Asian languages). -/
def hindi : LexicalProfile :=
  { language := "Hindi"
  , iso := "hin"
  , family := "Indo-European"
  , handArm := .none
  , fingerHand := .none
  , nonDerivedColours := .none
  , basicColours := .none
  , greenBlue := .none
  , redYellow := .none
  , mtPronouns := some .paradigmatic
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent
  , tea := some .cha
  , clicks := some .logical }

/-- Arabic (Egyptian) (Afro-Asiatic, Semitic).
    No M-T pattern; no /m/ in 1SG (*ana*). Tea from *cha* (*shay*). -/
def arabic : LexicalProfile :=
  { language := "Arabic (Egyptian)"
  , iso := "arz"
  , family := "Afro-Asiatic"
  , handArm := .none
  , fingerHand := .none
  , nonDerivedColours := .none
  , basicColours := .none
  , greenBlue := .none
  , redYellow := .none
  , mtPronouns := some .absent
  , mIn1sg := some .absent
  , nmPronouns := some .absent
  , mIn2sg := some .absent
  , tea := some .cha
  , clicks := .none }

/-- Swahili (Niger-Congo, Bantu).
    *Mkono* covers both 'hand' and 'arm' (identical). Distinct finger/hand.
    No M-T pattern; 1SG has /m/ (*mimi*). Tea from *cha*. Clicks affective. -/
def swahili : LexicalProfile :=
  { language := "Swahili"
  , iso := "swh"
  , family := "Niger-Congo"
  , handArm := some .identical
  , fingerHand := some .different
  , nonDerivedColours := .none
  , basicColours := .none
  , greenBlue := .none
  , redYellow := .none
  , mtPronouns := some .absent
  , mIn1sg := some .present
  , nmPronouns := some .absent
  , mIn2sg := some .absent
  , tea := some .cha
  , clicks := some .affective }

/-- Tagalog (Austronesian).
    Distinct hand/arm and finger/hand. No M-T pattern.
    Tea from *cha*. Clicks: other/none. -/
def tagalog : LexicalProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , family := "Austronesian"
  , handArm := some .different
  , fingerHand := some .different
  , nonDerivedColours := .none
  , basicColours := .none
  , greenBlue := .none
  , redYellow := .none
  , mtPronouns := some .absent
  , mIn1sg := some .absent
  , nmPronouns := some .absent
  , mIn2sg := some .present
  , tea := some .cha
  , clicks := some .otherOrNone }

/-- All language profiles in the sample. -/
def allLanguages : List LexicalProfile :=
  [ english, french, german, spanish, russian, japanese, mandarin, korean
  , turkish, finnish, hungarian, hindi, arabic, swahili, tagalog ]

-- ============================================================================
-- WALS Generated Data Abbreviations
-- ============================================================================

private abbrev ch129 := Core.WALS.F129A.allData
private abbrev ch130 := Core.WALS.F130A.allData
private abbrev ch130b := Core.WALS.F130B.allData
private abbrev ch132 := Core.WALS.F132A.allData
private abbrev ch133 := Core.WALS.F133A.allData
private abbrev ch134 := Core.WALS.F134A.allData
private abbrev ch135 := Core.WALS.F135A.allData
private abbrev ch136a := Core.WALS.F136A.allData
private abbrev ch136b := Core.WALS.F136B.allData
private abbrev ch137a := Core.WALS.F137A.allData
private abbrev ch137b := Core.WALS.F137B.allData
private abbrev ch138 := Core.WALS.F138A.allData
private abbrev ch139 := Core.WALS.F139A.allData
private abbrev ch140 := Core.WALS.F140A.allData
private abbrev ch141 := Core.WALS.F141A.allData
private abbrev ch142 := Core.WALS.F142A.allData

-- ============================================================================
-- Dataset Size Verification
-- ============================================================================

theorem wals_f129a_total : ch129.length = 617 := by native_decide
theorem wals_f130a_total : ch130.length = 593 := by native_decide
theorem wals_f130b_total : ch130b.length = 72 := by native_decide
theorem wals_f132a_total : ch132.length = 119 := by native_decide
theorem wals_f133a_total : ch133.length = 119 := by native_decide
theorem wals_f134a_total : ch134.length = 120 := by native_decide
theorem wals_f135a_total : ch135.length = 120 := by native_decide
theorem wals_f136a_total : ch136a.length = 230 := by native_decide
theorem wals_f136b_total : ch136b.length = 230 := by native_decide
theorem wals_f137a_total : ch137a.length = 230 := by native_decide
theorem wals_f137b_total : ch137b.length = 230 := by native_decide
theorem wals_f138a_total : ch138.length = 230 := by native_decide
theorem wals_f139a_total : ch139.length = 35 := by native_decide
theorem wals_f140a_total : ch140.length = 38 := by native_decide
theorem wals_f141a_total : ch141.length = 6 := by native_decide
theorem wals_f142a_total : ch142.length = 143 := by native_decide

-- ============================================================================
-- WALS Distribution Count Verification
-- ============================================================================

-- F129A: Hand and Arm
theorem wals_f129a_identical :
    (ch129.filter (·.value == .identical)).length = 228 := by native_decide
theorem wals_f129a_different :
    (ch129.filter (·.value == .different)).length = 389 := by native_decide

-- F130A: Finger and Hand
theorem wals_f130a_identical :
    (ch130.filter (·.value == .identical)).length = 72 := by native_decide
theorem wals_f130a_different :
    (ch130.filter (·.value == .different)).length = 521 := by native_decide

-- F130B: Cultural Categories
theorem wals_f130b_hunters :
    (ch130b.filter (·.value == .hunterGatherers)).length = 46 := by native_decide
theorem wals_f130b_farmerForagers :
    (ch130b.filter (·.value == .farmerForagers)).length = 18 := by native_decide
theorem wals_f130b_farmers :
    (ch130b.filter (·.value == .fullFledgedFarmers)).length = 8 := by native_decide

-- F134A: Green and Blue
theorem wals_f134a_distinct :
    (ch134.filter (·.value == .greenVsBlue)).length = 30 := by native_decide
theorem wals_f134a_merged :
    (ch134.filter (·.value == .greenBlue)).length = 68 := by native_decide

-- F135A: Red and Yellow
theorem wals_f135a_distinct :
    (ch135.filter (·.value == .redVsYellow)).length = 98 := by native_decide
theorem wals_f135a_merged :
    (ch135.filter (·.value == .redYellow)).length = 15 := by native_decide

-- F136A: M-T Pronouns
theorem wals_f136a_absent :
    (ch136a.filter (·.value == .noMTPronouns)).length = 200 := by native_decide
theorem wals_f136a_paradigmatic :
    (ch136a.filter (·.value == .mTPronounsParadigmatic)).length = 27 := by native_decide

-- F138A: Tea
theorem wals_f138a_cha :
    (ch138.filter (·.value == .wordsDerivedFromSiniticCha)).length = 110 := by native_decide
theorem wals_f138a_te :
    (ch138.filter (·.value == .wordsDerivedFromMinNanChineseTe)).length = 84 := by native_decide
theorem wals_f138a_other :
    (ch138.filter (·.value == .others)).length = 36 := by native_decide

-- F142A: Para-Linguistic Clicks
theorem wals_f142a_logical :
    (ch142.filter (·.value == .logicalMeanings)).length = 47 := by native_decide
theorem wals_f142a_affective :
    (ch142.filter (·.value == .affectiveMeanings)).length = 71 := by native_decide
theorem wals_f142a_other :
    (ch142.filter (·.value == .otherOrNone)).length = 25 := by native_decide

-- ============================================================================
-- Per-Language Profile Verification
-- ============================================================================

theorem sample_size : allLanguages.length = 15 := by native_decide

-- ============================================================================
-- WALS Grounding: F129A (Hand and Arm)
-- ============================================================================

theorem english_f129a :
    (Core.WALS.F129A.lookup "eng").map (fromWALS129A ·.value) =
    english.handArm := by native_decide
theorem french_f129a :
    (Core.WALS.F129A.lookup "fre").map (fromWALS129A ·.value) =
    french.handArm := by native_decide
theorem german_f129a :
    (Core.WALS.F129A.lookup "ger").map (fromWALS129A ·.value) =
    german.handArm := by native_decide
theorem spanish_f129a :
    (Core.WALS.F129A.lookup "spa").map (fromWALS129A ·.value) =
    spanish.handArm := by native_decide
theorem russian_f129a :
    (Core.WALS.F129A.lookup "rus").map (fromWALS129A ·.value) =
    russian.handArm := by native_decide
theorem japanese_f129a :
    (Core.WALS.F129A.lookup "jpn").map (fromWALS129A ·.value) =
    japanese.handArm := by native_decide
theorem mandarin_f129a :
    (Core.WALS.F129A.lookup "mnd").map (fromWALS129A ·.value) =
    mandarin.handArm := by native_decide
theorem korean_f129a :
    (Core.WALS.F129A.lookup "kor").map (fromWALS129A ·.value) =
    korean.handArm := by native_decide
theorem turkish_f129a :
    (Core.WALS.F129A.lookup "tur").map (fromWALS129A ·.value) =
    turkish.handArm := by native_decide
theorem finnish_f129a :
    (Core.WALS.F129A.lookup "fin").map (fromWALS129A ·.value) =
    finnish.handArm := by native_decide
theorem hungarian_f129a :
    (Core.WALS.F129A.lookup "hun").map (fromWALS129A ·.value) =
    hungarian.handArm := by native_decide
theorem swahili_f129a :
    (Core.WALS.F129A.lookup "swa").map (fromWALS129A ·.value) =
    swahili.handArm := by native_decide
theorem tagalog_f129a :
    (Core.WALS.F129A.lookup "tag").map (fromWALS129A ·.value) =
    tagalog.handArm := by native_decide

-- ============================================================================
-- WALS Grounding: F130A (Finger and Hand)
-- ============================================================================

theorem english_f130a :
    (Core.WALS.F130A.lookup "eng").map (fromWALS130A ·.value) =
    english.fingerHand := by native_decide
theorem french_f130a :
    (Core.WALS.F130A.lookup "fre").map (fromWALS130A ·.value) =
    french.fingerHand := by native_decide
theorem german_f130a :
    (Core.WALS.F130A.lookup "ger").map (fromWALS130A ·.value) =
    german.fingerHand := by native_decide
theorem spanish_f130a :
    (Core.WALS.F130A.lookup "spa").map (fromWALS130A ·.value) =
    spanish.fingerHand := by native_decide
theorem russian_f130a :
    (Core.WALS.F130A.lookup "rus").map (fromWALS130A ·.value) =
    russian.fingerHand := by native_decide
theorem japanese_f130a :
    (Core.WALS.F130A.lookup "jpn").map (fromWALS130A ·.value) =
    japanese.fingerHand := by native_decide
theorem mandarin_f130a :
    (Core.WALS.F130A.lookup "mnd").map (fromWALS130A ·.value) =
    mandarin.fingerHand := by native_decide
theorem korean_f130a :
    (Core.WALS.F130A.lookup "kor").map (fromWALS130A ·.value) =
    korean.fingerHand := by native_decide
theorem turkish_f130a :
    (Core.WALS.F130A.lookup "tur").map (fromWALS130A ·.value) =
    turkish.fingerHand := by native_decide
theorem finnish_f130a :
    (Core.WALS.F130A.lookup "fin").map (fromWALS130A ·.value) =
    finnish.fingerHand := by native_decide
theorem hungarian_f130a :
    (Core.WALS.F130A.lookup "hun").map (fromWALS130A ·.value) =
    hungarian.fingerHand := by native_decide
theorem swahili_f130a :
    (Core.WALS.F130A.lookup "swa").map (fromWALS130A ·.value) =
    swahili.fingerHand := by native_decide
theorem tagalog_f130a :
    (Core.WALS.F130A.lookup "tag").map (fromWALS130A ·.value) =
    tagalog.fingerHand := by native_decide

-- ============================================================================
-- WALS Grounding: F132A (Non-Derived Basic Colour Categories)
-- Only languages present in the F132A sample.
-- ============================================================================

theorem english_f132a :
    (Core.WALS.F132A.lookup "eng").map (fromWALS132A ·.value) =
    english.nonDerivedColours := by native_decide
theorem french_f132a :
    (Core.WALS.F132A.lookup "fre").map (fromWALS132A ·.value) =
    french.nonDerivedColours := by native_decide
theorem german_f132a :
    (Core.WALS.F132A.lookup "ger").map (fromWALS132A ·.value) =
    german.nonDerivedColours := by native_decide
theorem spanish_f132a :
    (Core.WALS.F132A.lookup "spa").map (fromWALS132A ·.value) =
    spanish.nonDerivedColours := by native_decide
theorem russian_f132a :
    (Core.WALS.F132A.lookup "rus").map (fromWALS132A ·.value) =
    russian.nonDerivedColours := by native_decide
theorem japanese_f132a :
    (Core.WALS.F132A.lookup "jpn").map (fromWALS132A ·.value) =
    japanese.nonDerivedColours := by native_decide
theorem mandarin_f132a :
    (Core.WALS.F132A.lookup "mnd").map (fromWALS132A ·.value) =
    mandarin.nonDerivedColours := by native_decide
theorem korean_f132a :
    (Core.WALS.F132A.lookup "kor").map (fromWALS132A ·.value) =
    korean.nonDerivedColours := by native_decide

-- ============================================================================
-- WALS Grounding: F133A (Basic Colour Categories)
-- ============================================================================

theorem english_f133a :
    (Core.WALS.F133A.lookup "eng").map (fromWALS133A ·.value) =
    english.basicColours := by native_decide
theorem french_f133a :
    (Core.WALS.F133A.lookup "fre").map (fromWALS133A ·.value) =
    french.basicColours := by native_decide
theorem german_f133a :
    (Core.WALS.F133A.lookup "ger").map (fromWALS133A ·.value) =
    german.basicColours := by native_decide
theorem spanish_f133a :
    (Core.WALS.F133A.lookup "spa").map (fromWALS133A ·.value) =
    spanish.basicColours := by native_decide
theorem russian_f133a :
    (Core.WALS.F133A.lookup "rus").map (fromWALS133A ·.value) =
    russian.basicColours := by native_decide
theorem japanese_f133a :
    (Core.WALS.F133A.lookup "jpn").map (fromWALS133A ·.value) =
    japanese.basicColours := by native_decide
theorem mandarin_f133a :
    (Core.WALS.F133A.lookup "mnd").map (fromWALS133A ·.value) =
    mandarin.basicColours := by native_decide
theorem korean_f133a :
    (Core.WALS.F133A.lookup "kor").map (fromWALS133A ·.value) =
    korean.basicColours := by native_decide

-- ============================================================================
-- WALS Grounding: F134A (Green and Blue)
-- ============================================================================

theorem english_f134a :
    (Core.WALS.F134A.lookup "eng").map (fromWALS134A ·.value) =
    english.greenBlue := by native_decide
theorem french_f134a :
    (Core.WALS.F134A.lookup "fre").map (fromWALS134A ·.value) =
    french.greenBlue := by native_decide
theorem german_f134a :
    (Core.WALS.F134A.lookup "ger").map (fromWALS134A ·.value) =
    german.greenBlue := by native_decide
theorem spanish_f134a :
    (Core.WALS.F134A.lookup "spa").map (fromWALS134A ·.value) =
    spanish.greenBlue := by native_decide
theorem russian_f134a :
    (Core.WALS.F134A.lookup "rus").map (fromWALS134A ·.value) =
    russian.greenBlue := by native_decide
theorem japanese_f134a :
    (Core.WALS.F134A.lookup "jpn").map (fromWALS134A ·.value) =
    japanese.greenBlue := by native_decide
theorem mandarin_f134a :
    (Core.WALS.F134A.lookup "mnd").map (fromWALS134A ·.value) =
    mandarin.greenBlue := by native_decide
theorem korean_f134a :
    (Core.WALS.F134A.lookup "kor").map (fromWALS134A ·.value) =
    korean.greenBlue := by native_decide

-- ============================================================================
-- WALS Grounding: F135A (Red and Yellow)
-- ============================================================================

theorem english_f135a :
    (Core.WALS.F135A.lookup "eng").map (fromWALS135A ·.value) =
    english.redYellow := by native_decide
theorem french_f135a :
    (Core.WALS.F135A.lookup "fre").map (fromWALS135A ·.value) =
    french.redYellow := by native_decide
theorem german_f135a :
    (Core.WALS.F135A.lookup "ger").map (fromWALS135A ·.value) =
    german.redYellow := by native_decide
theorem spanish_f135a :
    (Core.WALS.F135A.lookup "spa").map (fromWALS135A ·.value) =
    spanish.redYellow := by native_decide
theorem russian_f135a :
    (Core.WALS.F135A.lookup "rus").map (fromWALS135A ·.value) =
    russian.redYellow := by native_decide
theorem japanese_f135a :
    (Core.WALS.F135A.lookup "jpn").map (fromWALS135A ·.value) =
    japanese.redYellow := by native_decide
theorem mandarin_f135a :
    (Core.WALS.F135A.lookup "mnd").map (fromWALS135A ·.value) =
    mandarin.redYellow := by native_decide
theorem korean_f135a :
    (Core.WALS.F135A.lookup "kor").map (fromWALS135A ·.value) =
    korean.redYellow := by native_decide

-- ============================================================================
-- WALS Grounding: F136A (M-T Pronouns)
-- ============================================================================

theorem english_f136a :
    (Core.WALS.F136A.lookup "eng").map (fromWALS136A ·.value) =
    english.mtPronouns := by native_decide
theorem french_f136a :
    (Core.WALS.F136A.lookup "fre").map (fromWALS136A ·.value) =
    french.mtPronouns := by native_decide
theorem german_f136a :
    (Core.WALS.F136A.lookup "ger").map (fromWALS136A ·.value) =
    german.mtPronouns := by native_decide
theorem spanish_f136a :
    (Core.WALS.F136A.lookup "spa").map (fromWALS136A ·.value) =
    spanish.mtPronouns := by native_decide
theorem russian_f136a :
    (Core.WALS.F136A.lookup "rus").map (fromWALS136A ·.value) =
    russian.mtPronouns := by native_decide
theorem japanese_f136a :
    (Core.WALS.F136A.lookup "jpn").map (fromWALS136A ·.value) =
    japanese.mtPronouns := by native_decide
theorem mandarin_f136a :
    (Core.WALS.F136A.lookup "mnd").map (fromWALS136A ·.value) =
    mandarin.mtPronouns := by native_decide
theorem korean_f136a :
    (Core.WALS.F136A.lookup "kor").map (fromWALS136A ·.value) =
    korean.mtPronouns := by native_decide
theorem turkish_f136a :
    (Core.WALS.F136A.lookup "tur").map (fromWALS136A ·.value) =
    turkish.mtPronouns := by native_decide
theorem finnish_f136a :
    (Core.WALS.F136A.lookup "fin").map (fromWALS136A ·.value) =
    finnish.mtPronouns := by native_decide
theorem hungarian_f136a :
    (Core.WALS.F136A.lookup "hun").map (fromWALS136A ·.value) =
    hungarian.mtPronouns := by native_decide
theorem hindi_f136a :
    (Core.WALS.F136A.lookup "hin").map (fromWALS136A ·.value) =
    hindi.mtPronouns := by native_decide
theorem arabic_f136a :
    (Core.WALS.F136A.lookup "aeg").map (fromWALS136A ·.value) =
    arabic.mtPronouns := by native_decide
theorem swahili_f136a :
    (Core.WALS.F136A.lookup "swa").map (fromWALS136A ·.value) =
    swahili.mtPronouns := by native_decide
theorem tagalog_f136a :
    (Core.WALS.F136A.lookup "tag").map (fromWALS136A ·.value) =
    tagalog.mtPronouns := by native_decide

-- ============================================================================
-- WALS Grounding: F136B (M in 1SG)
-- ============================================================================

theorem english_f136b :
    (Core.WALS.F136B.lookup "eng").map (fromWALS136B ·.value) =
    english.mIn1sg := by native_decide
theorem french_f136b :
    (Core.WALS.F136B.lookup "fre").map (fromWALS136B ·.value) =
    french.mIn1sg := by native_decide
theorem german_f136b :
    (Core.WALS.F136B.lookup "ger").map (fromWALS136B ·.value) =
    german.mIn1sg := by native_decide
theorem spanish_f136b :
    (Core.WALS.F136B.lookup "spa").map (fromWALS136B ·.value) =
    spanish.mIn1sg := by native_decide
theorem russian_f136b :
    (Core.WALS.F136B.lookup "rus").map (fromWALS136B ·.value) =
    russian.mIn1sg := by native_decide
theorem japanese_f136b :
    (Core.WALS.F136B.lookup "jpn").map (fromWALS136B ·.value) =
    japanese.mIn1sg := by native_decide
theorem mandarin_f136b :
    (Core.WALS.F136B.lookup "mnd").map (fromWALS136B ·.value) =
    mandarin.mIn1sg := by native_decide
theorem korean_f136b :
    (Core.WALS.F136B.lookup "kor").map (fromWALS136B ·.value) =
    korean.mIn1sg := by native_decide
theorem turkish_f136b :
    (Core.WALS.F136B.lookup "tur").map (fromWALS136B ·.value) =
    turkish.mIn1sg := by native_decide
theorem finnish_f136b :
    (Core.WALS.F136B.lookup "fin").map (fromWALS136B ·.value) =
    finnish.mIn1sg := by native_decide
theorem hungarian_f136b :
    (Core.WALS.F136B.lookup "hun").map (fromWALS136B ·.value) =
    hungarian.mIn1sg := by native_decide
theorem hindi_f136b :
    (Core.WALS.F136B.lookup "hin").map (fromWALS136B ·.value) =
    hindi.mIn1sg := by native_decide
theorem arabic_f136b :
    (Core.WALS.F136B.lookup "aeg").map (fromWALS136B ·.value) =
    arabic.mIn1sg := by native_decide
theorem swahili_f136b :
    (Core.WALS.F136B.lookup "swa").map (fromWALS136B ·.value) =
    swahili.mIn1sg := by native_decide
theorem tagalog_f136b :
    (Core.WALS.F136B.lookup "tag").map (fromWALS136B ·.value) =
    tagalog.mIn1sg := by native_decide

-- ============================================================================
-- WALS Grounding: F137A (N-M Pronouns)
-- ============================================================================

theorem english_f137a :
    (Core.WALS.F137A.lookup "eng").map (fromWALS137A ·.value) =
    english.nmPronouns := by native_decide
theorem french_f137a :
    (Core.WALS.F137A.lookup "fre").map (fromWALS137A ·.value) =
    french.nmPronouns := by native_decide
theorem german_f137a :
    (Core.WALS.F137A.lookup "ger").map (fromWALS137A ·.value) =
    german.nmPronouns := by native_decide
theorem spanish_f137a :
    (Core.WALS.F137A.lookup "spa").map (fromWALS137A ·.value) =
    spanish.nmPronouns := by native_decide
theorem russian_f137a :
    (Core.WALS.F137A.lookup "rus").map (fromWALS137A ·.value) =
    russian.nmPronouns := by native_decide
theorem japanese_f137a :
    (Core.WALS.F137A.lookup "jpn").map (fromWALS137A ·.value) =
    japanese.nmPronouns := by native_decide
theorem mandarin_f137a :
    (Core.WALS.F137A.lookup "mnd").map (fromWALS137A ·.value) =
    mandarin.nmPronouns := by native_decide
theorem korean_f137a :
    (Core.WALS.F137A.lookup "kor").map (fromWALS137A ·.value) =
    korean.nmPronouns := by native_decide
theorem turkish_f137a :
    (Core.WALS.F137A.lookup "tur").map (fromWALS137A ·.value) =
    turkish.nmPronouns := by native_decide
theorem finnish_f137a :
    (Core.WALS.F137A.lookup "fin").map (fromWALS137A ·.value) =
    finnish.nmPronouns := by native_decide
theorem hungarian_f137a :
    (Core.WALS.F137A.lookup "hun").map (fromWALS137A ·.value) =
    hungarian.nmPronouns := by native_decide
theorem hindi_f137a :
    (Core.WALS.F137A.lookup "hin").map (fromWALS137A ·.value) =
    hindi.nmPronouns := by native_decide
theorem arabic_f137a :
    (Core.WALS.F137A.lookup "aeg").map (fromWALS137A ·.value) =
    arabic.nmPronouns := by native_decide
theorem swahili_f137a :
    (Core.WALS.F137A.lookup "swa").map (fromWALS137A ·.value) =
    swahili.nmPronouns := by native_decide
theorem tagalog_f137a :
    (Core.WALS.F137A.lookup "tag").map (fromWALS137A ·.value) =
    tagalog.nmPronouns := by native_decide

-- ============================================================================
-- WALS Grounding: F137B (M in 2SG)
-- ============================================================================

theorem english_f137b :
    (Core.WALS.F137B.lookup "eng").map (fromWALS137B ·.value) =
    english.mIn2sg := by native_decide
theorem french_f137b :
    (Core.WALS.F137B.lookup "fre").map (fromWALS137B ·.value) =
    french.mIn2sg := by native_decide
theorem german_f137b :
    (Core.WALS.F137B.lookup "ger").map (fromWALS137B ·.value) =
    german.mIn2sg := by native_decide
theorem spanish_f137b :
    (Core.WALS.F137B.lookup "spa").map (fromWALS137B ·.value) =
    spanish.mIn2sg := by native_decide
theorem russian_f137b :
    (Core.WALS.F137B.lookup "rus").map (fromWALS137B ·.value) =
    russian.mIn2sg := by native_decide
theorem japanese_f137b :
    (Core.WALS.F137B.lookup "jpn").map (fromWALS137B ·.value) =
    japanese.mIn2sg := by native_decide
theorem mandarin_f137b :
    (Core.WALS.F137B.lookup "mnd").map (fromWALS137B ·.value) =
    mandarin.mIn2sg := by native_decide
theorem korean_f137b :
    (Core.WALS.F137B.lookup "kor").map (fromWALS137B ·.value) =
    korean.mIn2sg := by native_decide
theorem turkish_f137b :
    (Core.WALS.F137B.lookup "tur").map (fromWALS137B ·.value) =
    turkish.mIn2sg := by native_decide
theorem finnish_f137b :
    (Core.WALS.F137B.lookup "fin").map (fromWALS137B ·.value) =
    finnish.mIn2sg := by native_decide
theorem hungarian_f137b :
    (Core.WALS.F137B.lookup "hun").map (fromWALS137B ·.value) =
    hungarian.mIn2sg := by native_decide
theorem hindi_f137b :
    (Core.WALS.F137B.lookup "hin").map (fromWALS137B ·.value) =
    hindi.mIn2sg := by native_decide
theorem arabic_f137b :
    (Core.WALS.F137B.lookup "aeg").map (fromWALS137B ·.value) =
    arabic.mIn2sg := by native_decide
theorem swahili_f137b :
    (Core.WALS.F137B.lookup "swa").map (fromWALS137B ·.value) =
    swahili.mIn2sg := by native_decide
theorem tagalog_f137b :
    (Core.WALS.F137B.lookup "tag").map (fromWALS137B ·.value) =
    tagalog.mIn2sg := by native_decide

-- ============================================================================
-- WALS Grounding: F138A (Tea)
-- ============================================================================

theorem english_f138a :
    (Core.WALS.F138A.lookup "eng").map (fromWALS138A ·.value) =
    english.tea := by native_decide
theorem french_f138a :
    (Core.WALS.F138A.lookup "fre").map (fromWALS138A ·.value) =
    french.tea := by native_decide
theorem german_f138a :
    (Core.WALS.F138A.lookup "ger").map (fromWALS138A ·.value) =
    german.tea := by native_decide
theorem spanish_f138a :
    (Core.WALS.F138A.lookup "spa").map (fromWALS138A ·.value) =
    spanish.tea := by native_decide
theorem russian_f138a :
    (Core.WALS.F138A.lookup "rus").map (fromWALS138A ·.value) =
    russian.tea := by native_decide
theorem japanese_f138a :
    (Core.WALS.F138A.lookup "jpn").map (fromWALS138A ·.value) =
    japanese.tea := by native_decide
theorem mandarin_f138a :
    (Core.WALS.F138A.lookup "mnd").map (fromWALS138A ·.value) =
    mandarin.tea := by native_decide
theorem korean_f138a :
    (Core.WALS.F138A.lookup "kor").map (fromWALS138A ·.value) =
    korean.tea := by native_decide
theorem turkish_f138a :
    (Core.WALS.F138A.lookup "tur").map (fromWALS138A ·.value) =
    turkish.tea := by native_decide
theorem finnish_f138a :
    (Core.WALS.F138A.lookup "fin").map (fromWALS138A ·.value) =
    finnish.tea := by native_decide
theorem hungarian_f138a :
    (Core.WALS.F138A.lookup "hun").map (fromWALS138A ·.value) =
    hungarian.tea := by native_decide
theorem hindi_f138a :
    (Core.WALS.F138A.lookup "hin").map (fromWALS138A ·.value) =
    hindi.tea := by native_decide
theorem arabic_f138a :
    (Core.WALS.F138A.lookup "aeg").map (fromWALS138A ·.value) =
    arabic.tea := by native_decide
theorem swahili_f138a :
    (Core.WALS.F138A.lookup "swa").map (fromWALS138A ·.value) =
    swahili.tea := by native_decide
theorem tagalog_f138a :
    (Core.WALS.F138A.lookup "tag").map (fromWALS138A ·.value) =
    tagalog.tea := by native_decide

-- ============================================================================
-- WALS Grounding: F142A (Para-Linguistic Clicks)
-- Only languages present in the F142A sample.
-- ============================================================================

theorem english_f142a :
    (Core.WALS.F142A.lookup "eng").map (fromWALS142A ·.value) =
    english.clicks := by native_decide
theorem german_f142a :
    (Core.WALS.F142A.lookup "ger").map (fromWALS142A ·.value) =
    german.clicks := by native_decide
theorem spanish_f142a :
    (Core.WALS.F142A.lookup "spa").map (fromWALS142A ·.value) =
    spanish.clicks := by native_decide
theorem russian_f142a :
    (Core.WALS.F142A.lookup "rus").map (fromWALS142A ·.value) =
    russian.clicks := by native_decide
theorem japanese_f142a :
    (Core.WALS.F142A.lookup "jpn").map (fromWALS142A ·.value) =
    japanese.clicks := by native_decide
theorem korean_f142a :
    (Core.WALS.F142A.lookup "kor").map (fromWALS142A ·.value) =
    korean.clicks := by native_decide
theorem turkish_f142a :
    (Core.WALS.F142A.lookup "tur").map (fromWALS142A ·.value) =
    turkish.clicks := by native_decide
theorem finnish_f142a :
    (Core.WALS.F142A.lookup "fin").map (fromWALS142A ·.value) =
    finnish.clicks := by native_decide
theorem hungarian_f142a :
    (Core.WALS.F142A.lookup "hun").map (fromWALS142A ·.value) =
    hungarian.clicks := by native_decide
theorem hindi_f142a :
    (Core.WALS.F142A.lookup "hin").map (fromWALS142A ·.value) =
    hindi.clicks := by native_decide
theorem swahili_f142a :
    (Core.WALS.F142A.lookup "swa").map (fromWALS142A ·.value) =
    swahili.clicks := by native_decide
theorem tagalog_f142a :
    (Core.WALS.F142A.lookup "tag").map (fromWALS142A ·.value) =
    tagalog.clicks := by native_decide

-- ============================================================================
-- Typological Generalizations
-- ============================================================================

/-- Most languages distinguish 'hand' from 'arm' (389 vs 228). -/
theorem hand_arm_different_majority : (389 : Nat) > 228 := by native_decide

/-- Finger-hand identity is rare: only 72/593 = 12% of languages. -/
theorem finger_hand_identity_rare : (72 : Nat) * 8 < 593 := by native_decide

/-- Among languages with finger=hand identity, hunter-gatherers dominate
    (46/72 = 64%). -/
theorem finger_hand_hunter_gatherer_majority : (46 : Nat) * 2 > 72 := by native_decide

/-- Grue (merged green/blue) is the majority pattern for the green-blue
    dimension (68/120 = 57%), far exceeding the distinct-terms pattern (30). -/
theorem grue_majority : (68 : Nat) > 30 := by native_decide

/-- Red and yellow are almost always distinguished: 98/120 = 82% of
    languages have separate terms. -/
theorem red_yellow_usually_distinct : (98 : Nat) * 5 > 120 * 4 := by native_decide

/-- The M-T pronoun pattern is a minority pattern: only 30/230 languages
    show any form of it. Most languages (200/230) lack it. -/
theorem mt_pronouns_minority : (200 : Nat) > 30 := by native_decide

/-- The *cha* route for tea is slightly more common than *te*:
    110 vs 84 languages. Both vastly outnumber independent forms (36). -/
theorem cha_more_common_than_te : (110 : Nat) > 84 := by native_decide
theorem tea_wanderwort_dominant : (110 : Nat) + 84 > 36 * 5 := by native_decide

/-- Affective click usage is more common than logical click usage
    (71 vs 47 languages). -/
theorem affective_clicks_more_common : (71 : Nat) > 47 := by native_decide

/-- In our sample, all European languages with an M-T pattern also
    have /m/ in 1SG (expected, since the M-T pattern implies 1SG=m). -/
theorem mt_implies_m_in_1sg :
    allLanguages.all (λ p =>
      match p.mtPronouns, p.mIn1sg with
      | some .paradigmatic, some v => v == .present
      | _, _ => true) = true := by native_decide

/-- The *cha*/*te* split in our sample follows geography:
    East/South Asian + Russian languages use *cha*, while
    Western European languages use *te*. -/
def chaLanguages : List LexicalProfile :=
  allLanguages.filter (λ p => p.tea == some .cha)
def teLanguages : List LexicalProfile :=
  allLanguages.filter (λ p => p.tea == some .te)

theorem cha_language_count : chaLanguages.length = 9 := by native_decide
theorem te_language_count : teLanguages.length = 6 := by native_decide

/-- All languages in our sample with colour data have exactly 6
    non-derived basic colour categories. -/
theorem all_sampled_have_six_nonderived :
    allLanguages.all (λ p =>
      match p.nonDerivedColours with
      | some v => v == .six
      | none => true) = true := by native_decide

/-- All languages in our sample with colour data distinguish green
    from blue (no grue languages in our major-language sample). -/
theorem all_sampled_distinguish_green_blue :
    allLanguages.all (λ p =>
      match p.greenBlue with
      | some v => v == .distinct
      | none => true) = true := by native_decide

end Phenomena.LexicalTypology.Typology
