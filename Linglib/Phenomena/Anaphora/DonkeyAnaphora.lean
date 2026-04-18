import Linglib.Core.Lexical.Word
import Linglib.Core.Definiteness
import Linglib.Core.Nominal.ArticleInventory
import Linglib.Fragments.German.Definiteness
import Linglib.Fragments.Thai.Definiteness
import Linglib.Fragments.Mandarin.Definiteness
import Linglib.Fragments.Shan.Definiteness

/-!
# Donkey Anaphora: Empirical Data
@cite{geach-1962} @cite{heim-1982} @cite{kadmon-1987} @cite{kanazawa-1994} @cite{schwarz-2009}

Theory-neutral data on donkey anaphora and related binding puzzles.

## The Phenomenon

Donkey sentences involve pronouns that are apparently bound by indefinites
in syntactically "inaccessible" positions:

  "Every farmer who owns a donkey beats it"

The indefinite "a donkey" is inside a relative clause, yet "it" seems
to depend on it for its reference.

## Properties

1. The indefinite doesn't c-command the pronoun (scope puzzle).
2. Often interpreted as "...beats every donkey they own" (universal force).
3. Sometimes "...beats some donkey they own" (weak readings).
4. "Most farmers who own a donkey beat it" (proportion problem).

-/

namespace Phenomena.Anaphora.DonkeyAnaphora

-- Part 1: Basic Donkey Sentence Data

/-- A donkey anaphora datum records a sentence with its readings -/
structure DonkeyDatum where
  /-- The sentence -/
  sentence : String
  /-- Does the pronoun depend on the indefinite? -/
  boundReading : Bool
  /-- Is a universal ("strong") reading available? -/
  strongReading : Bool
  /-- Is an existential ("weak") reading available? -/
  weakReading : Bool
  /-- Is the sentence grammatical? -/
  grammatical : Bool := true
  /-- Notes on the reading -/
  notes : String := ""
  /-- Citation -/
  source : String := ""
  deriving Repr

/-- Classic Geach donkey sentence -/
def geachDonkey : DonkeyDatum := {
  sentence := "Every farmer who owns a donkey beats it"
  boundReading := true
  strongReading := true  -- every donkey they own
  weakReading := true    -- some donkey they own (less salient)
  notes := "The original donkey sentence. Strong reading preferred."
  source := "Geach (1962)"
}

/-- Conditional donkey -/
def conditionalDonkey : DonkeyDatum := {
  sentence := "If a farmer owns a donkey, he beats it"
  boundReading := true
  strongReading := true
  weakReading := true
  notes := "Conditional variant. Similar to relative clause version."
  source := "Heim (1982)"
}

/-- Negated donkey -/
def negatedDonkey : DonkeyDatum := {
  sentence := "No farmer who owns a donkey beats it"
  boundReading := true
  strongReading := true  -- no farmer beats any donkey they own
  weakReading := false   -- weak reading incoherent here
  notes := "Negation context. Universal reading only."
  source := "Kanazawa (1994)"
}

/-- "Most" donkey (proportion problem) -/
def mostDonkey : DonkeyDatum := {
  sentence := "Most farmers who own a donkey beat it"
  boundReading := true
  strongReading := true
  weakReading := true
  notes := "The proportion problem: is this about farmer-donkey pairs or farmers?"
  source := "Kadmon (1987)"
}

-- Part 2: Weak vs Strong Readings

/-- Data on weak vs strong reading availability -/
structure WeakStrongDatum where
  sentence : String
  strongAvailable : Bool
  weakAvailable : Bool
  preferredReading : String  -- "strong", "weak", or "both"
  context : String := ""
  source : String := ""
  deriving Repr

/-- Strong reading dominant -/
def strongDominant : WeakStrongDatum := {
  sentence := "Every farmer who owns a donkey beats it"
  strongAvailable := true
  weakAvailable := true
  preferredReading := "strong"
  context := "Out of the blue"
  source := "Kanazawa (1994)"
}

/-- Weak reading facilitated by context -/
def weakFacilitated : WeakStrongDatum := {
  sentence := "Every person who has a credit card uses it to pay"
  strongAvailable := true
  weakAvailable := true
  preferredReading := "weak"
  context := "Buying groceries (single transaction)"
  source := "Chierchia (1995)"
}

/-- Only strong reading possible -/
def onlyStrong : WeakStrongDatum := {
  sentence := "No farmer who owns a donkey mistreats it"
  strongAvailable := true
  weakAvailable := false
  preferredReading := "strong"
  context := "Negative quantifier forces universal"
  source := "Kanazawa (1994)"
}

-- Part 3: Related Anaphora Puzzles

/-- Bathroom sentences (Partee) -/
def bathroomSentence : DonkeyDatum := {
  sentence := "Either there is no bathroom, or it is in a funny place"
  boundReading := true
  strongReading := false
  weakReading := false
  notes := "Pronoun 'it' depends on 'bathroom' across disjunction."
  source := "Partee (1972)"
}

/-- Paycheck pronouns -/
def paycheckSentence : DonkeyDatum := {
  sentence := "The man who gave his paycheck to his wife was wiser than the man who gave it to his mistress"
  boundReading := true
  strongReading := false
  weakReading := false
  notes := "'it' = 'his paycheck', but with second man's paycheck"
  source := "Karttunen (1969)"
}

/-- Sage plant sentences (Evans) -/
def sagePlant : DonkeyDatum := {
  sentence := "Few congressmen admire Kennedy, and they are very junior"
  boundReading := true
  strongReading := false
  weakReading := false
  notes := "'they' refers to the few congressmen who do admire Kennedy"
  source := "Evans (1977)"
}

-- Part 4: Cross-sentential Donkey Anaphora

/-- Discourse-level donkey anaphora -/
structure DiscourseDonkeyDatum where
  sentences : List String
  pronounSentenceIdx : Nat  -- which sentence contains the pronoun
  antecedentSentenceIdx : Nat  -- which sentence contains the antecedent
  grammatical : Bool
  notes : String := ""
  source : String := ""
  deriving Repr

/-- Cross-sentential binding -/
def crossSententialDonkey : DiscourseDonkeyDatum := {
  sentences := ["Every farmer owns a donkey.", "He beats it."]
  pronounSentenceIdx := 1
  antecedentSentenceIdx := 0
  grammatical := false  -- binding doesn't cross sentence boundary
  notes := "Quantifier scope doesn't extend across sentences"
  source := "Heim (1982)"
}

/-- Indefinite persists across sentences -/
def indefinitePersists : DiscourseDonkeyDatum := {
  sentences := ["A man walked in.", "He sat down."]
  pronounSentenceIdx := 1
  antecedentSentenceIdx := 0
  grammatical := true
  notes := "Indefinite introduces discourse referent that persists"
  source := "Heim (1982)"
}

-- Part 5: Proportion Problem Data

/-- The proportion problem: what is being counted? -/
structure ProportionDatum where
  sentence : String
  /-- Farmer-counting: proportion of farmers (who own donkeys) -/
  farmerCountingReading : String
  /-- Pair-counting: proportion of farmer-donkey pairs -/
  pairCountingReading : String
  /-- Which reading is more natural? -/
  preferredReading : String
  source : String := ""
  deriving Repr

/-- Classic proportion problem case -/
def proportionProblem : ProportionDatum := {
  sentence := "Most farmers who own a donkey beat it"
  farmerCountingReading := "Most farmers (among those who own donkeys) beat their donkey(s)"
  pairCountingReading := "Most farmer-donkey pairs are such that the farmer beats the donkey"
  preferredReading := "farmer-counting"
  source := "Kadmon (1987)"
}

-- Part 6: Collected Data

/-- All basic donkey data -/
def donkeyData : List DonkeyDatum := [
  geachDonkey,
  conditionalDonkey,
  negatedDonkey,
  mostDonkey,
  bathroomSentence,
  paycheckSentence,
  sagePlant
]

/-- All weak/strong reading data -/
def weakStrongData : List WeakStrongDatum := [
  strongDominant,
  weakFacilitated,
  onlyStrong
]

/-- All discourse-level data -/
def discourseDonkeyData : List DiscourseDonkeyDatum := [
  crossSententialDonkey,
  indefinitePersists
]

-- ============================================================================
-- §6: Bridge to Core.Definiteness
-- ============================================================================

/-! ### Donkey anaphora as a definiteness use type

@cite{schwarz-2009} §3: donkey pronouns in German pattern with anaphoric
definites (strong article *von dem*), not with uniqueness definites
(weak article *vom*). This means donkey anaphora selects the
*familiarity* presupposition type — the same as regular anaphora.

The cross-linguistic pattern:
- **German**: strong article (*von dem*) — two-article system distinguishes
- **Thai/Mandarin**: demonstrative — demonstratives fill the strong-article role
- **Shan**: bare noun — no articles, so no morphological signal

This parallels the general pattern for anaphoric definites in
@cite{moroney-2021} Table 4.4. -/

open Core.Definiteness (DefiniteUseType DefPresupType useTypeToPresupType
  ArticleType)
open Core.Nominal (ArticleInventory)

/-- Donkey anaphora is classified as its own use type in the definiteness
typology, distinct from regular anaphora but sharing the same
presupposition type (familiarity). -/
def donkeyUseType : DefiniteUseType := .donkey

/-- Donkey pronouns select the familiarity (strong article) presupposition
type. @cite{schwarz-2009} §3: in German, donkey pronouns require the
strong article (*von dem*), patterning with anaphoric uses rather
than uniqueness uses. -/
theorem donkey_presup_is_familiarity :
    useTypeToPresupType donkeyUseType = .familiarity := rfl

/-- Donkey anaphora and regular anaphora share the same presupposition
type (familiarity). This is why they select the same article form
cross-linguistically: both require discourse familiarity, not
situational uniqueness. -/
theorem donkey_patterns_with_anaphoric :
    useTypeToPresupType .donkey = useTypeToPresupType .anaphoric := rfl

/-- Cross-linguistic data on how donkey anaphora is expressed
morphologically. This connects the abstract `DefiniteUseType.donkey`
to concrete article forms.

The article system (`articleSystem`) is *derived* from the language's
fragment-level `articleInventory`, not stipulated independently —
`ArticleInventory` is the single source of truth. -/
structure DonkeyArticleDatum where
  language : String
  isoCode : String
  /-- Morphological form used for donkey pronouns -/
  form : String
  /-- Morphological article inventory (single source of truth from which
      `articleSystem` is derived). -/
  articleInventory : ArticleInventory
  deriving Repr

/-- Schwarz `ArticleType` classification, derived from `articleInventory`. -/
def DonkeyArticleDatum.articleSystem (d : DonkeyArticleDatum) : ArticleType :=
  d.articleInventory.toArticleType

def germanDonkey : DonkeyArticleDatum :=
  { language := "German", isoCode := "deu"
    form := "strong article (von dem)"
    articleInventory := Fragments.German.Definiteness.articleInventory }

def thaiDonkey : DonkeyArticleDatum :=
  { language := "Thai", isoCode := "tha"
    form := "demonstrative"
    articleInventory := Fragments.Thai.Definiteness.articleInventory }

def mandarinDonkey : DonkeyArticleDatum :=
  { language := "Mandarin", isoCode := "cmn"
    form := "demonstrative"
    articleInventory := Fragments.Mandarin.Definiteness.articleInventory }

def shanDonkey : DonkeyArticleDatum :=
  { language := "Shan", isoCode := "shn"
    form := "bare noun"
    articleInventory := Fragments.Shan.Definiteness.articleInventory }

/-- All cross-linguistic donkey article data. -/
def donkeyArticleData : List DonkeyArticleDatum :=
  [germanDonkey, thaiDonkey, mandarinDonkey, shanDonkey]

/-- In languages with a weak/strong article distinction, donkey anaphora
uses the strong form — never the weak form. This is predicted by
`donkey_presup_is_familiarity`: strong articles encode familiarity,
and donkey anaphora requires familiarity. -/
theorem weakAndStrong_uses_strong :
    (donkeyArticleData.filter (·.articleSystem == .weakAndStrong)).all
      (·.form == "strong article (von dem)") = true := by decide

end Phenomena.Anaphora.DonkeyAnaphora
