import Linglib.Syntax.ConstructionGrammar.ArgumentStructure
import Linglib.Semantics.Presupposition.Basic

/-!
# [goldberg-shirtz-2025]: the English Phrase-as-Lemma (PAL) construction

PALs are phrases used in slots typically reserved for single words ("a
trickle-down policy", "the 'both sides do it' argument"). Treating a phrase
as if it were a word invites a lemma-like construal: the PAL names a
situation type presumed familiar to speaker and addressee, with wit and
sarcasm as derived rhetorical effects of discussing the presumed-familiar.
The paper's Figure 5 network relates the prenominal PAL construction by
normal-mode inheritance to both the NN compound construction (tight
phonological/semantic unit, PAL-internal stress) and adjectival modification
(prenominal slot, no recursive embedding), with four experimentally
confirmed conventional subtypes.

## Main declarations

- `GoldbergShirtz2025.palConstruction`, `palConstructicon`: the Figure 5 network
- `GoldbergShirtz2025.palMeaning`: familiarity presupposition + head-noun assertion
- `GoldbergShirtz2025.pal_irreducible`: PAL is not fully compositional
- `GoldbergShirtz2025.palExamples`, `crossLinguisticPALs`: attested examples

## Experimental results

Five preregistered 2AFC surveys (statistics quoted from the paper's results;
700 recruited, 685 retained across the four surveys of studies 1–3). PAL
sentences vs. close paraphrases were judged to imply more common knowledge
(1a: M = 77.3%, β = 1.69, z = 4.80, p < 0.0001) and more shared background
(1b: M = 74.3%, β = 1.78, z = 4.62, p < 0.001), and to be wittier
(2: M = 82.2%, β = 2.58, z = 8.48, p < 0.001) and more sarcastic
(3: M = 84.5%, β = 2.71, z = 8.54, p < 0.001). Study 4 (high-frequency PALs
only, n = 70) replicated all three effects (common knowledge M = 72.88%;
wit M = 79.81; sarcasm M = 84.46). Study 5 (n = 74) confirmed four
conventional subtypes: instances were judged more natural than minimally
different foils (M = 86.09%, β = 2.28, z = 6.09, p < 0.0001).
-/

namespace GoldbergShirtz2025

open ConstructionGrammar
open Semantics.Presupposition

/-! ### The Figure 5 constructicon -/

/-- The prenominal PAL construction: a zero-level PAL whose internal syntax
is phrasal modifies a head N, forming an N′ (the paper's structure (7),
`[N′ PAL⁰ N]`, vs. the NN compound's `[N⁰ N⁰ N⁰]`). The head N's bar level
is left underspecified since PALs may modify nouns with complements
("a 'don't mess with me' type of driver"). -/
def palConstruction : Construction :=
  { name := "PAL"
  , form := "[N′ PAL⁰ N]"
  , meaning := "the PAL names a situation type; the head N is an instance of it"
  , specificity := .fullyAbstract
  , pragmaticFunction := "presumes familiarity with the situation type named by the PAL" }

/-- The semiproductive must-V subtype, frequently instantiated by
*must-read*, *must-see*, *must-have*. Study 5 tested only rare tokens
(≤ 10 COCA hits) against *should-V* foils. -/
def mustVerbConstruction : Construction :=
  { name := "must-V"
  , form := "[N′ [PAL⁰ must V] N]"
  , meaning := "N is something one must V"
  , specificity := .partiallyOpen
  , pragmaticFunction := "presumes familiarity with the situation type named by the PAL" }

/-- The *a simple ⟨PAL⟩* subtype: the PAL is itself the head noun
("Could've tried a simple 'I'm sorry.'"). Study 5's foils used *a short*. -/
def aSimplePALConstruction : Construction :=
  { name := "a simple [PAL⁰]"
  , form := "[NP a simple PAL⁰]"
  , meaning := "a routine instance of the situation type named by the PAL"
  , specificity := .partiallyOpen
  , pragmaticFunction := "presumes familiarity; 'simple' marks the situation type as routine" }

/-- The *Don't ⟨PAL⟩ me* subtype: the PAL fills a V slot, must quote the
immediately preceding discourse, and occurs in an interdiction context
("A: you're welcome. B: No, don't 'you're welcome' me."). Study 5's foils
broke exactly the quote-from-context or interdiction condition. -/
def dontPALmeConstruction : Construction :=
  { name := "Don't [PAL⁰ x y z] me"
  , form := "[VP Don't [V⁰ PAL⁰] me]"
  , meaning := "don't direct the just-quoted utterance at me"
  , specificity := .partiallyOpen
  , pragmaticFunction := "interdicts the quoted conversational move; presumes the quote from the immediately preceding context" }

/-- The *the old ⟨PAL⟩ (N)* subtype, with optional head N ("my dad pulled
the old 'I'm going to the store for smokes, be back in five'"). Study 5's
foils used *the tired*. -/
def theOldPALConstruction : Construction :=
  { name := "the old [PAL⁰] (N)"
  , form := "[NP the old PAL⁰ (N)]"
  , meaning := "a well-worn instance of the situation type named by the PAL"
  , specificity := .partiallyOpen
  , pragmaticFunction := "presumes familiarity; 'old' marks the situation type as conventional" }

/-- NN compound construction (parent: PAL-internal stress, tight unit). -/
def nnCompound : Construction :=
  { name := "NN compound"
  , form := "[N⁰ N⁰ N⁰]"
  , meaning := "compound nominal: modifier noun narrows head noun denotation"
  , specificity := .fullyAbstract }

/-- Adjectival modification construction (parent: prenominal slot). -/
def adjNModification : Construction :=
  { name := "Adj+N modification"
  , form := "[N′ Adj N′]"
  , meaning := "adjective restricts noun denotation"
  , specificity := .fullyAbstract }

/-- The PAL constructicon (the paper's Figure 5): the prenominal PAL
construction partially inherits, in normal mode, from both the NN compound
and adjectival modification constructions; the four conventional subtypes
confirmed by study 5 inherit from it. The figure's caption labels all
arrows "motivation and (normal mode) inheritance links", so no
Goldberg-1995 link type is assigned. -/
def palConstructicon : Constructicon :=
  { constructions :=
      [ palConstruction
      , mustVerbConstruction
      , aSimplePALConstruction
      , dontPALmeConstruction
      , theOldPALConstruction
      , nnCompound
      , adjNModification ]
  , links :=
      [ { parent := "NN compound"
        , child := "PAL"
        , mode := .normal
        , sharedProperties := ["prenominal slot for the modifier"
                              , "tight semantic and phonological unit: stress falls within the PAL"]
        , overriddenProperties := ["modifier is internally phrasal; PAL N is an N′, not an N⁰"] }
      , { parent := "Adj+N modification"
        , child := "PAL"
        , mode := .normal
        , sharedProperties := ["prenominal slot for the modifier"
                              , "no recursive embedding within another PAL N construction"]
        , overriddenProperties := ["modifier is a zero-level PAL, not an Adj"] }
      , { parent := "PAL"
        , child := "must-V"
        , mode := .normal
        , sharedProperties := ["lemma-like construal: presumed familiarity"]
        , overriddenProperties := ["'must' lexically fixed; V slot open"] }
      , { parent := "PAL"
        , child := "a simple [PAL⁰]"
        , mode := .normal
        , sharedProperties := ["lemma-like construal: presumed familiarity"]
        , overriddenProperties := ["PAL is the head noun, not a prenominal modifier"] }
      , { parent := "PAL"
        , child := "Don't [PAL⁰ x y z] me"
        , mode := .normal
        , sharedProperties := ["lemma-like construal: presumed familiarity"]
        , overriddenProperties := ["PAL fills a V slot; quote-from-context and interdiction required"] }
      , { parent := "PAL"
        , child := "the old [PAL⁰] (N)"
        , mode := .normal
        , sharedProperties := ["lemma-like construal: presumed familiarity"]
        , overriddenProperties := ["head N optional; PAL may serve as head"] } ] }

/-! ### Lemma-like meaning -/

/-- A PAL utterance's two-part meaning: the head noun's denotation is
at-issue (an instance of the situation type); the lemma-like construal
contributes that the situation type itself is presumed familiar.

The paper treats the familiarity as an invited *as-if* construal rather
than a hard definedness condition: speakers exploit the construction
precisely for situation types that are not antecedently familiar
(observational humor, sniglets), so common-ground satisfaction is typically
reached by accommodation or pretense, not antecedent entailment. -/
def palMeaning (W : Type*) (situationType headNoun : W → Prop) : PrProp W :=
  { presup := situationType, assertion := headNoun }

/-! ### Irreducibility -/

/-- The PAL construction is not fully compositional: pairing
phrase-in-a-word-slot form with a presumed-familiarity function is a
construction-specific pragmatic function, so PAL cannot be decomposed into
the three universal combination schemata (see `isFullyCompositional`). -/
theorem pal_irreducible :
    isFullyCompositional palConstruction = false := rfl

/-! ### Attested distribution

PALs prototypically modify nouns but are attested as head Nouns,
predicative Adjectives, and Verbs (the paper's Table 2), and take word-level
inflection in those slots — plural *-s*, progressive *-ing* (Table 3). -/

/-- Syntactic positions where PALs are attested (the paper's Table 2). -/
inductive PALPosition where
  | prenominalModifier
  | headNoun
  | predicativeAdj
  | verb
  deriving Repr, DecidableEq

/-- An attested PAL example with its syntactic position. -/
structure PALExample where
  pal : String
  position : PALPosition
  sentence : String
  deriving Repr

/-- Attested examples (the paper's ex. (1), Table 2, and Table 3;
COCA unless noted). -/
def palExamples : List PALExample :=
  [ { pal := "trickle-down"
    , position := .prenominalModifier
    , sentence := "a trickle-down policy" }
  , { pal := "both sides do it"
    , position := .prenominalModifier
    , sentence := "the 'both sides do it' argument" }
  , { pal := "must see"
    , position := .headNoun
    , sentence := "This show is a must see." }
  , { pal := "I'm sorry"
    , position := .headNoun
    , sentence := "Could've tried a simple 'I'm sorry.'" }
  , -- Jespersen 1924:96; plural -s on a PAL in a Noun slot (Table 3)
    { pal := "I told you so"
    , position := .headNoun
    , sentence := "his speech abounded in I told you so's" }
  , { pal := "I'm nothing like you"
    , position := .predicativeAdj
    , sentence := "Romney's slogan should be more 'I'm nothing like you.'" }
  , -- Brit Bennett, *The vanishing half*; progressive -ing on a PAL in a V slot
    { pal := "honey-I'm-home"
    , position := .verb
    , sentence := "carrying on like a television husband, honey-I'm-home-ing her from the doorway" }
  , { pal := "you're welcome"
    , position := .verb
    , sentence := "A: you're welcome. B: No, don't 'you're welcome' me." } ]

/-! ### Comparable constructions in other languages (§7) -/

/-- Host frame of a comparable PAL construction. West Germanic and Turkish
PALs occur in compound(-like) frames (Turkish marks the host with the
compound marker on the head noun); Hebrew and Brazilian Portuguese PALs
occur as complements of a preposition (*ʃel* / *de*) — showing the PAL
construction need not resemble a compound, only occupy a slot typical of
single words. -/
inductive PALHostFrame where
  | compound
  | prepositionComplement
  deriving Repr, DecidableEq

/-- A reported PAL-comparable construction in another language. -/
structure CrossLinguisticPAL where
  language : String
  family : String
  exemplar : String
  gloss : String
  hostFrame : PALHostFrame
  deriving Repr

/-- German (the paper's ex. (8a), from [meibauer-2007]:250). [meibauer-2007]
also found German PALs judged wittier than relative-clause paraphrases —
the effect study 2 replicates for English. -/
def german : CrossLinguisticPAL :=
  { language := "German"
  , family := "Indo-European (Germanic)"
  , exemplar := "Kaufe-Ihr-Auto-Kärtchen"
  , gloss := "'I-buy-your-car card'"
  , hostFrame := .compound }

/-- Dutch (ex. (15a), from [meibauer-2007]:235). -/
def dutch : CrossLinguisticPAL :=
  { language := "Dutch"
  , family := "Indo-European (Germanic)"
  , exemplar := "lach of ik schiet humor"
  , gloss := "'laugh-or-I-shoot humor'"
  , hostFrame := .compound }

/-- Afrikaans (ex. (15b), from [meibauer-2007]:235, as printed there). -/
def afrikaans : CrossLinguisticPAL :=
  { language := "Afrikaans"
  , family := "Indo-European (Germanic)"
  , exemplar := "God is dod theologie"
  , gloss := "'god-is-dead theology'"
  , hostFrame := .compound }

/-- Turkish (ex. (15c), from [trips-kornfilt-2015]:307); the compound
marker on the head noun signals the compound-like frame. -/
def turkish : CrossLinguisticPAL :=
  { language := "Turkish"
  , family := "Turkic"
  , exemplar := "'iç çamaşır-ın-ı göster' oyun-u"
  , gloss := "'\"show your underwear\" game'"
  , hostFrame := .compound }

/-- Modern Hebrew (ex. (16b), the paper's own observation, from Twitter). -/
def hebrew : CrossLinguisticPAL :=
  { language := "Hebrew"
  , family := "Afro-Asiatic (Semitic)"
  , exemplar := "keta ʃel mi=ʃe yodea yodea"
  , gloss := "'an if-you-know-you-know thing'"
  , hostFrame := .prepositionComplement }

/-- Brazilian Portuguese (ex. (18b), the paper's own observation, from the
NOW corpus). -/
def brazilianPortuguese : CrossLinguisticPAL :=
  { language := "Brazilian Portuguese"
  , family := "Indo-European (Romance)"
  , exemplar := "o clima ameno de 'eu te ajudo, você me ajuda e está tudo bem'"
  , gloss := "'the pleasant climate of \"I help you, you help me, and everything is good\"'"
  , hostFrame := .prepositionComplement }

/-- All cross-linguistic attestations reported in §7. -/
def crossLinguisticPALs : List CrossLinguisticPAL :=
  [german, dutch, afrikaans, turkish, hebrew, brazilianPortuguese]

end GoldbergShirtz2025
