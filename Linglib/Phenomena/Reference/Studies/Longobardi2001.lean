import Linglib.Theories.Semantics.Noun.Kind.Chierchia1998
import Linglib.Theories.Semantics.Noun.Kind.Carlson1977
import Linglib.Phenomena.Generics.KindReference
import Linglib.Fragments.Italian.Nouns
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.Greek.Nouns

/-! # Longobardi (2001): A Unified Parametric Theory of Bare Nouns and Proper Names
@cite{longobardi-2001}

Natural Language Semantics 9: 335--369.

## Core Thesis

Crosslinguistic variation in bare noun (BN) semantics and proper name (PN)
syntax reduces to two DP-internal parameters: whether D has 'strong'
referential features (`strongD`), and whether N-raising crosses adjectives
transparently (`transparentAlpha`). The paper establishes:

1. **Romance BNs are always indefinites** — quantificational variables
   (existentially or generically bound), never kind-denoting constants.
2. **English BNs are ambiguous** — they can be *referential* (kind names,
   in the spirit of @cite{carlson-1977}) OR *quantificational* (indefinite
   variables, like Romance BNs).
3. **Two types of genericity** (supporting @cite{gerstner-krifka-1987}):
   - Indefinite/quantificational generics: variables bound by GEN
   - Definite/referential generics: kind-denoting constants (via D)
4. **Typological generalization**: PN syntax (N-to-D raising) and BN
   semantics (kind reference) are parametrically linked — object-referring
   nouns may occur without phonetically filled D iff kind-referring nouns can.

## Connection to Existing Theory

Longobardi's `ArgumentType` distinction (referential vs quantificational)
cross-cuts @cite{chierchia-1998}'s Nominal Mapping Parameter:
- Chierchia's NMP captures *which denotation types* are available
- Longobardi's parameters capture *why* the denotation types vary,
  grounding the variation in DP-internal syntax (N-to-D raising)

The `DPParameter` structure unifies Chierchia's three-way typology
into a 2×2 parametric space that also predicts PN syntax.

-/

namespace Longobardi2001

open Semantics.Noun.Kind.Chierchia1998 (NominalMapping canDenoteKind)
open Semantics.Noun.Kind.Carlson1977 (PredicateLevel barePluralTranslation
  genericDerivation existentialDerivation RealizationRel stageLevelPred)

-- ============================================================================
-- § 1: Argument Type — Referential vs Quantificational
-- ============================================================================

/-- The semantic type of a nominal argument.

@cite{longobardi-2001} §2: All nominal arguments denote entities from
Carlson's ontology (objects and kinds). They divide into two types:

- **Referential**: constants — denote directly through the lexical
  referring potential of the head noun. Proper names and kind names.
  Rigid designators with widest scope (@cite{kripke-1980}).
- **Quantificational**: variables — denote via a variable bound by
  a (possibly covert) operator, with the noun's kind-naming meaning
  serving as predicative restrictor. Overt indefinites and Romance BNs. -/
inductive ArgumentType where
  /-- Constants: denote directly via lexical reference (proper names,
      kind names). No variable, no operator binding. -/
  | referential
  /-- Variables: denote via a variable bound by Ex or Gen.
      The noun's kind-naming meaning provides the restrictor. -/
  | quantificational
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: DP Parameters — Strong D × Transparent α
-- ============================================================================

/-- The DP-internal parametric system from @cite{longobardi-2001} table (61).

Two binary parameters on the nominal projection:

- `strongD`: Whether D has 'strong' referential features requiring
  visible association with referential items. In Romance, D is strong:
  referential nouns must be introduced by a phonetically filled D
  (either by N-to-D raising for PNs or by an expletive article).
  In English/Germanic, D is weak: referential readings are available
  without overt D.

- `transparentAlpha`: Whether the α constituent (between D and N) is
  transparent to N-raising. In Romance, α is transparent: N can raise
  across adjectives to D. In English/Germanic, α is opaque: N cannot
  raise past adjectives. This is visible from adjective position:
  Romance has postnominal adjectives (N raises past them), English
  has prenominal adjectives (N stays in situ).

Note: `transparentAlpha` affects only DP-internal *syntax* (adjective
position, N-raising), not BN *semantics* directly. BN semantics is
determined by `strongD` alone. The two parameters are independent
but co-vary in the unmarked cases (Romance: both +; English: both −).
Greek (§9.5) shows they can be set independently (+strong, −transparent). -/
structure DPParameter where
  /-- D has strong referential features (Romance +, English −) -/
  strongD : Bool
  /-- α is transparent to N-raising (Romance +, English −) -/
  transparentAlpha : Bool
  deriving DecidableEq, Repr

/-- Romance (Italian, French, Spanish): strong D, transparent α. -/
def romance : DPParameter := { strongD := true, transparentAlpha := true }

/-- English (Germanic): weak D, opaque α. -/
def english : DPParameter := { strongD := false, transparentAlpha := false }

/-- Greek: strong D, opaque α — the intermediate case.
    BNs pattern like Romance (quantificational only).
    PNs require overt definite article (cannot raise to D through opaque α,
    and D is strong so must be overtly filled). -/
def greek : DPParameter := { strongD := true, transparentAlpha := false }

/-- Celtic (speculative): weak D, transparent α — the other intermediate.
    @cite{longobardi-2001} fn. 35: "The other intermediate pair of values
    ('weak' D and transparent α) is likely to be instantiated by Celtic
    languages and is irrelevant to the present reasoning." Included for
    completeness of the 2×2 table; not empirically developed in the paper. -/
def celtic : DPParameter := { strongD := false, transparentAlpha := true }

-- ============================================================================
-- § 3: BN Interpretation — The Two Mapping Systems
-- ============================================================================

/-- Whether bare nouns can be referential (kind-denoting constants)
    in a given language's parametric setting.

    @cite{longobardi-2001} (44): English BNs can be referential (kind names)
    because D is weak — referential status doesn't require overt D.
    Romance BNs are always quantificational because D is strong —
    referential status requires overt D (only definite plurals achieve it).

    The derivation: BN referentiality requires that a kind-naming meaning
    can reach D without overt material. With weak D, no overt association
    needed. With strong D, the noun would need to raise to D (N-to-D)
    or an expletive article is needed — but BNs by definition lack both.

    Note: this depends only on `strongD`, not `transparentAlpha`. The α
    parameter affects whether N *can* raise to D (relevant for PNs), but
    BN referentiality is about whether D *requires* overt filling at all. -/
def bnCanBeReferential (dp : DPParameter) : Bool :=
  !dp.strongD

/-- Whether bare nouns are always quantificational (indefinites). -/
def bnAlwaysQuantificational (dp : DPParameter) : Bool :=
  dp.strongD

/-- Available argument types for BNs in a language. -/
def bnArgumentTypes (dp : DPParameter) : List ArgumentType :=
  if bnCanBeReferential dp then
    [.referential, .quantificational]
  else
    [.quantificational]

-- ============================================================================
-- § 4: Two Types of Genericity
-- ============================================================================

/-- Generic reading type, following @cite{gerstner-krifka-1987} as
    adopted by @cite{longobardi-2001}.

    The paper shows that 'genericity' is an epiphenomenon covering
    two structurally distinct interpretive strategies. -/
inductive GenericType where
  /-- Quantificational generalization over objects of a kind.
      The nominal is an indefinite (variable) bound by GEN.
      Available in characterizing environments only.
      Romance BNs, overt indefinites (both Romance and English). -/
  | indefiniteGeneric
  /-- Kind denotation — the nominal is a referential expression
      (a kind name, like a proper name). Available in all environments.
      Only through overtly definite DPs in Romance (definite generics),
      or through bare plurals in English (which can be kind names). -/
  | definiteGeneric
  deriving DecidableEq, Repr

/-- Which generic types are available for bare nouns in a language. -/
def bnGenericTypes (dp : DPParameter) : List GenericType :=
  if bnCanBeReferential dp then
    [.indefiniteGeneric, .definiteGeneric]
  else
    [.indefiniteGeneric]

-- ============================================================================
-- § 5: Typological Generalization — PN Syntax ↔ BN Semantics
-- ============================================================================

/-- Whether proper names require overt D (an article or N-to-D raising).

    @cite{longobardi-2001} (52): In some languages (Romance), argument PNs
    must undergo N-to-D raising or appear with an expletive article.
    In others (English), they need neither.

    This is derived from `strongD`: if D must be overtly associated with
    referential items, PNs (prototypical referential items) need overt D.
    If D is weak, PNs can occur bare. -/
def pnRequiresOvertD (dp : DPParameter) : Bool :=
  dp.strongD

/-- Whether proper names require an overt *article* specifically
    (as opposed to satisfying strong D by N-to-D raising).

    @cite{longobardi-2001} §9.5: In Romance (strong D, transparent α),
    PNs can satisfy strong D by N-raising across the transparent α
    constituent. In Greek (strong D, opaque α), N cannot raise past α,
    so PNs MUST appear with an overt definite article. This is the
    paper's key prediction confirmed by (65): all Greek object-referring
    arguments require an overt determiner.

    This is the only prediction that uses `transparentAlpha` directly,
    making the 2×2 parametric table genuinely non-redundant. -/
def pnRequiresArticle (dp : DPParameter) : Bool :=
  dp.strongD && !dp.transparentAlpha

/-- Romance PNs can N-raise to D (transparent α), so they don't need
    an article. Greek PNs cannot raise (opaque α), so they do. -/
theorem pn_article_romance_vs_greek :
    pnRequiresArticle romance = false ∧
    pnRequiresArticle greek = true ∧
    pnRequiresArticle english = false ∧
    pnRequiresArticle celtic = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Typological generalization (56) from @cite{longobardi-2001}:
    Object-referring nouns may occur without a phonetically filled D
    iff kind-referring nouns may.

    Both PN syntax (bare PNs allowed?) and BN semantics (kind reference
    without overt D?) are controlled by the same parameter: `strongD`.
    When D is weak, both bare PNs and referential BNs are licensed.
    When D is strong, neither is. -/
theorem typological_generalization :
    ∀ dp : DPParameter,
      (!pnRequiresOvertD dp) = bnCanBeReferential dp := by
  intro dp; simp [pnRequiresOvertD, bnCanBeReferential]

-- ============================================================================
-- § 6: Generalization (5) — The Natural Class
-- ============================================================================

/-- The four nominal types considered by @cite{longobardi-2001}.

    The paper's key empirical observation (p.355, table) is that three of
    these four pattern identically (as quantificational indefinites), while
    English BNs are the outlier — they can also be referential.

    | Romance overt indef | Romance BN      |  ← same (quantificational)
    | English overt indef | **English BN**  |  ← English BN is different -/
inductive NominalClass where
  | romanceOvertIndef   -- "due elefanti" / "degli elefanti"
  | romanceBN           -- "elefanti"
  | englishOvertIndef   -- "some elephants" / "two elephants"
  | englishBN           -- "elephants"
  deriving DecidableEq, Repr

/-- Whether a nominal class can be referential (kind-denoting).

    @cite{longobardi-2001} (5): Three of four nominal types are purely
    quantificational. Only English BNs have the additional referential
    (kind-denoting) reading. -/
def nominalClassReferential : NominalClass → Bool
  | .romanceOvertIndef  => false
  | .romanceBN          => false
  | .englishOvertIndef  => false
  | .englishBN          => true

/-- Generalization (5a): Italian BNs = Italian overt indefinites in
    distribution of Ex/Gen readings. -/
theorem gen5a_romance_bn_eq_indef :
    nominalClassReferential .romanceBN =
    nominalClassReferential .romanceOvertIndef := rfl

/-- Generalization (5b): Italian BNs ≠ English BNs. -/
theorem gen5b_romance_bn_ne_english_bn :
    nominalClassReferential .romanceBN ≠
    nominalClassReferential .englishBN := by decide

/-- The natural class: three of four types are quantificational only.
    English BNs are the outlier. -/
theorem natural_class :
    [NominalClass.romanceOvertIndef, .romanceBN, .englishOvertIndef].all
      (fun nc => !nominalClassReferential nc) = true ∧
    nominalClassReferential .englishBN = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 7: Italian BN Data — Romance BNs as Indefinites
-- ============================================================================

/-- Italian BN reading datum.

    @cite{longobardi-2001} §3--7: Italian BNs distribute their readings
    identically to overt indefinites (generalization (5a)). -/
structure ItalianBNDatum where
  sentence : String
  gloss : String
  /-- Available readings: Ex, Gen, or both -/
  exOK : Bool
  genOK : Bool
  /-- Kind-level predicate (K-level)? -/
  kLevelPred : Bool := false
  notes : String
  deriving Repr

-- S-level predicates: Ex (episodic), Gen/?Ex (habitual)

def elephantsEpisodic : ItalianBNDatum :=
  { sentence := "Elefanti di colore bianco hanno creato in passato grande curiosità."
  , gloss := "White-colored elephants raised a lot of curiosity in the past."
  , exOK := true, genOK := false
  , notes := "S-level episodic: Ex only" }

def elephantsHabitual : ItalianBNDatum :=
  { sentence := "Elefanti di colore bianco possono creare grande curiosità."
  , gloss := "White-colored elephants may raise a lot of curiosity."
  , exOK := true, genOK := true
  , notes := "S-level characterizing (habitual): Gen/?Ex" }

-- S-level with generalizing adverb: Gen/?Ex

def elephantsAdverb : ItalianBNDatum :=
  { sentence := "Elefanti di colore bianco hanno creato sempre/spesso in passato grande curiosità."
  , gloss := "White-colored elephants always/often raised a lot of curiosity in the past."
  , exOK := true, genOK := true
  , notes := "S-level + adverb: Gen/?Ex" }

-- I-level predicates: split into class A (eventive) and class B (stative)

def watchdogsEfficient : ItalianBNDatum :=
  { sentence := "Cani da guardia di grosse dimensioni sono più efficienti."
  , gloss := "Watchdogs of large size are more efficient."
  , exOK := false, genOK := true
  , notes := "I-level class A (eventive): Gen only" }

def statesProsperous : ItalianBNDatum :=
  { sentence := "??Stati di grandi dimensioni sono prosperi."
  , gloss := "States of large size are prosperous."
  , exOK := false, genOK := false
  , notes := "I-level class B (stative): ?? — neither Ex nor Gen" }

def watchdogsHairy : ItalianBNDatum :=
  { sentence := "??Cani da guardia di grosse dimensioni sono più pelosi/neri."
  , gloss := "Watchdogs of large size are more hairy/black."
  , exOK := false, genOK := false
  , notes := "I-level class B (stative): ?? — neither Ex nor Gen" }

-- K-level predicates: neither Ex nor Gen for BNs

def elephantsExtinct : ItalianBNDatum :=
  { sentence := "*Elefanti di colore bianco sono estinti."
  , gloss := "White-colored elephants have become extinct."
  , exOK := false, genOK := false, kLevelPred := true
  , notes := "K-level: neither Ex nor Gen — BN cannot denote kind" }

def elephantsGrowLarger : ItalianBNDatum :=
  { sentence := "*Elefanti di colore bianco diventano sempre più grandi man mano che si va a nord."
  , gloss := "White-colored elephants grow larger as one drives north."
  , exOK := false, genOK := false, kLevelPred := true
  , notes := "K-level: impossible for BN" }

-- Object BNs

def excludedOldLadies : ItalianBNDatum :=
  { sentence := "Ho escluso solo vecchie signore."
  , gloss := "I only excluded old ladies."
  , exOK := true, genOK := false
  , notes := "Object BN, episodic: Ex only" }

def loveOranges : ItalianBNDatum :=
  { sentence := "Amo/Adoro/Mi piacciono arance di grandi dimensioni."
  , gloss := "I love/adore/like oranges of large size."
  , exOK := false, genOK := true
  , notes := "Object BN, I-level verb: Gen only" }

def italianBNData : List ItalianBNDatum :=
  [ elephantsEpisodic, elephantsHabitual, elephantsAdverb
  , watchdogsEfficient, statesProsperous, watchdogsHairy
  , elephantsExtinct, elephantsGrowLarger
  , excludedOldLadies, loveOranges ]

-- K-level predicates are impossible for Italian BNs
#guard italianBNData.filter (·.kLevelPred) |>.all (fun d => !d.exOK && !d.genOK)

-- I-level class A (eventive) allows Gen; class B (stative) does not
#guard watchdogsEfficient.genOK && !statesProsperous.genOK && !watchdogsHairy.genOK

-- ============================================================================
-- § 8: Italian Definite Generics — Referential Kind Denotation
-- ============================================================================

/-- Italian definite generics can appear in ALL environments where Italian
    BNs cannot — including with K-level predicates and in episodic contexts
    with generic readings. @cite{longobardi-2001} examples (34)--(37). -/
structure ItalianDefGenericDatum where
  sentence : String
  gloss : String
  genOK : Bool
  notes : String
  deriving Repr

def defElephantsCuriosity : ItalianDefGenericDatum :=
  { sentence := "Gli elefanti di colore bianco hanno creato in passato grande curiosità."
  , gloss := "The white-colored elephants raised a lot of curiosity in the past."
  , genOK := true
  , notes := "S-level episodic: Gen via definite kind reference" }

def defElephantsExtinct : ItalianDefGenericDatum :=
  { sentence := "Gli elefanti di colore bianco sono estinti."
  , gloss := "The white-colored elephants have become extinct."
  , genOK := true
  , notes := "K-level: definite plural can denote kind" }

def defElephantsGrow : ItalianDefGenericDatum :=
  { sentence := "Gli elefanti di colore bianco diventano sempre più grandi man mano che si va a nord."
  , gloss := "The white-colored elephants grow larger as one drives north."
  , genOK := true
  , notes := "K-level: definite plural can denote kind" }

def defElephantsSoCalled : ItalianDefGenericDatum :=
  { sentence := "Gli elefanti di colore bianco sono così chiamati per la pigmentazione della loro pelle."
  , gloss := "The white-colored elephants are so-called because of the pigmentation of their skin."
  , genOK := true
  , notes := "K-level: definite plural can denote kind" }

def italianDefGenericData : List ItalianDefGenericDatum :=
  [ defElephantsCuriosity, defElephantsExtinct
  , defElephantsGrow, defElephantsSoCalled ]

-- Italian definite generics are generic in all environments
#guard italianDefGenericData.all (·.genOK)

-- ============================================================================
-- § 9: Anaphoric Binding Diagnostic (§5)
-- ============================================================================

/-- @cite{longobardi-2001} §5: The anaphoric binding test distinguishes
    referential from quantificational BNs.

    English (22): "Cats think very highly of themselves."
    → Ambiguous: 'themselves' refers to the species (kind anaphora,
      non-distributive) OR to each individual cat (distributive).

    Italian (24): "Gatti di grandi dimensioni hanno un'alta opinione di se stessi."
    → Distributive only: each big cat thinks highly of itself.
      The species reading is unavailable because Italian BNs cannot
      denote kinds (quantificational variables lack kind reference).

    The kind-anaphora reading requires referential (kind-denoting) status.
    Only English BNs, which can be referential, provide it. -/
structure AnaphoricBindingDatum where
  sentence : String
  gloss : String
  language : String
  /-- Species (kind anaphora, non-distributive) reading available? -/
  speciesReadingOK : Bool
  /-- Distributive (each individual) reading available? -/
  distributiveReadingOK : Bool
  notes : String
  deriving Repr

def englishCatsThemselves : AnaphoricBindingDatum :=
  { sentence := "Cats think very highly of themselves."
  , gloss := "Cats think very highly of themselves."
  , language := "English"
  , speciesReadingOK := true   -- kind anaphora: the species thinks highly of itself
  , distributiveReadingOK := true  -- each cat thinks highly of itself
  , notes := "English BN: referential → kind anaphora available" }

def italianCatsThemselves : AnaphoricBindingDatum :=
  { sentence := "Gatti di grandi dimensioni hanno un'alta opinione di se stessi."
  , gloss := "Cats of great size have a high opinion of themselves."
  , language := "Italian"
  , speciesReadingOK := false  -- no kind reference → no kind anaphora
  , distributiveReadingOK := true
  , notes := "Italian BN: quantificational → distributive only" }

def anaphoricData : List AnaphoricBindingDatum :=
  [englishCatsThemselves, italianCatsThemselves]

-- English BNs allow kind anaphora; Italian BNs do not
#guard anaphoricData.filter (·.language == "English") |>.all (·.speciesReadingOK)
#guard anaphoricData.filter (·.language == "Italian") |>.all (!·.speciesReadingOK)

/-- The anaphoric binding test aligns with `bnCanBeReferential`:
    kind anaphora requires referential status. -/
theorem anaphoric_binding_from_referentiality :
    -- English: referential → kind anaphora OK
    bnCanBeReferential english = true ∧
    englishCatsThemselves.speciesReadingOK = true ∧
    -- Romance: not referential → kind anaphora blocked
    bnCanBeReferential romance = false ∧
    italianCatsThemselves.speciesReadingOK = false := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 10: English vs Italian BN Contrast
-- ============================================================================

/-- @cite{longobardi-2001} §§4,9.1: English BNs can be generic with
    predicates where Italian BNs cannot — episodic S-level, K-level,
    and stative I-level predicates. The contrast arises because English
    BNs can be referential (kind names), while Italian BNs cannot.
    The six contrast environments are summarized in §9.3. -/
structure ContrastDatum where
  predType : String
  italianBNgeneric : Bool
  englishBNgeneric : Bool
  notes : String
  deriving Repr

def contrastEpisodic : ContrastDatum :=
  { predType := "episodic S-level"
  , italianBNgeneric := false, englishBNgeneric := true
  , notes := "Italian Ex only; English Ex/Gen" }

def contrastKLevel : ContrastDatum :=
  { predType := "K-level"
  , italianBNgeneric := false, englishBNgeneric := true
  , notes := "Italian *; English Gen (kind name)" }

def contrastStativeILevel : ContrastDatum :=
  { predType := "stative (class B) I-level"
  , italianBNgeneric := false, englishBNgeneric := true
  , notes := "Italian ?; English Gen" }

def contrastHabitualSLevel : ContrastDatum :=
  { predType := "habitual S-level"
  , italianBNgeneric := true, englishBNgeneric := true
  , notes := "Both: Gen available (characterizing environment)" }

def contrastData : List ContrastDatum :=
  [contrastEpisodic, contrastKLevel, contrastStativeILevel, contrastHabitualSLevel]

-- The contrasts where Italian BN ≠ English BN are exactly where
-- referential (kind) interpretation is needed
example : (contrastData.filter (fun d => d.englishBNgeneric && !d.italianBNgeneric)
      |>.length) = 3 := rfl

-- Where both languages allow Gen, characterizing environment suffices
-- (quantificational genericity is universal)
example : (contrastData.filter (fun d => d.italianBNgeneric && d.englishBNgeneric)
      |>.length) = 1 := rfl

-- ============================================================================
-- § 11: Greek Evidence — The Intermediate Case
-- ============================================================================

/-- @cite{longobardi-2001} §9.5: Greek has strong D + opaque α.
    This predicts:
    - BNs are quantificational only (like Romance) → no K-level predicates
    - PNs require overt definite article (strong D + opaque α blocks
      both N-raising and bare referential D)

    Greek examples (62)-(65) confirm both predictions. -/
structure GreekDatum where
  sentence : String
  gloss : String
  /-- Is the sentence grammatical (under any reading)? -/
  grammatical : Bool
  /-- Is a kind/generic reading available? -/
  kindReadingOK : Bool
  notes : String
  deriving Repr

def greekBNExtinct : GreekDatum :=
  { sentence := "*Asproi elephantes echoun exaphanisthei."
  , gloss := "White elephants have become extinct."
  , grammatical := false, kindReadingOK := false
  , notes := "K-level + BN: ungrammatical (BN cannot denote kind)" }

def greekBNEpisodic : GreekDatum :=
  { sentence := "Asproi elephantes apothekatisthēkan apo ena kataklysmo to 1874."
  , gloss := "White elephants were exterminated by a cataclysm in 1874."
  , grammatical := true, kindReadingOK := false
  , notes := "Episodic + BN: grammatical with Ex reading only; no kind/Gen reading" }

def greekDefPlExtinct : GreekDatum :=
  { sentence := "Oi asproi elephantes echoun exafanisthei."
  , gloss := "The white elephants have become extinct."
  , grammatical := true, kindReadingOK := true
  , notes := "K-level + def pl: kind denotation via overt D" }

def greekPNRequiresArticle : GreekDatum :=
  { sentence := "*(Ē) Rōmē einai ē proteuousa tēs Italias."
  , gloss := "(The) Rome is the capital of (the) Italy."
  , grammatical := false, kindReadingOK := false
  , notes := "PN without article: ungrammatical (strong D + opaque α)" }

def greekData : List GreekDatum :=
  [greekBNExtinct, greekBNEpisodic, greekDefPlExtinct, greekPNRequiresArticle]

-- Greek BNs cannot get kind readings (even when grammatical with Ex)
#guard !greekBNExtinct.kindReadingOK && !greekBNEpisodic.kindReadingOK
-- Greek definite plurals rescue kind readings
#guard greekDefPlExtinct.kindReadingOK

/-- Greek confirms the `strongD` prediction: BN kind reference is
    blocked, and PNs require overt D — same as Romance for both. -/
theorem greek_confirms_strong_d :
    bnCanBeReferential greek = false ∧
    pnRequiresOvertD greek = true ∧
    -- Greek BNs pattern like Romance BNs, not English BNs
    bnCanBeReferential greek = bnCanBeReferential romance := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 12: Bridge to Chierchia (1998) — DPParameter Derives NominalMapping
-- ============================================================================

/-- Map Longobardi's `DPParameter` to Chierchia's `NominalMapping`.

    Only `strongD` determines the mapping; `transparentAlpha` is irrelevant
    because it controls DP-internal word order (adjective position), not
    the argument/predicate denotation types available to nouns.

    - Strong D → nouns are predicates (need D for argumenthood) → `predOnly`
    - Weak D → nouns can be arguments without D → `argAndPred`

    `argOnly` (Chinese) is not addressed by Longobardi's parameters —
    it would require a separate parameter for classifier systems. -/
def toNominalMapping (dp : DPParameter) : NominalMapping :=
  if dp.strongD then .predOnly else .argAndPred

/-- Romance parameters yield Chierchia's `predOnly`. -/
theorem romance_is_predOnly : toNominalMapping romance = .predOnly := rfl

/-- English parameters yield Chierchia's `argAndPred`. -/
theorem english_is_argAndPred : toNominalMapping english = .argAndPred := rfl

/-- Greek parameters yield `predOnly` (same as Romance for BN semantics). -/
theorem greek_is_predOnly : toNominalMapping greek = .predOnly := rfl

-- ============================================================================
-- § 13: Bridge to Chierchia (1998) — Kind Denotation
-- ============================================================================

/-- English BNs can denote kinds (without overt D).
    Derived: weak D → `argAndPred` → `canDenoteKind` = true without D. -/
theorem english_bn_can_denote_kind :
    canDenoteKind (toNominalMapping english) false = true := rfl

/-- Italian BNs cannot denote kinds (without overt D).
    Derived: strong D → `predOnly` → `canDenoteKind` = false without D. -/
theorem italian_bn_cannot_denote_kind :
    canDenoteKind (toNominalMapping romance) false = false := rfl

/-- Italian definite plurals can denote kinds (with overt D).
    Even in a `predOnly` language, overt D restores kind denotation. -/
theorem italian_defpl_can_denote_kind :
    canDenoteKind (toNominalMapping romance) true = true := rfl

/-- Greek BNs cannot denote kinds.
    Same as Romance: strong D → `predOnly` → no kind without D. -/
theorem greek_bn_cannot_denote_kind :
    canDenoteKind (toNominalMapping greek) false = false := rfl

-- ============================================================================
-- § 14: Bridge to Carlson (1977) — English BNs as Proper Names of Kinds
-- ============================================================================

/-- @cite{longobardi-2001} (43) recovers @cite{carlson-1977}'s original
    insight: English generic BNs (outside characterizing environments)
    are kind-referential expressions — proper names of kinds.

    Carlson analyzed ALL bare plural readings as kind-denoting.
    Longobardi refines this: English BNs are AMBIGUOUS between
    kind-referential (Carlson's analysis) and quantificational
    (like Romance BNs). The referential reading is the one that
    behaves like proper names — rigid, scopeless, opaque-only.

    When a BN is referential, its semantics is @cite{carlson-1977}'s
    `barePluralTranslation`: λP.P{k}. -/
theorem english_bn_referential_is_carlson :
    .referential ∈ bnArgumentTypes english := by
  simp [bnArgumentTypes, bnCanBeReferential, english]

/-- Romance BNs are never referential — contra Carlson's universal claim
    but consistent with his observations about English specifically. -/
theorem romance_bn_never_referential :
    .referential ∉ bnArgumentTypes romance := by
  simp [bnArgumentTypes, bnCanBeReferential, romance]

/-- Referential BNs denote kinds via @cite{carlson-1977}'s λP.P{k}.

    The bare plural "dogs" denotes the kind d; applying any predicate P
    just evaluates P at d — no quantificational structure. This is what
    makes referential BNs scopeless and opaque-only: proper names don't
    take scope. -/
theorem referential_bn_semantics (Entity : Type) (k : Entity) (P : Entity → Bool) :
    barePluralTranslation k P = P k := rfl

/-- Kind-level predicates apply directly to a referential BN via
    @cite{carlson-1977}'s `genericDerivation`. This is why English BNs
    (which can be referential) appear with kind-level predicates
    ("Dogs are extinct") while Italian BNs (always quantificational) cannot. -/
theorem kind_level_via_carlson (Entity : Type) (k : Entity) (P : Entity → Bool) :
    genericDerivation k P = P k := rfl

/-- Existential readings of referential BNs arise via
    @cite{carlson-1977}'s `existentialDerivation`: the predicate
    introduces ∃ over stages, not the NP.

    "Dogs are in the yard" = ∃y[R(y,d) ∧ in-yard'(y)]

    The existential is part of the predicate semantics, which is
    why it always takes narrowest scope. -/
theorem existential_via_carlson (Entity : Type) (R : RealizationRel Entity)
    (k : Entity) (P : Entity → Bool) :
    existentialDerivation R k P = stageLevelPred Entity R P k := rfl

-- ============================================================================
-- § 15: Bridge to Fragment Data
-- ============================================================================

section FragmentBridges

/-- Longobardi's `romance` parameters correctly predict the Italian
    fragment's independently-declared mapping parameter. -/
theorem romance_matches_italian_fragment :
    toNominalMapping romance = Fragments.Italian.Nouns.italianMapping := rfl

/-- Longobardi's `english` parameters correctly predict the English
    fragment's independently-declared mapping parameter. -/
theorem english_matches_english_fragment :
    toNominalMapping english = Fragments.English.Nouns.englishMapping := rfl

/-- Longobardi's `greek` parameters correctly predict the Greek
    fragment's independently-declared mapping parameter. -/
theorem greek_matches_greek_fragment :
    toNominalMapping greek = Fragments.Greek.Nouns.greekMapping := rfl

/-- All three fragment bridges together: `DPParameter` *predicts*
    the independently-stipulated `NominalMapping` in each fragment.

    The derivation chain is:
    ```
    DPParameter (Longobardi syntax) → toNominalMapping → NominalMapping
    ```
    and each fragment independently declares the same `NominalMapping`,
    so the bridge theorems verify the prediction. -/
theorem all_fragment_mappings :
    toNominalMapping romance = Fragments.Italian.Nouns.italianMapping ∧
    toNominalMapping english = Fragments.English.Nouns.englishMapping ∧
    toNominalMapping greek = Fragments.Greek.Nouns.greekMapping := ⟨rfl, rfl, rfl⟩

/-- Longobardi's analysis explains WHY Italian bare plurals are not
    licensed: strong D means BNs are always quantificational variables,
    and these variables need licensing (characterizing environments for
    Gen, VP-internal position for Ex). General bare argument use is
    restricted because BNs cannot function as referential (kind) names. -/
theorem italian_bare_restriction_from_strong_d :
    bnAlwaysQuantificational romance = true ∧
    Fragments.Italian.Nouns.barePluralLicensed = false ∧
    Fragments.Italian.Nouns.bareSingularLicensed = false := ⟨rfl, rfl, rfl⟩

/-- English bare plurals are licensed (weak D allows referential BNs). -/
theorem english_bare_plurals_licensed :
    bnCanBeReferential english = true ∧
    Fragments.English.Nouns.barePluralLicensed = true := ⟨rfl, rfl⟩

/-- Greek bare plurals are not licensed (same as Italian: strong D). -/
theorem greek_bare_restriction_from_strong_d :
    bnAlwaysQuantificational greek = true ∧
    Fragments.Greek.Nouns.barePluralLicensed = false := ⟨rfl, rfl⟩

end FragmentBridges

-- ============================================================================
-- § 16: Bridge to KindReference Data
-- ============================================================================

/-- Longobardi's theory predicts the Italian vs English BP denotation
    data in `KindReference.lean`.

    English BPs: kind denotation available (weak D → referential OK)
    Italian bare plurals: kind denotation unavailable (strong D)
    Italian definite plurals: kind denotation available (overt D fills D) -/
theorem kind_reference_predictions :
    -- English BP can denote kind (= KindReference.englishBPKind.available)
    bnCanBeReferential english = true ∧
    -- Italian bare pl cannot denote kind (= KindReference.italianBarePlKind.available)
    bnCanBeReferential romance = false ∧
    -- Italian def pl can denote kind (overt D overrides strong D)
    canDenoteKind (toNominalMapping romance) true = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 17: The Full Parametric Table
-- ============================================================================

/-- Full parametric table (61) from @cite{longobardi-2001} with
    derived properties.

    | Language | Strong D | Transp. α | BN ref. | PN needs D | PN needs art. |
    |----------|----------|-----------|---------|------------|---------------|
    | Romance  |    +     |     +     |   no    |    yes     |      no       |
    | English  |    −     |     −     |   yes   |    no      |      no       |
    | Greek    |    +     |     −     |   no    |    yes     |      yes      |
    | Celtic   |    −     |     +     |   yes   |    no      |      no       |

    The "PN needs article" column is the only prediction that uses
    `transparentAlpha` directly, making the 2×2 table non-redundant. -/
theorem parametric_table :
    -- Romance: strong D, transparent α → BN quant only, PN needs D but not article
    bnCanBeReferential romance = false ∧
    pnRequiresOvertD romance = true ∧
    pnRequiresArticle romance = false ∧
    -- English: weak D, opaque α → BN can be referential, PN bare OK
    bnCanBeReferential english = true ∧
    pnRequiresOvertD english = false ∧
    pnRequiresArticle english = false ∧
    -- Greek: strong D, opaque α → BN quant only, PN needs article specifically
    bnCanBeReferential greek = false ∧
    pnRequiresOvertD greek = true ∧
    pnRequiresArticle greek = true ∧
    -- Celtic: weak D, transparent α → BN can be referential, PN bare OK
    bnCanBeReferential celtic = true ∧
    pnRequiresOvertD celtic = false ∧
    pnRequiresArticle celtic = false := by
  simp [bnCanBeReferential, pnRequiresOvertD, pnRequiresArticle,
        romance, english, greek, celtic]

/-- The 2×2 table has four distinct parameter combinations. -/
theorem four_language_types :
    romance ≠ english ∧ romance ≠ greek ∧ romance ≠ celtic ∧
    english ≠ greek ∧ english ≠ celtic ∧
    greek ≠ celtic := by
  simp [romance, english, greek, celtic, DPParameter.mk.injEq]

-- ============================================================================
-- § 18: Mapping Systems (45)-(46) — Reading Distribution
-- ============================================================================

/-- @cite{longobardi-2001} (45)-(46): The two mapping systems.

    English BNs have two sources of Ex/Gen ambiguity:
    1. Referential → Gen (in all environments, kind-level)
    2. Quantificational → Gen (characterizing) / Ex (S-level)

    Romance BNs have only one source:
    1. Quantificational → Gen (characterizing) / Ex (S-level) -/
inductive BNEnvironment where
  /-- Characterizing: habitual aspect, Q-adverb, I-level pred -/
  | characterizing
  /-- Episodic: S-level predicate with non-habitual aspect -/
  | episodic
  /-- Kind-level: predicate applies to kinds (extinct, widespread) -/
  | kindLevel
  deriving DecidableEq, Repr

/-- Whether a generic reading is available for a BN in a given environment. -/
def bnGenericAvailable (dp : DPParameter) (env : BNEnvironment) : Bool :=
  match env with
  | .characterizing => true  -- quantificational Gen always available
  | .episodic       => bnCanBeReferential dp  -- only via referential (kind name)
  | .kindLevel      => bnCanBeReferential dp  -- only via referential (kind name)

/-- English BNs are generic in all environments. -/
theorem english_bn_generic_everywhere :
    ∀ env, bnGenericAvailable english env = true := by
  intro env; cases env <;> rfl

/-- Romance BNs are generic only in characterizing environments. -/
theorem romance_bn_generic_characterizing_only :
    bnGenericAvailable romance .characterizing = true ∧
    bnGenericAvailable romance .episodic = false ∧
    bnGenericAvailable romance .kindLevel = false := ⟨rfl, rfl, rfl⟩

/-- The environments where English and Italian BNs contrast are exactly
    those requiring referential (kind) denotation. -/
theorem contrast_environments :
    ∀ env, bnGenericAvailable english env ≠ bnGenericAvailable romance env →
      (env = .episodic ∨ env = .kindLevel) := by
  intro env h
  cases env with
  | characterizing => simp [bnGenericAvailable] at h
  | episodic => left; rfl
  | kindLevel => right; rfl

-- ============================================================================
-- § 19: Bridge to Carlson (1977) — Predicate Level ↔ BN Environment
-- ============================================================================

/-- Maps @cite{carlson-1977}'s `PredicateLevel` to Longobardi's
    `BNEnvironment` for the purpose of determining whether referential
    (kind) denotation is needed.

    - Individual-level predicates (properties) create characterizing
      environments where quantificational Gen suffices
    - Stage-level predicates (states) in episodic aspect create
      environments where only referential BNs get generic readings -/
def predicateLevelToEnvironment : PredicateLevel → BNEnvironment
  | .individualLevel => .characterizing
  | .stageLevel       => .episodic

/-- Individual-level predicates yield characterizing environments
    where both English and Italian BNs get generic readings. -/
theorem ilp_yields_characterizing :
    predicateLevelToEnvironment .individualLevel = .characterizing := rfl

/-- Stage-level predicates in episodic aspect yield environments where
    only referential BNs (English) get generic readings. Italian BNs
    are stuck with the existential reading. -/
theorem slp_episodic_needs_referential :
    bnGenericAvailable english (predicateLevelToEnvironment .stageLevel) = true ∧
    bnGenericAvailable romance (predicateLevelToEnvironment .stageLevel) = false :=
  ⟨rfl, rfl⟩

/-- The full chain: @cite{carlson-1977}'s `PredicateLevel` determines
    `BNEnvironment`, which together with @cite{longobardi-2001}'s
    `DPParameter` determines whether a generic reading is available.

    | PredicateLevel    | Environment    | English BN Gen | Italian BN Gen |
    |-------------------|----------------|----------------|----------------|
    | individualLevel   | characterizing | yes            | yes            |
    | stageLevel        | episodic       | yes            | no             |
    | (kind-level pred) | kindLevel      | yes            | no             |

    The Italian/English contrast arises only in non-characterizing
    environments — exactly where @cite{carlson-1977}'s referential
    kind-denotation is needed. -/
theorem carlson_longobardi_integration :
    -- Individual-level: both languages get Gen
    (bnGenericAvailable english (predicateLevelToEnvironment .individualLevel) = true) ∧
    (bnGenericAvailable romance (predicateLevelToEnvironment .individualLevel) = true) ∧
    -- Stage-level (episodic): only English gets Gen (via referential kind denotation)
    (bnGenericAvailable english (predicateLevelToEnvironment .stageLevel) = true) ∧
    (bnGenericAvailable romance (predicateLevelToEnvironment .stageLevel) = false) :=
  ⟨rfl, rfl, rfl, rfl⟩

end Longobardi2001
