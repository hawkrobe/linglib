import Linglib.Core.Lexical.Binominal
import Linglib.Theories.Semantics.Lexical.Noun.Binominal
import Linglib.Theories.Syntax.ConstructionGrammar.Basic

/-!
# English Binominal Noun Phrases @cite{ten-wolde-2023}

Lexical entries for English nouns appearing in *of*-binominal constructions
(N₁ of N₂), classified by @cite{ten-wolde-2023}'s six-way taxonomy.

## Taxonomy

@cite{ten-wolde-2023} identifies six *of*-binominal constructions along
a grammaticalization cline:

1. **N+PP**: *the beast of the field* — N₁ heads, PP ascribes property
2. **Head-classifier**: *a cake of rye* — N₁ heads, PP classifies
3. **Pseudo-partitive**: *a glass of water* — N₁ quantizes, N₂ heads
4. **Evaluative BNP**: *that idiot of a doctor* — N₁ evaluates N₂
5. **Evaluative Modifier**: *a hell of a time* — [N₁ of a] modifies N₂
6. **Binominal Intensifier**: *a hell of a good time* — [N₁ of a] intensifies

## Integration

- Evaluative and quantizing-bridge semantics live in
  `Semantics.Lexical.Noun.Binominal` (cross-linguistic theory)
- The constructional network uses `ConstructionGrammar.Constructicon`
- The three-way `BinominalType` is shared with Spanish binominals
  via `Core.Lexical.Binominal`
-/

namespace Fragments.English.Binominals

open Core.Lexical.Binominal
open Semantics.Lexical.Noun.Binominal (ebnpSemantics quantizingToOfBinominal)

-- ═══════════════════════════════════════════════════════════════
-- § 1: N₁ Noun Semantic Class
-- ═══════════════════════════════════════════════════════════════

/-- Semantic class of the N₁ noun in an *of*-binominal.

N₁ nouns come from three broad semantic groups
(@cite{ten-wolde-2023}), each with different
grammaticalization behavior. -/
inductive N₁SemanticClass where
  /-- Inanimate concrete nouns: *cake*, *nub*, *breeze*, *husk*.
      These develop pseudo-partitive readings first, then (sometimes)
      evaluative uses. -/
  | inanimate
  /-- Animate nouns: *beast*, *snake*, *whale*.
      These generally skip pseudo-partitive, entering directly as
      head-classifiers → evaluative BNPs. (*snake* is a notable
      exception, with attested pseudo-partitive uses.) -/
  | animate
  /-- Abstract nouns: *hell*, *devil*, *idiot*, *angel*, *bitch*, *bastard*, *honey*.
      Includes religious/mythical beings and expletives that often
      refer to animate things. Already metaphorical; move quickly
      to evaluative and intensifier uses. -/
  | abstract
  deriving Repr, DecidableEq, BEq

/-- Inanimate N₁ nouns typically develop pseudo-partitive readings;
    animate and abstract ones do not. -/
def N₁SemanticClass.developsPseudoPartitive : N₁SemanticClass → Bool
  | .inanimate => true
  | .animate   => false
  | .abstract  => false

-- ═══════════════════════════════════════════════════════════════
-- § 2: English Binominal N₁ Entries
-- ═══════════════════════════════════════════════════════════════

/-- An English N₁ noun entry for *of*-binominal constructions.

Each entry records the constructions in which the noun participates
and its semantic class. The `constructions` field lists the
`OfBinominalType`s attested for this noun. -/
structure BinominalN₁Entry where
  /-- Surface form (e.g., "hell", "beast", "cake"). -/
  form : String
  /-- Plural form. -/
  formPlural : String
  /-- Semantic class. -/
  semanticClass : N₁SemanticClass
  /-- Which *of*-binominal constructions this noun appears in. -/
  constructions : List OfBinominalType
  /-- Does this noun have a reduced/fused intensifier form
      (e.g., *helluva*, *hella*, *beasta*)? -/
  hasReducedForm : Bool := false
  deriving Repr, BEq

-- Case study nouns from @cite{ten-wolde-2023}

def hell : BinominalN₁Entry where
  form := "hell"
  formPlural := "hells"
  semanticClass := .abstract
  constructions := [.nPP, .headClassifier, .pseudoPartitive,
                    .evaluative, .evaluativeModifier, .binominalIntensifier]
  hasReducedForm := true  -- helluva, hella

def beast : BinominalN₁Entry where
  form := "beast"
  formPlural := "beasts"
  semanticClass := .animate
  constructions := [.nPP, .headClassifier,
                    .evaluative, .evaluativeModifier, .binominalIntensifier]

def cake : BinominalN₁Entry where
  form := "cake"
  formPlural := "cakes"
  semanticClass := .inanimate
  constructions := [.nPP, .headClassifier, .pseudoPartitive, .evaluative]

-- Corpus study nouns from @cite{ten-wolde-2023}

def whale : BinominalN₁Entry where
  form := "whale"
  formPlural := "whales"
  semanticClass := .animate
  constructions := [.nPP, .headClassifier,
                    .evaluative, .evaluativeModifier, .binominalIntensifier]

def bitch : BinominalN₁Entry where
  form := "bitch"
  formPlural := "bitches"
  semanticClass := .abstract
  constructions := [.nPP, .evaluative, .evaluativeModifier, .binominalIntensifier]

def nub : BinominalN₁Entry where
  form := "nub"
  formPlural := "nubs"
  semanticClass := .inanimate
  constructions := [.nPP, .headClassifier, .pseudoPartitive, .evaluative]

def breeze : BinominalN₁Entry where
  form := "breeze"
  formPlural := "breezes"
  semanticClass := .inanimate
  constructions := [.nPP, .headClassifier, .pseudoPartitive, .evaluative]

def husk : BinominalN₁Entry where
  form := "husk"
  formPlural := "husks"
  semanticClass := .inanimate
  constructions := [.nPP, .headClassifier, .pseudoPartitive, .evaluative]

def snake : BinominalN₁Entry where
  form := "snake"
  formPlural := "snakes"
  semanticClass := .animate
  constructions := [.nPP, .headClassifier, .pseudoPartitive, .evaluative]

-- Common evaluative N₁ nouns

def idiot : BinominalN₁Entry where
  form := "idiot"
  formPlural := "idiots"
  semanticClass := .abstract
  constructions := [.evaluative]

def angel : BinominalN₁Entry where
  form := "angel"
  formPlural := "angels"
  semanticClass := .abstract
  constructions := [.evaluative]

def gem : BinominalN₁Entry where
  form := "gem"
  formPlural := "gems"
  semanticClass := .inanimate
  constructions := [.evaluative, .evaluativeModifier]

def allN₁Entries : List BinominalN₁Entry :=
  [hell, beast, cake, whale, bitch, nub, breeze, husk, snake, idiot, angel, gem]

-- ═══════════════════════════════════════════════════════════════
-- § 3: Constructional Network
-- ═══════════════════════════════════════════════════════════════

open ConstructionGrammar

/-- The six *of*-binominal constructions as CxG `Construction` entries
    (@cite{ten-wolde-2023}). -/
def nPPConstruction : Construction where
  name := "N+PP"
  form := "[Det][N][of][Det][N]"
  meaning := "N₁ denotes a referent, PP ascribes a property onto the head"
  specificity := .partiallyOpen

def headClassifierConstruction : Construction where
  name := "Head-Classifier"
  form := "[Det][N][of][N]"
  meaning := "Construction denotes a referent, PP classifies head"
  specificity := .partiallyOpen

def pseudoPartitiveConstruction : Construction where
  name := "Pseudo-partitive"
  form := "[Det][N][of][N]"
  meaning := "N₁ quantizes, N₂ denotes measured substance"
  specificity := .partiallyOpen

def ebnpConstruction : Construction where
  name := "Evaluative BNP"
  form := "[Det₁][N₁][of][a][N₂]"
  meaning := "N₁ ascribes evaluative property to N₂ referent"
  specificity := .partiallyOpen

def emConstruction : Construction where
  name := "Evaluative Modifier"
  form := "[Det₁][N₁ of (a)][N₂]"
  meaning := "[N₁ of a] is complex modifier, speaker evaluation of N₂"
  specificity := .partiallyOpen

def biConstruction : Construction where
  name := "Binominal Intensifier"
  form := "[N₁ of (a)][Adj/Quant][N₂]"
  meaning := "[N₁ of a] intensifies following adjective or quantifier"
  specificity := .partiallyOpen

/-- The *of*-binominal constructional network (@cite{ten-wolde-2023}).

All links on the grammaticalization path are **metaphorical** (M) at the
micro-construction level (Figs 8.7, 8.9, 8.11, 8.13): each step involves
a conceptual metaphor that extends the source construction's meaning
to a new domain. Each construction also has a taxonomic link to the
schematic N+PP mother node at a higher level (not modeled here). -/
def ofBinominalNetwork : Constructicon where
  constructions :=
    [ nPPConstruction, headClassifierConstruction, pseudoPartitiveConstruction
    , ebnpConstruction, emConstruction, biConstruction ]
  links :=
    [ -- Metaphorical: N+PP → Head-Classifier (Fig 8.7)
      { parent := "N+PP", child := "Head-Classifier"
        mode := .metaphorical
        sharedProperties := ["[Det][N][of] frame", "N₁ heads"]
        overriddenProperties := ["PP classifies → of is linker", "no Det₂"] }
    , -- Taxonomic: N+PP → Pseudo-partitive
      { parent := "N+PP", child := "Pseudo-partitive"
        mode := .normal
        sharedProperties := ["[Det][N][of] frame"]
        overriddenProperties := ["head: N₁ → N₂"] }
    , -- Metaphorical: Head-Classifier → EBNP (Fig 8.9)
      { parent := "Head-Classifier", child := "Evaluative BNP"
        mode := .metaphorical
        sharedProperties := ["N₁ classifies/evaluates N₂"]
        overriddenProperties := ["head: N₁ → N₂", "N₁ evaluative"] }
    , -- Metaphorical: EBNP → EM (Fig 8.11)
      { parent := "Evaluative BNP", child := "Evaluative Modifier"
        mode := .metaphorical
        sharedProperties := ["N₂ is semantic head", "N₁ evaluative"]
        overriddenProperties := ["N₁ frozen singular", "N₁ semantics bleached"] }
    , -- Metaphorical: EM → BI (Fig 8.13)
      { parent := "Evaluative Modifier", child := "Binominal Intensifier"
        mode := .metaphorical
        sharedProperties := ["[N₁ of a] chunk", "N₁ nonreferential"]
        overriddenProperties := ["[N of a] shifts into AdjP", "N₁ intensifies Adj"] }
    ]

/-- The network has 6 constructions. -/
theorem network_size : ofBinominalNetwork.constructions.length = 6 := rfl

/-- The network has 5 inheritance links. -/
theorem network_links : ofBinominalNetwork.links.length = 5 := rfl

-- ═══════════════════════════════════════════════════════════════
-- § 4: Per-Entry Verification
-- ═══════════════════════════════════════════════════════════════

/-- *hell* participates in all six constructions (most grammaticalized). -/
theorem hell_all_six : hell.constructions.length = 6 := rfl

/-- *hell* has a reduced form (helluva, hella). -/
theorem hell_has_reduced : hell.hasReducedForm = true := rfl

/-- *idiot* appears only in evaluative BNPs. -/
theorem idiot_evaluative_only : idiot.constructions = [.evaluative] := rfl

/-- *beast* has no pseudo-partitive (typical for animate N₁ nouns). -/
theorem beast_no_pseudopartitive :
    beast.constructions.elem .pseudoPartitive = false := by native_decide

/-- *snake* is an exceptional animate noun with pseudo-partitive attestations. -/
theorem snake_pseudopartitive : snake.constructions.elem .pseudoPartitive = true := by native_decide

/-- All inanimate N₁ nouns develop pseudo-partitive readings. -/
theorem cake_pseudopartitive : cake.constructions.elem .pseudoPartitive = true := by native_decide
theorem nub_pseudopartitive : nub.constructions.elem .pseudoPartitive = true := by native_decide
theorem breeze_pseudopartitive : breeze.constructions.elem .pseudoPartitive = true := by native_decide
theorem husk_pseudopartitive : husk.constructions.elem .pseudoPartitive = true := by native_decide

-- ═══════════════════════════════════════════════════════════════
-- § 5: Cross-Linguistic Bridge (English ↔ Spanish)
-- ═══════════════════════════════════════════════════════════════

/-- English pseudo-partitive N₁ nouns correspond to Spanish
    pseudo-partitive/quantificational binominals. -/
theorem english_pseudopartitive_matches_spanish :
    BinominalType.pseudoPartitive.toOfBinominalType = .pseudoPartitive ∧
    BinominalType.quantificational.toOfBinominalType = .pseudoPartitive := by
  constructor <;> rfl

/-- English evaluative BNPs correspond to Spanish qualitative binominals. -/
theorem english_evaluative_matches_spanish :
    BinominalType.qualitative.toOfBinominalType = .evaluative := rfl

end Fragments.English.Binominals
