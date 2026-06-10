import Linglib.Semantics.Quantification.BinominalDefs
import Linglib.Semantics.Quantification.Binominal
import Linglib.Syntax.ConstructionGrammar.Basic

/-!
# English Binominal Noun Phrases [ten-wolde-2023]

Lexical entries for English nouns appearing in *of*-binominal constructions
(N₁ of N₂), classified by [ten-wolde-2023]'s six-way taxonomy.

## Taxonomy

[ten-wolde-2023] identifies six *of*-binominal constructions along
a grammaticalization cline:

1. **N+PP**: *the beast of the field* — N₁ heads, PP ascribes property
2. **Head-classifier**: *a cake of rye* — N₁ heads, PP classifies
3. **Pseudo-partitive**: *a glass of water* — N₁ quantizes, N₂ heads
4. **Evaluative BNP**: *that idiot of a doctor* — N₁ evaluates N₂
5. **Evaluative Modifier**: *a hell of a time* — [N₁ of a] modifies N₂
6. **Binominal Intensifier**: *a hell of a good time* — [N₁ of a] intensifies

## Integration

- Evaluative and quantizing-bridge semantics live in
  `Semantics.Quantification.Binominal` (cross-linguistic theory)
- The constructional network uses `ConstructionGrammar.Constructicon`
- The three-way `BinominalType` is shared with Spanish binominals
  via `Semantics.Quantification.Binominal`
-/

namespace English.Binominals

open Semantics.Quantification.Binominal
open Semantics.Quantification.Binominal (ebnpSemantics quantizingToOfBinominal)

-- ═══════════════════════════════════════════════════════════════
-- § 1: N₁ Noun Semantic Class
-- ═══════════════════════════════════════════════════════════════

/-- Semantic class of the N₁ noun in an *of*-binominal.

N₁ nouns come from three broad semantic groups
([ten-wolde-2023]), each with different
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
  deriving Repr, DecidableEq

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
      (e.g., *helluva*, *hella*, *whaleuva*)? -/
  hasReducedForm : Bool := false
  deriving Repr, BEq

-- Case study nouns from [ten-wolde-2023]

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

-- Corpus study nouns from [ten-wolde-2023]

def whale : BinominalN₁Entry where
  form := "whale"
  formPlural := "whales"
  semanticClass := .animate
  constructions := [.nPP, .headClassifier,
                    .evaluative, .evaluativeModifier, .binominalIntensifier]
  hasReducedForm := true  -- whaleuva (Figs 8.10, 8.12)

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
    ([ten-wolde-2023]). -/
def nPPConstruction : Construction where
  name := "N+PP"
  form :=
    [ { filler := .open_ .DET }
    , { filler := .open_ .NOUN, role := some "head", isHead := true }
    , { filler := .fixed "of" }
    , { filler := .open_ .DET }
    , { filler := .open_ .NOUN, role := some "property" } ]
  meaning := "N₁ denotes a referent, PP ascribes a property onto the head"

def headClassifierConstruction : Construction where
  name := "Head-Classifier"
  form :=
    [ { filler := .open_ .DET }
    , { filler := .open_ .NOUN, role := some "head", isHead := true }
    , { filler := .fixed "of" }
    , { filler := .open_ .NOUN, role := some "classifier" } ]
  meaning := "Construction denotes a referent, PP classifies head"

def pseudoPartitiveConstruction : Construction where
  name := "Pseudo-partitive"
  form :=
    [ { filler := .open_ .DET }
    , { filler := .open_ .NOUN, role := some "quantizer", isHead := true }
    , { filler := .fixed "of" }
    , { filler := .open_ .NOUN, role := some "substance" } ]
  meaning := "N₁ quantizes, N₂ denotes measured substance"

def ebnpConstruction : Construction where
  name := "Evaluative BNP"
  form :=
    [ { filler := .open_ .DET }
    , { filler := .open_ .NOUN, role := some "evaluation" }
    , { filler := .fixed "of" }
    , { filler := .fixed "a" }
    , { filler := .open_ .NOUN, role := some "referent", isHead := true } ]
  meaning := "N₁ ascribes evaluative property to N₂ referent"

def emConstruction : Construction where
  name := "Evaluative Modifier"
  form :=  -- optional "a" elided
    [ { filler := .open_ .DET }
    , { filler := .open_ .NOUN, role := some "evaluation" }
    , { filler := .fixed "of" }
    , { filler := .open_ .NOUN, role := some "head", isHead := true } ]
  meaning := "[N₁ of a] is complex modifier, speaker evaluation of N₂"

def biConstruction : Construction where
  name := "Binominal Intensifier"
  form :=  -- optional "a" elided
    [ { filler := .open_ .NOUN, role := some "intensifier" }
    , { filler := .fixed "of" }
    , { filler := .open_ .ADJ, role := some "intensified" }
    , { filler := .open_ .NOUN, role := some "head", isHead := true } ]
  meaning := "[N₁ of a] intensifies following adjective or quantifier"

/-- The simple NP construction ([ten-wolde-2023] §8.4).

The simple NP [[Det] (Mod) [N]] plays a key role in the constructional
network: the head-classifier shares a polysemy link with the classifier
premodifier in the NP, and the evaluative constructions share polysemy
links with evaluative/intensifier premodifiers in the NP. -/
def simpleNPConstruction : Construction where
  name := "Simple NP"
  form :=  -- optional premodifier elided
    [ { filler := .open_ .DET }
    , { filler := .open_ .NOUN, role := some "head", isHead := true } ]
  meaning := "denotes a referent, premodifier ascribes property to head"

/-- The adjective phrase construction, linked to BI ([ten-wolde-2023] Fig 8.13). -/
def adjPhraseConstruction : Construction where
  name := "AP"
  form :=
    [ { filler := .open_ .ADV, role := some "intensifier" }
    , { filler := .open_ .ADJ, role := some "head", isHead := true } ]
  meaning := "intensifier emphasizes the following adjective"

/-- The *of*-binominal constructional network ([ten-wolde-2023]).

All links on the grammaticalization path are **metaphorical** (M) at the
micro-construction level (Figs 8.7, 8.9, 8.11, 8.13): each step involves
a conceptual metaphor that extends the source construction's meaning
to a new domain. Each construction also has a taxonomic link to the
schematic N+PP mother node at a higher level (not modeled here). -/
def ofBinominalNetwork : Constructicon where
  constructions :=
    [ nPPConstruction, headClassifierConstruction, pseudoPartitiveConstruction
    , ebnpConstruction, emConstruction, biConstruction
    , simpleNPConstruction, adjPhraseConstruction ]
  links :=
    [ -- Metaphorical: N+PP → Head-Classifier (Fig 8.7)
      { parent := "N+PP", child := "Head-Classifier"
        mode := .normal
        linkType := some .metaphorical
        sharedProperties := ["[Det][N][of] frame", "N₁ heads"]
        overriddenProperties := ["PP classifies → of is linker", "no Det₂"] }
    , -- NOTE: This link is NOT in [ten-wolde-2023]'s network figures
      -- (Figs 8.7–8.13), which focus on the main evaluative path. Pseudo-partitive
      -- is a side branch, not on the N+PP → HC → EBNP → EM → BI path.
      -- Included here for structural completeness of the six-type taxonomy.
      { parent := "N+PP", child := "Pseudo-partitive"
        mode := .normal
        linkType := some .polysemy
        sharedProperties := ["[Det][N][of] frame"]
        overriddenProperties := ["head: N₁ → N₂", "N₁ quantizes"] }
    , -- Metaphorical: Head-Classifier → EBNP (Fig 8.9)
      { parent := "Head-Classifier", child := "Evaluative BNP"
        mode := .normal
        linkType := some .metaphorical
        sharedProperties := ["N₁ classifies/evaluates N₂"]
        overriddenProperties := ["head: N₁ → N₂", "N₁ evaluative"] }
    , -- Polysemy: Head-Classifier → Simple NP (Fig 8.7)
      -- The classifier premodifier in the NP and the head-classifier share
      -- semantic function; this competition drives reanalysis.
      { parent := "Head-Classifier", child := "Simple NP"
        mode := .normal
        linkType := some .polysemy
        sharedProperties := ["classifier function"]
        overriddenProperties := ["[N of N] → [classifier N]"] }
    , -- Metaphorical: EBNP → EM (Fig 8.11)
      { parent := "Evaluative BNP", child := "Evaluative Modifier"
        mode := .normal
        linkType := some .metaphorical
        sharedProperties := ["N₂ is semantic head", "N₁ evaluative"]
        overriddenProperties := ["N₁ frozen singular", "N₁ semantics bleached"] }
    , -- Polysemy: EBNP → Simple NP (Fig 8.9)
      -- EBNP shares evaluative premodification function with the NP:
      -- *a beast of a boy* ↔ *a beastly boy*.
      { parent := "Evaluative BNP", child := "Simple NP"
        mode := .normal
        linkType := some .polysemy
        sharedProperties := ["N₁ ascribes evaluative property to head"]
        overriddenProperties := ["[N of a N] → [Adj N]"] }
    , -- Metaphorical: EM → BI (Fig 8.13)
      { parent := "Evaluative Modifier", child := "Binominal Intensifier"
        mode := .normal
        linkType := some .metaphorical
        sharedProperties := ["[N₁ of a] chunk", "N₁ nonreferential"]
        overriddenProperties := ["[N of a] shifts into AdjP", "N₁ intensifies Adj"] }
    , -- Polysemy: EM → Simple NP (Fig 8.11)
      -- EM functions as subjective descriptive modifier in the NP:
      -- *a hell of a game* ↔ *a hellish game*.
      { parent := "Evaluative Modifier", child := "Simple NP"
        mode := .normal
        linkType := some .polysemy
        sharedProperties := ["speaker evaluation of referent"]
        overriddenProperties := ["[N of a] → evaluative premodifier"] }
    , -- Polysemy: BI → AP (Fig 8.13)
      -- BI's [N of a] chunk functions as an adjective intensifier:
      -- *a hell of a good time* ↔ *a hella good time*.
      { parent := "Binominal Intensifier", child := "AP"
        mode := .normal
        linkType := some .polysemy
        sharedProperties := ["intensifier function"]
        overriddenProperties := ["[N of a] → degree intensifier in AdjP"] }
    ]

/-- The network has 8 constructions (6 of-binominal + simple NP + AP). -/
theorem network_size : ofBinominalNetwork.constructions.length = 8 := rfl

/-- The network has 9 links (4 grammaticalization + 1 N+PP polysemy + 4 polysemy to NP/AP). -/
theorem network_links : ofBinominalNetwork.links.length = 9 := rfl

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

end English.Binominals
