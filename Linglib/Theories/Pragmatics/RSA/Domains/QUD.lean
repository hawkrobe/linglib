/-
# QUD-Sensitive RSA Fragments

Building blocks for QUD-sensitive RSA scenarios (hyperbole, metaphor).

## Components

- `Dimension`: A meaning dimension (price, affect, etc.)
- `QUD`: Which dimension(s) the speaker cares about
- `qudProject`: Equivalence under a QUD
- `qudScenario`: Builder for QUD-sensitive scenarios

## The Pattern

QUD-sensitive RSA involves:
1. **Multi-dimensional meanings**: World = Dim₁ × Dim₂ × ...
2. **QUDs**: Which dimensions matter for communication
3. **Projection**: Worlds equivalent if they match on QUD-relevant dimensions

Example: Hyperbole ("It cost a million dollars")
- Meaning space: Price × Affect
- QUD "affect": only affect dimension matters
- Under QUD "affect", literally false but affectively-appropriate utterances work

## Usage

```lean
import Linglib.Theories.Pragmatics.RSA.Domains.QUD

-- Price × Affect meaning space
def scenario := QUD.priceAffect

#eval RSAL.L1_qud scenario .million
-- Infers QUD was probably "affect" (hyperbole interpretation)
```

## References

- Kao, Wu, Bergen & Goodman (2014). Nonliteral understanding of number words.
- Kao & Goodman (2015). Metaphor and hyperbole chapter.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Mathlib.Data.Rat.Defs

namespace RSA.Domains.QUD

-- Generic Multi-Dimensional Meanings

/--
A QUD specifies which dimensions of meaning are relevant.

When QUD = "affect", two worlds are equivalent if they have the same affect,
regardless of other dimensions (like exact price).
-/
structure Goal (dims : List String) where
  /-- Which dimensions this goal cares about -/
  relevantDims : List String
  /-- Name for display -/
  name : String := ""
  deriving Repr, DecidableEq, BEq

-- Price × Affect Domain (Kao et al. 2014)

/-- Price levels -/
inductive Price where
  | low      -- e.g., $50
  | medium   -- e.g., $500
  | high     -- e.g., $10,000
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Affect states -/
inductive Affect where
  | neutral
  | annoyed
  | amazed
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Full meaning: Price × Affect -/
abbrev PriceAffect := Price × Affect

instance : BEq PriceAffect := instBEqProd

/-- All Price × Affect worlds -/
def allPriceAffect : List PriceAffect :=
  [Price.low, .medium, .high].flatMap λ p =>
    [Affect.neutral, .annoyed, .amazed].map λ a => (p, a)

/-- QUD for Price × Affect domain -/
inductive PriceAffectQUD where
  | price   -- care about exact price
  | affect  -- care about affect (allows hyperbole)
  | both    -- care about both (strict)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- QUD projection: are two worlds equivalent under this QUD? -/
def priceAffectProject (q : PriceAffectQUD) (w1 w2 : PriceAffect) : Bool :=
  match q with
  | .price => w1.1 == w2.1          -- same price
  | .affect => w1.2 == w2.2         -- same affect
  | .both => w1 == w2               -- exact match

-- Utterances for Price Domain

/-- Price utterances (can be literal or hyperbolic) -/
inductive PriceUtt where
  | low       -- "fifty dollars"
  | medium    -- "five hundred dollars"
  | high      -- "ten thousand dollars"
  | million   -- "a million dollars" (hyperbolic)
  | silent    -- say nothing
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Literal semantics: does utterance match price? -/
def priceLiteral (u : PriceUtt) (p : Price) : Bool :=
  match u, p with
  | .low, .low => true
  | .medium, .medium => true
  | .high, .high => true
  | .million, _ => false  -- literally false for all real prices!
  | .silent, _ => true
  | _, _ => false

/--
Extended semantics: literal price + affect congruence.

"A million dollars" is literally false but conveys high affect.
-/
def priceAffectMeaning (w : PriceAffect) (u : PriceUtt) : Bool :=
  let (p, _) := w
  match u with
  | .low => p == .low
  | .medium => p == .medium
  | .high => p == .high
  | .million => false  -- literally false for all worlds
  | .silent => true

/-- Arousal/affect associated with utterance (for QUD projection) -/
def uttArousal (u : PriceUtt) : Affect :=
  match u with
  | .low => .neutral
  | .medium => .neutral
  | .high => .annoyed
  | .million => .amazed  -- hyperbolic = high arousal
  | .silent => .neutral

-- Scenario Builders

/--
A list-based QUD scenario for #eval demonstrations.
-/
structure QUDScenario where
  /-- Utterance type -/
  Utterance : Type
  /-- World type -/
  World : Type
  /-- QUD type -/
  QUD : Type
  /-- Utterances list -/
  utterances : List Utterance
  /-- Worlds list -/
  worlds : List World
  /-- QUDs list -/
  quds : List QUD
  /-- Meaning function -/
  meaning : World → Utterance → Bool
  /-- QUD projection -/
  project : QUD → World → World → Bool
  /-- World prior -/
  worldPrior : World → ℚ := λ _ => 1
  /-- QUD prior -/
  qudPrior : QUD → ℚ := λ _ => 1
  /-- BEq instances -/
  [uttBEq : BEq Utterance]
  [worldBEq : BEq World]
  [qudBEq : BEq QUD]

attribute [instance] QUDScenario.uttBEq QUDScenario.worldBEq QUDScenario.qudBEq

/-- L1 world distribution for QUD scenario -/
def QUDScenario.L1_world (S : QUDScenario) (u : S.Utterance) : List (S.World × ℚ) :=
  let φ := λ _ _ (u : S.Utterance) (w : S.World) => boolToRat (S.meaning w u)
  RSA.Eval.L1_world S.utterances S.worlds [()] [()] [()] S.quds
    φ S.worldPrior (λ _ => 1) (λ _ => 1) (λ _ => 1) S.qudPrior
    (λ _ _ => 1) (λ q w w' => S.project q w w') (λ _ => 0) 1 u

/-- L1 QUD distribution for QUD scenario -/
def QUDScenario.L1_qud (S : QUDScenario) (u : S.Utterance) : List (S.QUD × ℚ) :=
  let φ := λ _ _ (u : S.Utterance) (w : S.World) => boolToRat (S.meaning w u)
  -- Full joint computation, then marginalize
  let tuples := S.worlds.flatMap λ w =>
    S.quds.map λ q => (w, q)
  let scores := tuples.map λ (w, q) =>
    let prior := S.worldPrior w * S.qudPrior q
    let s1 := RSA.Eval.S1 S.utterances S.worlds φ S.worldPrior
      (λ _ _ => 1) (λ q' w1 w2 => S.project q' w1 w2) (λ _ => 0) 1 w () () () q
    let s1Score := RSA.Eval.getScore s1 u
    ((w, q), prior * s1Score)
  let normalized := RSA.Eval.normalize scores
  -- Marginalize over worlds
  S.quds.map λ q =>
    let qScores := normalized.filter (λ ((_, q'), _) => q' == q) |>.map (·.2)
    (q, RSA.Eval.sumScores qScores)

/--
Price × Affect scenario with QUDs.

Uses list-based API for #eval demonstrations.
-/
def priceAffect : QUDScenario where
  Utterance := PriceUtt
  World := PriceAffect
  QUD := PriceAffectQUD
  utterances := [PriceUtt.low, .medium, .high, .million, .silent]
  worlds := allPriceAffect
  quds := [PriceAffectQUD.price, .affect, .both]
  meaning := priceAffectMeaning
  project := priceAffectProject

/--
Generic QUD scenario builder.

For custom meaning spaces with QUD-sensitive projection.
-/
def scenario {U W Q : Type} [BEq U] [BEq W] [BEq Q]
    (utterances : List U)
    (worlds : List W)
    (quds : List Q)
    (meaning : W → U → Bool)
    (project : Q → W → W → Bool)
    (worldPrior : W → ℚ := λ _ => 1)
    (qudPrior : Q → ℚ := λ _ => 1)
    : QUDScenario where
  Utterance := U
  World := W
  QUD := Q
  utterances := utterances
  worlds := worlds
  quds := quds
  meaning := meaning
  project := project
  worldPrior := worldPrior
  qudPrior := qudPrior

-- Binary Dimension Pattern

/--
Common pattern: two dimensions where QUD selects one.

Many phenomena fit this: Price × Affect, Precision × Quantity, Form × Meaning.
-/
structure BinaryDomain (D1 D2 : Type) where
  dim1Values : List D1
  dim2Values : List D2
  dim1Name : String := "dim1"
  dim2Name : String := "dim2"

/-- QUD for binary domain -/
inductive BinaryQUD where
  | first   -- care about first dimension
  | second  -- care about second dimension
  | both    -- care about both
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Projection for binary domain -/
def binaryProject {D1 D2 : Type} [BEq D1] [BEq D2]
    (q : BinaryQUD) (w1 w2 : D1 × D2) : Bool :=
  match q with
  | .first => w1.1 == w2.1
  | .second => w1.2 == w2.2
  | .both => w1 == w2

/-- All worlds for binary domain -/
def BinaryDomain.allWorlds {D1 D2 : Type} (d : BinaryDomain D1 D2) : List (D1 × D2) :=
  d.dim1Values.flatMap λ x => d.dim2Values.map λ y => (x, y)

-- Examples

-- Hyperbole scenario
#eval priceAffect.L1_world .million
-- "million" → probably high affect world

#eval priceAffect.L1_qud .million
-- "million" → probably QUD was "affect" (hyperbole interpretation)

-- Compare to literal utterance
#eval priceAffect.L1_qud .medium
-- "medium" → probably QUD was "price" (literal interpretation)

end RSA.Domains.QUD
