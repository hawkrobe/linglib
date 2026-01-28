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
import Linglib.Fragments.QUD

-- Price × Affect meaning space
def scenario := QUD.priceAffect

#eval RSA.L1_qud scenario .million
-- Infers QUD was probably "affect" (hyperbole interpretation)
```

## References

- Kao, Wu, Bergen & Goodman (2014). Nonliteral understanding of number words.
- Kao & Goodman (2015). Metaphor and hyperbole chapter.
-/

import Linglib.Theories.RSA.Core.Basic
import Mathlib.Data.Rat.Defs

namespace QUD

-- ============================================================================
-- Generic Multi-Dimensional Meanings
-- ============================================================================

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

-- ============================================================================
-- Price × Affect Domain (Kao et al. 2014)
-- ============================================================================

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
  [Price.low, .medium, .high].flatMap fun p =>
    [Affect.neutral, .annoyed, .amazed].map fun a => (p, a)

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

-- ============================================================================
-- Utterances for Price Domain
-- ============================================================================

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

-- ============================================================================
-- Scenario Builders
-- ============================================================================

/--
Price × Affect scenario with QUDs.

Uses `RSAScenario.qudBool` for QUD-sensitive speaker.
-/
def priceAffect : RSAScenario :=
  RSAScenario.qudBool
    [PriceUtt.low, .medium, .high, .million, .silent]
    allPriceAffect
    [PriceAffectQUD.price, .affect, .both]
    priceAffectMeaning
    priceAffectProject

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
    (worldPrior : W → ℚ := fun _ => 1)
    (qudPrior : Q → ℚ := fun _ => 1)
    : RSAScenario :=
  RSAScenario.qudBool utterances worlds quds meaning project worldPrior qudPrior

-- ============================================================================
-- Binary Dimension Pattern
-- ============================================================================

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
  d.dim1Values.flatMap fun x => d.dim2Values.map fun y => (x, y)

-- ============================================================================
-- Examples
-- ============================================================================

-- Hyperbole scenario
#eval RSA.L1_world priceAffect .million
-- "million" → probably high affect world

#eval RSA.L1_qud priceAffect .million
-- "million" → probably QUD was "affect" (hyperbole interpretation)

-- Compare to literal utterance
#eval RSA.L1_qud priceAffect .medium
-- "medium" → probably QUD was "price" (literal interpretation)

end QUD
