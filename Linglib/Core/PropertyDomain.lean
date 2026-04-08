/-!
# Property Domains for Adjective Dimensions

@cite{giles-etal-2026} @cite{wolfe-horowitz-2017}

Structured replacement for raw `String` dimension labels in adjective entries.
Connects adjective semantics to the perceptual noise infrastructure in
`RSA.Core.Noise` via `PropertyDomain.noiseDiscrimination`.

## Design

A `Dimension` pairs a human-readable name with a `PropertyDomain` that
classifies the perceptual channel. Smart constructors cover all dimensions
used across the English adjective fragments.

## Perceptual Grounding

The first four domains (`color`, `size`, `material`, `orientation`) have
established relationships to perceptual discriminability:

- **Colour and orientation** are privileged features in visual search
  (@cite{wolfe-horowitz-2017}): they guide pre-attentive filtering and
  produce pop-out effects.
- **Size** is privileged but weaker than colour/orientation.
- **Material** is not visually privileged; its perception often requires
  auditory or haptic verification (@cite{giles-etal-2026}).
-/

namespace Core

-- ═══════════════════════════════════════════
-- Property Domains
-- ═══════════════════════════════════════════

/-- Broad perceptual/cognitive domain that a gradable dimension belongs to.
    The first four (`color`, `size`, `material`, `orientation`) have
    established noise parameters in `RSA.Noise`; the rest are classified
    but not yet parameterised. -/
inductive PropertyDomain where
  | color
  | size
  | material
  | orientation
  | sensory
  | evaluative
  | psychological
  | state
  deriving Repr, DecidableEq, Inhabited

/-- A named dimension classified by its perceptual domain. -/
structure Dimension where
  name : String
  domain : PropertyDomain
  deriving Repr

instance : BEq Dimension where
  beq d1 d2 := d1.name == d2.name && d1.domain == d2.domain

instance : DecidableEq Dimension :=
  fun d1 d2 =>
    if h1 : d1.name = d2.name then
      if h2 : d1.domain = d2.domain then
        .isTrue (by cases d1; cases d2; simp_all)
      else
        .isFalse (fun h => h2 (by cases h; rfl))
    else
      .isFalse (fun h => h1 (by cases h; rfl))

instance : Inhabited Dimension := ⟨⟨"", .state⟩⟩

-- ═══════════════════════════════════════════
-- Antonymy Type
-- ═══════════════════════════════════════════

/--
Types of antonymy for gradable adjective pairs.

**Contradictories** (e.g., "clean" / "dirty"):
- Cannot both be true AND cannot both be false
- Negation of one entails the other: not clean ⟹ dirty
- No extension gap between the two standards

**Contraries** (e.g., "tall" / "short", "large" / "small"):
- Cannot both be true BUT can both be false
- Negation of one does NOT entail the other: not large ⟹/⟹ small
- Extension gap between the two standards

References:
- @cite{cruse-1986}. Lexical Semantics.
- @cite{horn-1989}. A Natural History of Negation.
- @cite{kennedy-2007}. Vagueness and Grammar.
-/
inductive NegationType where
  | contradictory
  | contrary
  deriving Repr, DecidableEq

-- ═══════════════════════════════════════════
-- Evaluative Valence
-- ═══════════════════════════════════════════

/--
Evaluative valence of a gradable predicate.

Distinct from scalar polarity (positive/negative scale direction):
- **positive**: denotes a good/desirable property (pleasant, nice, good)
- **negative**: denotes a bad/undesirable property (horrible, terrible, bad)
- **neutral**: no inherent evaluative content (usual, possible, tall)

@cite{nouwen-2024} argues that evaluative valence, not scalar polarity,
determines the intensifier degree class (Goldilocks effect):
negative-evaluative bases yield H-degree intensifiers,
positive-evaluative bases yield M-degree intensifiers.
-/
inductive EvaluativeValence where
  | positive
  | negative
  | neutral
  deriving Repr, DecidableEq

-- ═══════════════════════════════════════════
-- Smart Constructors
-- ═══════════════════════════════════════════

-- Size domain
def Dimension.height : Dimension := ⟨"height", .size⟩
def Dimension.width : Dimension := ⟨"width", .size⟩
def Dimension.length : Dimension := ⟨"length", .size⟩

-- Sensory domain
def Dimension.temperature : Dimension := ⟨"temperature", .sensory⟩

-- Evaluative domain
def Dimension.happiness : Dimension := ⟨"happiness", .evaluative⟩
def Dimension.cost : Dimension := ⟨"cost", .evaluative⟩
def Dimension.price : Dimension := ⟨"price", .evaluative⟩
def Dimension.quality : Dimension := ⟨"quality", .evaluative⟩
def Dimension.value : Dimension := ⟨"value", .evaluative⟩

-- Psychological domain
def Dimension.intelligence : Dimension := ⟨"intelligence", .psychological⟩

-- State domain
def Dimension.fullness : Dimension := ⟨"fullness", .state⟩
def Dimension.wetness : Dimension := ⟨"wetness", .state⟩
def Dimension.cleanliness : Dimension := ⟨"cleanliness", .state⟩
def Dimension.straightness : Dimension := ⟨"straightness", .state⟩
def Dimension.flatness : Dimension := ⟨"flatness", .state⟩
def Dimension.openness : Dimension := ⟨"openness", .state⟩
def Dimension.freedom : Dimension := ⟨"freedom", .state⟩
def Dimension.tightness : Dimension := ⟨"tightness", .state⟩
def Dimension.alive : Dimension := ⟨"alive", .state⟩
def Dimension.pregnancy : Dimension := ⟨"pregnancy", .state⟩
def Dimension.hardness : Dimension := ⟨"hardness", .state⟩
def Dimension.smoothness : Dimension := ⟨"smoothness", .state⟩
def Dimension.purity : Dimension := ⟨"purity", .state⟩
def Dimension.cracking : Dimension := ⟨"cracking", .state⟩
def Dimension.denting : Dimension := ⟨"denting", .state⟩
def Dimension.scratching : Dimension := ⟨"scratching", .state⟩
def Dimension.shattering : Dimension := ⟨"shattering", .state⟩

-- Physical dimension
def Dimension.weight : Dimension := ⟨"weight", .size⟩
def Dimension.thickness : Dimension := ⟨"thickness", .size⟩
def Dimension.depth : Dimension := ⟨"depth", .size⟩
def Dimension.speed : Dimension := ⟨"speed", .size⟩
def Dimension.strength : Dimension := ⟨"strength", .size⟩
def Dimension.age : Dimension := ⟨"age", .size⟩
def Dimension.brightness : Dimension := ⟨"brightness", .sensory⟩
def Dimension.volume : Dimension := ⟨"volume", .sensory⟩
def Dimension.danger : Dimension := ⟨"danger", .evaluative⟩
def Dimension.beauty : Dimension := ⟨"beauty", .evaluative⟩
def Dimension.importance : Dimension := ⟨"importance", .evaluative⟩
def Dimension.safety : Dimension := ⟨"safety", .evaluative⟩

-- General size dimension (large/small/gigantic/tiny)
def Dimension.generalSize : Dimension := ⟨"size", .size⟩

-- Perceptual domain (for RSA noise connection)
def Dimension.color : Dimension := ⟨"color", .color⟩
def Dimension.material : Dimension := ⟨"material", .material⟩
def Dimension.orientation : Dimension := ⟨"orientation", .orientation⟩

-- ═══════════════════════════════════════════
-- Domain Properties
-- ═══════════════════════════════════════════

/-- Whether adjectives in this domain typically require comparison-class
    computation for interpretation. Size, evaluative, psychological, and
    sensory domains contain relative gradable adjectives (RGAs) interpreted
    relative to a contextually-determined standard. Color, material,
    orientation, and state domains contain adjectives with more stable
    meanings.

    This distinction is theoretically significant: @cite{sedivy-etal-1999}
    showed that comparison-class-dependent (scalar) adjectives trigger
    contrastive inferences in referential contexts, while non-dependent
    (color) adjectives do not. -/
def PropertyDomain.requiresComparisonClass : PropertyDomain → Bool
  | .size          => true   -- tall, short, big, wide, ...
  | .evaluative    => true   -- expensive, good, ...
  | .psychological => true   -- smart, ...
  | .sensory       => true   -- hot, cold, ...
  | .color         => false  -- yellow, red, ...
  | .material      => false  -- wooden, metal, ...
  | .orientation   => false  -- vertical, horizontal, ...
  | .state         => false  -- full, wet, dead, ...

end Core
