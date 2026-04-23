/-!
# PropertyDomain — Perceptual/Cognitive Channels for Adjective Dimensions

@cite{giles-etal-2026} @cite{wolfe-horowitz-2017}

A taxonomy of perceptual and cognitive channels that classify the
dimension a gradable adjective measures along. The first four domains
(`color`, `size`, `material`, `orientation`) have established perceptual-
discriminability profiles in the visual-search literature; the rest are
inventoried for typological completeness.

`Dimension` pairs a human-readable name with a `PropertyDomain` and is
populated by the smart constructors below; the bridge to noise
parameters (`Features.PropertyDomain.noiseDiscrimination`) lives in
`Theories/Pragmatics/RSA/Channel.lean`.
-/

namespace Features

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
  deriving Repr, DecidableEq, Inhabited

/-- Whether adjectives in this domain typically require comparison-class
    computation for interpretation. Size, evaluative, psychological, and
    sensory domains contain relative gradable adjectives (RGAs) interpreted
    relative to a contextually-determined standard. Color, material,
    orientation, and state domains contain adjectives with more stable
    meanings.

    @cite{sedivy-etal-1999} showed that comparison-class-dependent
    (scalar) adjectives trigger contrastive inferences in referential
    contexts, while non-dependent (color) adjectives do not. -/
def PropertyDomain.requiresComparisonClass : PropertyDomain → Bool
  | .size          => true   -- tall, short, big, wide, ...
  | .evaluative    => true   -- expensive, good, ...
  | .psychological => true   -- smart, ...
  | .sensory       => true   -- hot, cold, ...
  | .color         => false  -- yellow, red, ...
  | .material      => false  -- wooden, metal, ...
  | .orientation   => false  -- vertical, horizontal, ...
  | .state         => false  -- full, wet, dead, ...

-- Smart constructors for `Dimension`, organised by domain.
-- Used via anonymous-constructor syntax in adjective entries:
--   `{ ..., dimension := .height, ... } : GradableAdjEntry`

-- Size domain
def Dimension.height      : Dimension := ⟨"height",      .size⟩
def Dimension.width       : Dimension := ⟨"width",       .size⟩
def Dimension.length      : Dimension := ⟨"length",      .size⟩
def Dimension.weight      : Dimension := ⟨"weight",      .size⟩
def Dimension.thickness   : Dimension := ⟨"thickness",   .size⟩
def Dimension.depth       : Dimension := ⟨"depth",       .size⟩
def Dimension.speed       : Dimension := ⟨"speed",       .size⟩
def Dimension.strength    : Dimension := ⟨"strength",    .size⟩
def Dimension.age         : Dimension := ⟨"age",         .size⟩
def Dimension.generalSize : Dimension := ⟨"size",        .size⟩

-- Sensory domain
def Dimension.temperature : Dimension := ⟨"temperature", .sensory⟩
def Dimension.brightness  : Dimension := ⟨"brightness",  .sensory⟩
def Dimension.volume      : Dimension := ⟨"volume",      .sensory⟩

-- Evaluative domain
def Dimension.happiness   : Dimension := ⟨"happiness",   .evaluative⟩
def Dimension.cost        : Dimension := ⟨"cost",        .evaluative⟩
def Dimension.price       : Dimension := ⟨"price",       .evaluative⟩
def Dimension.quality     : Dimension := ⟨"quality",     .evaluative⟩
def Dimension.value       : Dimension := ⟨"value",       .evaluative⟩
def Dimension.danger      : Dimension := ⟨"danger",      .evaluative⟩
def Dimension.beauty      : Dimension := ⟨"beauty",      .evaluative⟩
def Dimension.importance  : Dimension := ⟨"importance",  .evaluative⟩
def Dimension.safety      : Dimension := ⟨"safety",      .evaluative⟩

-- Psychological domain
def Dimension.intelligence : Dimension := ⟨"intelligence", .psychological⟩
def Dimension.expectation  : Dimension := ⟨"expectation",  .psychological⟩
def Dimension.possibility  : Dimension := ⟨"possibility",  .psychological⟩
def Dimension.confidence   : Dimension := ⟨"confidence",   .psychological⟩

-- State domain
def Dimension.fullness      : Dimension := ⟨"fullness",      .state⟩
def Dimension.wetness       : Dimension := ⟨"wetness",       .state⟩
def Dimension.cleanliness   : Dimension := ⟨"cleanliness",   .state⟩
def Dimension.straightness  : Dimension := ⟨"straightness",  .state⟩
def Dimension.flatness      : Dimension := ⟨"flatness",      .state⟩
def Dimension.openness      : Dimension := ⟨"openness",      .state⟩
def Dimension.freedom       : Dimension := ⟨"freedom",       .state⟩
def Dimension.tightness     : Dimension := ⟨"tightness",     .state⟩
def Dimension.alive         : Dimension := ⟨"alive",         .state⟩
def Dimension.pregnancy     : Dimension := ⟨"pregnancy",     .state⟩
def Dimension.hardness      : Dimension := ⟨"hardness",      .state⟩
def Dimension.smoothness    : Dimension := ⟨"smoothness",    .state⟩
def Dimension.purity        : Dimension := ⟨"purity",        .state⟩
def Dimension.cracking      : Dimension := ⟨"cracking",      .state⟩
def Dimension.denting       : Dimension := ⟨"denting",       .state⟩
def Dimension.scratching    : Dimension := ⟨"scratching",    .state⟩
def Dimension.shattering    : Dimension := ⟨"shattering",    .state⟩

-- Perceptual domain (RSA noise connection)
def Dimension.color       : Dimension := ⟨"color",       .color⟩
def Dimension.material    : Dimension := ⟨"material",    .material⟩
def Dimension.orientation : Dimension := ⟨"orientation", .orientation⟩

end Features
