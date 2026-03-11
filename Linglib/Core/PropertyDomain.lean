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

The `primaryModality` and `isVisuallyPrivileged` functions make these
perceptual properties explicit, connecting the linguistic classification
to the psychophysics infrastructure in `Core.Agent.SignalDetection` and
`Core.Agent.Psychophysics`.
-/

namespace Core

-- ═══════════════════════════════════════════
-- Modality
-- ═══════════════════════════════════════════

/-- Sensory modality through which a property is primarily verified
    during perceptual search. @cite{giles-etal-2026} show that search
    efficiency generalises across modalities: discriminability drives
    overinformativeness for both visual colour and auditory material. -/
inductive Modality where
  | visual
  | auditory
  | haptic
  deriving Repr, DecidableEq, BEq

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
  deriving Repr, DecidableEq, BEq, Inhabited

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
  deriving Repr, DecidableEq, BEq

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

-- Psychological domain
def Dimension.intelligence : Dimension := ⟨"intelligence", .psychological⟩

-- State domain
def Dimension.fullness : Dimension := ⟨"fullness", .state⟩
def Dimension.wetness : Dimension := ⟨"wetness", .state⟩
def Dimension.cleanliness : Dimension := ⟨"cleanliness", .state⟩
def Dimension.straightness : Dimension := ⟨"straightness", .state⟩
def Dimension.flatness : Dimension := ⟨"flatness", .state⟩
def Dimension.openness : Dimension := ⟨"openness", .state⟩
def Dimension.alive : Dimension := ⟨"alive", .state⟩
def Dimension.pregnancy : Dimension := ⟨"pregnancy", .state⟩

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

/-- The primary modality through which a property domain is verified
    in typical referential contexts. This is a default — experimental
    designs may present properties in non-default modalities (e.g.,
    @cite{giles-etal-2026} present material auditorily via impact sounds).

    The distinction matters for search efficiency: visual attributes
    can be verified by a glance, while auditory or haptic attributes
    require more effortful verification. -/
def PropertyDomain.primaryModality : PropertyDomain → Modality
  | .color       => .visual
  | .size        => .visual
  | .orientation => .visual
  | .material    => .haptic   -- visual texture also possible; haptic is primary
  | .sensory     => .haptic
  | _            => .visual   -- evaluative, psychological, state: no strong default

/-- Whether a property domain corresponds to a privileged visual feature
    that guides pre-attentive search (@cite{wolfe-horowitz-2017}). Privileged
    features produce pop-out effects: targets with distinctive values are
    found in constant time regardless of display size.

    @cite{giles-etal-2026} show that colour and orientation are both
    privileged, yet colour is disproportionately overinformed — privileging
    alone does not explain colour's special status in reference production. -/
def PropertyDomain.isVisuallyPrivileged : PropertyDomain → Bool
  | .color       => true
  | .orientation => true
  | .size        => true   -- size pop-out is weaker than colour
  | _            => false

end Core
