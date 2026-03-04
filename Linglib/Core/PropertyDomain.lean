/-!
# Property Domains for Adjective Dimensions

Structured replacement for raw `String` dimension labels in adjective entries.
Connects adjective semantics to the perceptual noise infrastructure in
`RSA.Core.Noise` via `PropertyDomain.noiseDiscrimination`.

## Design

A `Dimension` pairs a human-readable name with a `PropertyDomain` that
classifies the perceptual channel. Smart constructors cover all dimensions
used across the English adjective fragments.
-/

namespace Core

/-- Broad perceptual/cognitive domain that a gradable dimension belongs to.
    The first three (`color`, `size`, `material`) have established noise
    parameters in `RSA.Noise`; the rest are classified but not yet
    parameterized. -/
inductive PropertyDomain where
  | color
  | size
  | material
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

-- Perceptual domain (for RSA noise connection)
def Dimension.color : Dimension := ⟨"color", .color⟩
def Dimension.material : Dimension := ⟨"material", .material⟩

end Core
