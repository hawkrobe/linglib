import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Montague.Types

/-!
# Degree Semantics: Core Infrastructure
@cite{heim-2001} @cite{kennedy-2007} @cite{klein-1980} @cite{rett-2026} @cite{schwarzschild-2008} @cite{israel-2011} @cite{kennedy-mcnally-2005}

Shared types and interfaces for degree-based analyses of gradable
expressions. This module defines the minimal `GradablePredicate`
interface that all degree semantic frameworks (Kennedy, Heim, Klein,
Schwarzschild, Rett) share, and the compositional `DegP` structure
for degree phrase composition.

## Design

Every degree framework provides a measure function μ : Entity → Degree.
They differ in how the degree argument is bound and how the standard of
comparison is introduced:

| Framework       | Degree binding           | Standard introduction  |
|-----------------|--------------------------|------------------------|
| @cite{kennedy-2007}  | Degree quantifier -er    | Degree clause          |
| @cite{heim-2001}     | Sentential -er operator  | λ-abstraction          |
| @cite{klein-1980}    | No degrees               | Comparison class       |
| Schwarzschild   | Intervals on scale       | Interval semantics     |
| @cite{rett-2026}     | Order-sensitive MAX      | Scale-directional MAX  |

All frameworks except Klein posit degrees; this module provides the
interface they share.

## Connection to Core.Scale

`Core.Scale` defines the algebraic infrastructure (boundedness, MAX,
DirectedMeasure, degree/threshold types for computation). This module adds
the linguistic interface: gradable predicates, DegP composition, and
standard-of-comparison structure.

## Relationship to Lexical.Adjective.Theory

This module uses abstract types (`Entity D : Type*` with `LinearOrder D`)
for framework-level theorems. `Lexical.Adjective.Theory` uses concrete
`Degree max` (= `Fin (max+1)`) for computation in RSA models and Fragment
entries. The two serve different clients: this module is imported by
`Degree/Frameworks/` and `Degree/Comparative.lean`; `Adjective.Theory` is
imported by `Fragments/English/` and `Phenomena/Gradability/` bridges.

-/

namespace Semantics.Degree

open Core.Scale (Boundedness ComparativeScale Degree Threshold)

-- ════════════════════════════════════════════════════
-- § 1. Gradable Predicate Interface
-- ════════════════════════════════════════════════════

/-- Minimal interface for a gradable predicate: a measure function
    mapping entities to degrees on a scale with known boundedness.

    Extends `DirectedMeasure D Entity` with a lexical `form` field.
    Every degree framework (Kennedy, Heim, Schwarzschild, Rett) provides
    an instance. Klein's delineation approach does not use degrees, so
    it does not instantiate this interface.

    The algebraic content (μ, boundedness, direction) comes from
    `DirectedMeasure`. `GradablePredicate` adds only the lexical identity.

    The `D` parameter is the degree type (e.g., `ℚ`, `Degree max`,
    or an abstract `LinearOrder`). -/
structure GradablePredicate (Entity D : Type*) [LinearOrder D]
    extends Core.Scale.DirectedMeasure D Entity where
  /-- The adjective's lexical form (for identification) -/
  form : String

-- ════════════════════════════════════════════════════
-- § 2. DegP Compositional Structure
-- ════════════════════════════════════════════════════

/-- The compositional structure of a Degree Phrase (DegP).

    In all degree frameworks, DegP is the syntactic locus where
    degree comparison happens. The internal structure varies:

    Kennedy: [DegP [Deg -er/as/est] [DegComplement than-clause]]
    Heim: [DegP [-er d₁ d₂]...] (sentential operator)

    This type captures the framework-independent parts:
    what kind of comparison, and what standard type. -/
inductive DegPType where
  | comparative   -- -er / more
  | equative      -- as...as
  | superlative   -- -est / most
  | excessive     -- too
  | sufficiency   -- enough
  deriving DecidableEq, BEq, Repr

/-- The standard of comparison: what the degree is compared to. -/
inductive StandardType where
  | explicit     -- "taller than Bill" — explicit standard
  | contextual   -- "tall" — contextually determined standard
  | absolute     -- "full" — scale endpoint as standard
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. Positive Form Semantics
-- ════════════════════════════════════════════════════

/-- The positive (unmarked) form of a gradable adjective:
    "Kim is tall" is true iff μ(Kim) exceeds a contextual standard θ.

    This is the common core across Kennedy and Heim:
    - Kennedy: ⟦tall⟧ = λd.λx. height(x) ≥ d, with θ = pos(tall)
    - Heim: ⟦tall⟧ = λx. height(x) ≥ θ_c

    Klein's approach is different: "tall" is true relative to a
    comparison class, with no degree parameter. -/
def positiveSem {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (θ : D) (x : Entity) : Prop :=
  μ x ≥ θ

/-- The positive form with standard derived from scale structure.
    @cite{kennedy-2007}: for closed-scale adjectives, the standard IS
    the scale endpoint (minimum or maximum); for open-scale adjectives,
    it's contextually determined. -/
def positiveFromScale {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (b : Boundedness) (x : Entity) : Prop :=
  match b with
  | .closed | .upperBounded => μ x = ⊤   -- "completely full"
  | .lowerBounded           => μ x > ⊥   -- "wet" (any amount)
  | .open_                  => True       -- needs contextual θ

-- ════════════════════════════════════════════════════
-- § 4. Concrete Threshold-Based Meaning Functions
-- ════════════════════════════════════════════════════

/-! Computational (`Bool`) versions of threshold comparison using concrete
    `Degree max` types. Moved from `Lexical.Adjective.Theory` — these are
    general degree operations, not adjective-specific. -/

/-- Positive form: degree > threshold -/
def positiveMeaning {max : Nat} (d : Degree max) (t : Threshold max) : Bool :=
  (t : Degree max) < d

/-- Negative form: degree < threshold -/
def negativeMeaning {max : Nat} (d : Degree max) (t : Threshold max) : Bool :=
  d < (t : Degree max)

/-- Antonym reverses the comparison -/
def antonymMeaning {max : Nat} (d : Degree max) (t : Threshold max) : Bool :=
  d ≤ (t : Degree max)

/-- Monotonicity of `positiveMeaning` in the threshold: a higher threshold
    is informationally stronger. If `d > θ_strong` and `θ_weak ≤ θ_strong`,
    then `d > θ_weak`. This grounds the `InformationalStrength` distinction
    between weak adjectives (lower θ) and strong adjectives (higher θ). -/
theorem positiveMeaning_monotone {max : Nat} (d : Degree max)
    (θ_weak θ_strong : Threshold max)
    (h_ord : θ_weak ≤ θ_strong)
    (h_strong : positiveMeaning d θ_strong = true) :
    positiveMeaning d θ_weak = true := by
  simp only [positiveMeaning, decide_eq_true_eq] at *
  exact lt_of_le_of_lt h_ord h_strong

-- ════════════════════════════════════════════════════
-- § 5. Degree Modifiers (@cite{kennedy-mcnally-2005}; @cite{israel-2011})
-- ════════════════════════════════════════════════════

/-- Degree modifier direction — same axis as NPI scalar direction. -/
inductive ModifierDirection where
  | amplifier   -- very, extremely: θ + δ → strengthens
  | downtoner   -- slightly, kind of: θ - δ → attenuates
  deriving DecidableEq, BEq, Repr

/-- A degree modifier that shifts the threshold of a gradable predicate. -/
structure DegreeModifier (max : Nat) where
  form : String
  direction : ModifierDirection
  shift : Fin (max + 1)
  rank : Nat
  deriving Repr

/-- Apply a modifier to a threshold. -/
def DegreeModifier.applyToThreshold {max : Nat} (m : DegreeModifier max)
    (θ : Threshold max) : Threshold max :=
  have hθ := θ.value.isLt
  have hm := m.shift.isLt
  match m.direction with
  | .amplifier =>
    ⟨⟨min (θ.value.val + m.shift.val) (max - 1), by omega⟩⟩
  | .downtoner =>
    ⟨⟨θ.value.val - m.shift.val, by omega⟩⟩

/-- A modified gradable predicate: degree(x) > M(θ). -/
def modifiedMeaning {max : Nat} (m : DegreeModifier max)
    (d : Degree max) (θ : Threshold max) : Bool :=
  positiveMeaning d (m.applyToThreshold θ)

section ModifierInstances

variable (max : Nat)

/-- "slightly" — minimal downtoner -/
def slightly (h : 1 ≤ max := by omega) : DegreeModifier max :=
  { form := "slightly", direction := .downtoner
  , shift := ⟨1, by omega⟩, rank := 1 }

/-- "kind of" — moderate downtoner -/
def kindOf (h : 2 ≤ max := by omega) : DegreeModifier max :=
  { form := "kind of", direction := .downtoner
  , shift := ⟨2, by omega⟩, rank := 2 }

/-- "quite" — amplifier (AmE reading). -/
def quite (h : 1 ≤ max := by omega) : DegreeModifier max :=
  { form := "quite", direction := .amplifier
  , shift := ⟨1, by omega⟩, rank := 1 }

/-- "very" — strong amplifier -/
def very (h : 2 ≤ max := by omega) : DegreeModifier max :=
  { form := "very", direction := .amplifier
  , shift := ⟨2, by omega⟩, rank := 2 }

/-- "extremely" — maximal amplifier -/
def extremely (h : 3 ≤ max := by omega) : DegreeModifier max :=
  { form := "extremely", direction := .amplifier
  , shift := ⟨3, by omega⟩, rank := 3 }

end ModifierInstances

open Core.Scale (Threshold.toNat) in
#guard Nat.blt (quite 10).rank (very 10).rank
open Core.Scale (Threshold.toNat) in
#guard Nat.blt (very 10).rank (extremely 10).rank
open Core.Scale (Threshold.toNat) in
#guard Nat.blt (slightly 10).rank (kindOf 10).rank
open Core.Scale (Threshold.toNat) in
#guard Nat.blt 3 ((very 10).applyToThreshold (⟨⟨3, by omega⟩⟩ : Threshold 10) |>.toNat)
open Core.Scale (Threshold.toNat) in
#guard Nat.blt ((slightly 10).applyToThreshold (⟨⟨5, by omega⟩⟩ : Threshold 10) |>.toNat) 5

-- ════════════════════════════════════════════════════
-- § 6. Construction Types
-- ════════════════════════════════════════════════════

/-- Degree construction type (positive, comparative, equative, etc.).
    Used by evaluativity analyses to track which constructions trigger
    evaluative readings. -/
inductive AdjectivalConstruction where
  | positive
  | comparative
  | equative
  | measurePhrase
  | degreeQuestion
  deriving Repr, DecidableEq, BEq

instance : ToString AdjectivalConstruction where
  toString
    | .positive => "positive"
    | .comparative => "comparative"
    | .equative => "equative"
    | .measurePhrase => "measurePhrase"
    | .degreeQuestion => "degreeQuestion"

-- ════════════════════════════════════════════════════
-- § 7. Positive Form Standard (@cite{kennedy-2007})
-- ════════════════════════════════════════════════════

/-- Positive form standard: how the contextual threshold is determined.
    @cite{kennedy-2007}: for open scales, the standard is the contextual
    norm; for closed scales, it's the relevant endpoint. -/
inductive PositiveStandard where
  | contextual    -- open-scale: θ = norm relative to comparison class
  | minEndpoint   -- lower-bounded: θ = minimum (e.g., "bent", "wet")
  | maxEndpoint   -- upper-bounded/closed: θ = maximum (e.g., "full", "dry")
  deriving DecidableEq, BEq, Repr

/-- Interpretive Economy determines the standard from scale structure.
    When a scale has an endpoint, Interpretive Economy requires using it
    as the standard (more informative than contextual norm). -/
def interpretiveEconomy (b : Boundedness) : PositiveStandard :=
  match b with
  | .open_        => .contextual
  | .lowerBounded => .minEndpoint
  | .upperBounded => .maxEndpoint
  | .closed       => .maxEndpoint   -- both endpoints; max is default

/-- @cite{kennedy-2007} Class A vs. Class B adjectives.
    - **Class A** (relative): open scale, contextual standard.
      "tall", "expensive", "heavy"
    - **Class B** (absolute): closed scale, endpoint standard.
      "full", "empty", "straight", "bent"

    The class is determined entirely by scale boundedness. -/
def isClassA (b : Boundedness) : Bool :=
  match b with
  | .open_ => true
  | _ => false

def isClassB (b : Boundedness) : Bool :=
  !isClassA b

/-- Class A adjectives have contextual standards. -/
theorem classA_contextual : interpretiveEconomy .open_ = .contextual := rfl

/-- Class B adjectives (closed scale) have endpoint standards. -/
theorem classB_endpoint : interpretiveEconomy .closed = .maxEndpoint := rfl

-- ════════════════════════════════════════════════════
-- § 8. Scale Structure → Comparison Class Sensitivity
-- ════════════════════════════════════════════════════

/-- Whether the positive standard depends on contextual class membership.
    @cite{kennedy-2007} notes that Class A adjectives have standards
    determined by "the relevant class of individuals" (p. 17) — what
    @cite{klein-1980} and @cite{tessler-goodman-2022} call the comparison
    class. Endpoint standards (Class B) are fixed by scale structure.

    `true` for `.contextual` (threshold varies with comparison class),
    `false` for `.minEndpoint` / `.maxEndpoint` (threshold is a scale bound). -/
def PositiveStandard.requiresComparisonClass : PositiveStandard → Bool
  | .contextual  => true
  | .minEndpoint  => false
  | .maxEndpoint  => false

/-- Class A adjectives require comparison class resolution:
    open scale → contextual standard → CC-dependent. -/
theorem classA_requires_cc :
    (interpretiveEconomy .open_).requiresComparisonClass = true := rfl

/-- Class B adjectives do NOT require comparison class resolution:
    bounded scale → endpoint standard → CC-independent. -/
theorem classB_no_cc (b : Boundedness) (h : isClassA b = false) :
    (interpretiveEconomy b).requiresComparisonClass = false := by
  cases b <;> simp_all [isClassA, interpretiveEconomy,
    PositiveStandard.requiresComparisonClass]

/-- The full chain: `isClassA` ↔ `requiresComparisonClass` after
    Interpretive Economy. Scale structure determines everything. -/
theorem scale_determines_cc_sensitivity (b : Boundedness) :
    isClassA b = (interpretiveEconomy b).requiresComparisonClass := by
  cases b <;> rfl

end Semantics.Degree
