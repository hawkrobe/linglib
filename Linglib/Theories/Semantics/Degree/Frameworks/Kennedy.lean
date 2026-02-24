import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Degree.Core

/-!
# Kennedy's Measure Function Approach

Kennedy (2007) "Vagueness and Grammar": gradable adjectives denote
relations between individuals and degrees, mediated by a measure
function μ.

## Denotation

    ⟦tall⟧ = λd.λx. height(x) ≥ d

The adjective takes a degree argument d (type `⟨d,⟨e,t⟩⟩`) and returns
a predicate true of entities whose degree meets or exceeds d.

## Comparative

    ⟦-er⟧ = λG.λG'. max(G') > max(G)

The comparative morpheme takes two degree predicates (from the matrix
and the than-clause) and asserts the matrix maximum exceeds the standard
maximum.

## Scale Structure and Interpretive Economy

Kennedy's key contribution: scale structure (open vs. closed) determines
how the positive form standard is set:
- **Open scale** (tall): standard = contextual norm (comparison class)
- **Closed scale** (full): standard = scale endpoint (Interpretive Economy)

Interpretive Economy: "Maximize the contribution of the conventional
meanings of the elements of a sentence to the computation of its truth
conditions." When a scale has an endpoint, using it as the standard is
more informative than using a contextual norm.

## References

- Kennedy, C. (2007). Vagueness and grammar: The semantics of relative
  and absolute gradable adjectives. *Linguistics and Philosophy* 30(1): 1-45.
- Kennedy, C. & McNally, L. (2005). Scale structure, degree modification,
  and the semantics of gradable predicates. *Language* 81(2): 345-381.
-/

namespace Semantics.Degree.Frameworks.Kennedy

open Core.Scale (Boundedness Degree Threshold)

-- ════════════════════════════════════════════════════
-- § 1. Adjective Denotation
-- ════════════════════════════════════════════════════

/-- Kennedy's adjective denotation: a relation between degrees and entities.
    ⟦tall⟧ = λd.λx. height(x) ≥ d
    The degree argument is abstracted over and bound by a degree morpheme
    (-er, as, -est, too, enough). -/
def adjDenotation {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (d : D) (x : Entity) : Prop :=
  μ x ≥ d

/-- The degree set of an entity: the set of degrees d such that μ(x) ≥ d.
    This is an initial segment (downward closed set) of the scale. -/
def degreeSet {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (x : Entity) : Set D :=
  { d | μ x ≥ d }

-- ════════════════════════════════════════════════════
-- § 2. Comparative Morpheme
-- ════════════════════════════════════════════════════

/-- Kennedy's comparative morpheme: ⟦-er⟧ = λG.λG'. max(G') > max(G).
    Under the measure function approach, this reduces to comparing the
    maxima of two degree sets. Since degreeSet is [0, μ(x)] (for positive
    adjectives on bounded scales), max = μ(x). -/
def comparativeMorpheme {D : Type*} [LinearOrder D]
    (maxA maxB : D) : Prop :=
  maxA > maxB

/-- Kennedy comparative with measure function: reduces to direct comparison.
    "A is taller than B" iff height(A) > height(B). -/
def kennedyComparative {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) : Prop :=
  μ a > μ b

-- ════════════════════════════════════════════════════
-- § 3. Positive Form and Standard
-- ════════════════════════════════════════════════════

/-- Positive form standard: how the contextual threshold is determined.
    Kennedy (2007, §4): for open scales, the standard is the contextual
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

-- ════════════════════════════════════════════════════
-- § 4. Scale Structure Constraints
-- ════════════════════════════════════════════════════

/-- Kennedy (2007) Class A vs. Class B adjectives.
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

end Semantics.Degree.Frameworks.Kennedy
