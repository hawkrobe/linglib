import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Max
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Tactic.NormNum
import Linglib.Tactics.OntSort

/-!
# Scales
@cite{fox-hackl-2006} @cite{hay-kennedy-levin-1999} @cite{holliday-icard-2013} @cite{kennedy-2007} @cite{kennedy-mcnally-2005} @cite{krantz-1971} @cite{krifka-1989} @cite{link-1983} @cite{rett-2026} @cite{rotstein-winter-2004} @cite{rouillard-2026} @cite{rullmann-1995}

Root algebraic infrastructure for all scale-based reasoning in linglib.

## Categorical Structure

The file defines a category of scales with two levels of enrichment:

```
                    ComparativeScale (α, ≤, boundedness)
                    ╱ ╲
          (+ join, ⊥, FA) (linear, μ, direction)
              ╱ ╲
      AdditiveScale DirectedMeasure
        ╱ ╲ │
MereoScale EpistemicScale (†) │
    │ │ │
    │ additive │ additive │ μ
    │ representation representation │
    ▼ ▼ ▼
                  (ℚ, ≤)

(†) See `Core/EpistemicScale.lean` for the epistemic arm.
```

**Objects**: `ComparativeScale α` — a preorder with boundedness classification.

**Morphisms**: `Monotone` (from Mathlib) — the categorical morphisms are just
  monotone maps between preorders. `MereoDim` (= `StrictMono`) is the injective
  subcategory.

**Enriched subcategory**: `AdditiveScale α` — comparative scale with join and
  finite additivity (FA). Two independent instances:
  - Mereological: `ExtMeasure.additive`
  - Epistemic: `EpistemicSystemFA` + `FinAddMeasure` (@cite{holliday-icard-2013}, §7)

**Linear specialization**: `DirectedMeasure` — comparative scale with a linear
  order, measure function, and direction. Instances: Kennedy adjectives,
  Rouillard TIAs, epistemic vocabulary.

The commutative diagram: both additive arms (mereological, epistemic) land in
(ℚ, ≤) via additive representation morphisms. The MIP arm also lands in (ℚ, ≤)
via measure functions. All three paths factor through `ComparativeScale`.

## Measurement Scales

Below the root structures, the file provides measurement scale infrastructure
shared by degree semantics and temporal measurement:

| Kennedy (Adjectival scales)         | Rouillard (TIAs / VPs)               |
|-------------------------------------|--------------------------------------|
| Degree scale                        | Duration measurement domain          |
| Open scale (tall, expensive)        | Atelic DA verb (lengthen, cool)      |
| → "??completely tall"               | → "*lengthened in three days"        |
| Closed scale (full, empty)          | Telic DA verb (straighten, dry)      |
| → "completely full" ✓               | → "straightened in three days" ✓    |
| Interpretive Economy | MIP                 |

Both domains use `Boundedness` to classify scales, and `Boundedness.isLicensed`
derives a "any endpoint exists" prediction (NOT @cite{kennedy-2007}'s full
modifier-class licensing matrix — see `Boundedness.isLicensed` docstring).
Actual scale types encode boundedness via Mathlib typeclasses (`OrderTop`,
`OrderBot`, `NoMaxOrder`, `NoMinOrder`).

**Cross-domain caveat.** The Kennedy-↔-Rouillard alignment above holds only
for **degree achievements** — verbs derived from gradable adjectives, where
@cite{hay-kennedy-levin-1999} establishes the scale-↔-telicity arrow. States
("be sick", "be full") and accomplishments ("write a paper") are outside HKL
1999's scope; their telicity needs separate justification (Krifka 1989/1998
on predicate quantization, or specific aspectual analyses).

-/

namespace Core.Scale

-- ════════════════════════════════════════════════════
-- § 1. Scale Boundedness
-- ════════════════════════════════════════════════════

/-- Classification of scale boundedness.
    @cite{kennedy-mcnally-2005} eq (1) and @cite{kennedy-2007} §4.2 eq (59):
    four scale types based on which endpoints exist (independently
    discovered by @cite{rotstein-winter-2004}).
    @cite{rouillard-2026}: temporal domains have similar boundary structure
    (closed intervals have both bounds, open intervals lack them).

    This enum is the **lexical data tag** for classifying scales in fragment
    entries and phenomena files — a role mathlib's typeclass instances cannot
    play (you cannot store an `[OrderTop α]` instance in a record field).
    The actual order-theoretic properties of concrete scale types are
    encoded via Mathlib typeclasses (`OrderTop`, `OrderBot`, `NoMaxOrder`,
    `NoMinOrder`); the two encodings serve different roles and both are real.

    **Standard-type dimension.** @cite{kennedy-2007} §4.3 eq (66) (Interpretive
    Economy) DERIVES standard type (relative / min-absolute / max-absolute)
    from scale structure for `open_`, `lowerBounded`, and `upperBounded`. For
    `closed`, all three interpretations are licensed (see eq 67: *opaque*,
    *transparent*) — this enum doesn't capture that disambiguation. Fragment
    entries with `boundedness = .closed` may need a separate `standardType`
    slot if downstream theorems care about the distinction.

    **Open-bounded sub-distinction.** @cite{kennedy-2007} fn 28: open scales
    can be further distinguished by whether they approach a value (e.g. 0 for
    cost) but don't include it, vs. completely unbounded. Not captured here. -/
inductive Boundedness where
  | open_        -- no inherent bounds (Kennedy: tall; Rouillard: atelic VP)
  | lowerBounded -- minimum exists, no maximum (Kennedy: wet; Rouillard: N/A)
  | upperBounded -- maximum exists, no minimum (Kennedy: dry; Rouillard: N/A)
  | closed       -- both bounds exist (Kennedy: full; Rouillard: telic VP)
  deriving DecidableEq, Repr

/-- Does this scale have an inherent maximum? -/
def Boundedness.hasMax : Boundedness → Bool
  | .upperBounded | .closed => true
  | .open_ | .lowerBounded => false

/-- Does this scale have an inherent minimum? -/
def Boundedness.hasMin : Boundedness → Bool
  | .lowerBounded | .closed => true
  | .open_ | .upperBounded => false

/-- "Any endpoint exists" predicate: returns `true` whenever the scale
    has at least one bound (max or min). An open scale returns `false`.

    **NOT @cite{kennedy-2007}'s full licensing prediction.** Kennedy's actual
    prediction is the 4×2 modifier-class matrix in @cite{kennedy-2007}
    eq (61) (= @cite{kennedy-mcnally-2005} eq (15)): maximizers
    (*completely, perfectly*) require an UPPER endpoint; minimizers
    (*slightly, partially*) require a LOWER endpoint; proportional modifiers
    (*half*) require BOTH. A single Bool can't encode this — to be faithful,
    split into `licensesMaximizer`/`licensesMinimizer`/`licensesProportional`.

    The current Bool is sufficient for callers that only need to distinguish
    "open" from "any-endpoint-exists" (e.g. Interpretive Economy gating a
    relative vs. absolute interpretation, @cite{kennedy-2007} §4.3, or
    Rouillard's MIP, @cite{rouillard-2026}). For modifier-specific
    licensing, consumers must consult `hasMax`/`hasMin` directly. -/
def Boundedness.isLicensed : Boundedness → Bool
  | .closed | .lowerBounded | .upperBounded => true
  | .open_ => false

-- ════════════════════════════════════════════════════
-- § 1a′. Rational Unit Interval
-- ════════════════════════════════════════════════════

/-- A rational number in the unit interval [0, 1].

    Wraps Mathlib's `Set.Icc` subtype for gradient linguistic properties
    (at-issueness, projectivity, etc.) and their contextual thresholds.
    Using `Set.Icc` gives us standard interval infrastructure from Mathlib
    (order, membership, etc.) without custom boilerplate.

    Access: `r.val` for the rational value, `r.prop.1` for `0 ≤ r`,
    `r.prop.2` for `r ≤ 1`. -/
abbrev Rat01 := ↥(Set.Icc (0 : ℚ) 1)

namespace Rat01

/-- The rational value. -/
abbrev value (r : Rat01) : ℚ := r.val

/-- Proof that the value is non-negative. -/
theorem nonneg (r : Rat01) : 0 ≤ r.val := r.prop.1

/-- Proof that the value is at most 1. -/
theorem le_one (r : Rat01) : r.val ≤ 1 := r.prop.2

instance : Repr Rat01 where
  reprPrec r _ := repr r.val

/-- The endpoint 0. -/
def zero : Rat01 := ⟨0, by norm_num, by norm_num⟩

/-- The endpoint 1. -/
def one : Rat01 := ⟨1, by norm_num, by norm_num⟩

/-- The midpoint ½, the standard default threshold. -/
def half : Rat01 := ⟨1/2, by norm_num, by norm_num⟩

/-- Does the value strictly exceed a threshold? -/
def exceeds (d θ : Rat01) : Prop := θ.val < d.val

instance (d θ : Rat01) : Decidable (exceeds d θ) :=
  inferInstanceAs (Decidable (θ.val < d.val))

end Rat01

-- ════════════════════════════════════════════════════
-- § 1b. MereoTag + LicensingPipeline
-- ════════════════════════════════════════════════════

/-- Binary mereological classification: the shared abstraction underlying
    all four licensing frameworks (Kennedy, Rouillard, Krifka, Zwarts). -/
inductive MereoTag where
  | qua  -- quantized / bounded / telic / closed
  | cum  -- cumulative / unbounded / atelic / open
  deriving DecidableEq, Repr

def MereoTag.toBoundedness : MereoTag → Boundedness
  | .qua => .closed
  | .cum => .open_

/-- A licensing pipeline: any type whose elements can be classified into
    scale boundedness. Kennedy, Rouillard, Krifka, and Zwarts all
    instantiate this with different source types but the same target.

    Core instances (`Boundedness`, `MereoTag`) live here. Domain-specific
    instances (`Telicity`, `VendlerClass`, `PathShape`, `BoundaryType`)
    live in their respective theory/bridge files. -/
class LicensingPipeline (α : Type*) where
  toBoundedness : α → Boundedness

namespace LicensingPipeline

variable {α : Type*} [LicensingPipeline α]

def isLicensed (a : α) : Bool :=
  (toBoundedness a).isLicensed

instance : LicensingPipeline Boundedness where
  toBoundedness := id

instance : LicensingPipeline MereoTag where
  toBoundedness := MereoTag.toBoundedness

/-- The universal licensing theorem: any two pipeline inputs that map to
    the same Boundedness yield the same licensing prediction, regardless
    of which framework they come. -/
theorem universal {α β : Type*} [LicensingPipeline α] [LicensingPipeline β]
    (a : α) (b : β) (h : toBoundedness a = toBoundedness b) :
    isLicensed a = isLicensed b := by
  simp only [isLicensed, h]

end LicensingPipeline

-- ════════════════════════════════════════════════════
-- § 1c. Comparative Scale (Root Algebraic Structure)
-- ════════════════════════════════════════════════════

/-- A comparative scale: a boundedness classification on a preorder.
    This is the root object in the category of scales. All scale-based
    reasoning in linglib (degree semantics, mereological measurement,
    epistemic comparison) factors through this structure.

    The ordering comes from the ambient `[Preorder α]` — no redundant
    `le`/`le_refl`/`le_trans` fields. Morphisms are Mathlib's `Monotone`.

    @cite{krantz-1971}: a comparative scale is an ordered set with
    enough structure to support qualitative comparison. -/
@[ont_sort] structure ComparativeScale (α : Type*) [Preorder α] where
  /-- Scale boundedness classification -/
  boundedness : Boundedness

/-- An additive scale: a comparative scale enriched with join and finite
    additivity (FA). Two independent instances exist in linglib:
    - Mereological: `ExtMeasure.additive`
    - Epistemic: probability FA

    The FA axiom says disjoint augmentation preserves order: if z is
    disjoint from both x and y, then x ≤ y ↔ x ⊔ z ≤ y ⊔ z. This
    is the qualitative content of additive representation. -/
structure AdditiveScale (α : Type*) [SemilatticeSup α] extends ComparativeScale α where
  /-- Disjointness predicate -/
  disjoint : α → α → Prop
  /-- Finite additivity: disjoint augmentation preserves order.
      Both `≤` and `⊔` come from the ambient `SemilatticeSup`. -/
  fa : ∀ (x y z : α), disjoint x z → disjoint y z →
    (x ≤ y ↔ x ⊔ z ≤ y ⊔ z)

namespace ComparativeScale

/-- Licensing prediction from the underlying boundedness. -/
def isLicensed {α : Type*} [Preorder α] (S : ComparativeScale α) : Bool :=
  S.boundedness.isLicensed

end ComparativeScale

-- ════════════════════════════════════════════════════
-- § 1d. Scale Polarity
-- ════════════════════════════════════════════════════

/-- Intrinsic polarity of a scale dimension.
    `positive`: the unmarked direction (tall, hot, confident).
    `negative`: the marked/inverted direction (short, cold, doubtful). -/
inductive ScalePolarity where
  | positive
  | negative
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 1e. Directed Measure (Root Algebraic Primitive)
-- ════════════════════════════════════════════════════

/-- A directed measurement on a bounded scale: the algebraic primitive
    underlying degree semantics, modal semantics, and epistemic scales.

    A `DirectedMeasure D E` packages:
    - A degree type `D` with a linear order (the scale)
    - An entity type `E` (what gets measured)
    - A measure function `μ : E → D` (the measurement)
    - Boundedness classification (from `ComparativeScale`)
    - A direction/polarity (positive or negative)

    This is the common algebraic core of `GradablePredicate` (degree
    semantics), MIP domain constructors (maximal informativity), and
    `epistemicAsGradable` (epistemic threshold semantics). Each of
    these extends or instantiates `DirectedMeasure`:

    - `GradablePredicate E D` extends `DirectedMeasure D E` with `form`
    - `kennedyNumeral`, `rouillardETIA`, etc. produce `DirectedMeasure` instances
    - Epistemic vocabulary: `DirectedMeasure ℚ (E × (W → Prop))`

    The degree property (`atLeastDeg` for positive, `atMostDeg` for
    negative) is **derived** from direction, not stored. This captures
    the insight from @cite{lassiter-goodman-2017} that the binary direction choice
    (which side of the threshold counts as "satisfying the predicate")
    is the fundamental parameter, and the degree property follows.

    References:
    - Kennedy, C. (2007). Vagueness and grammar.
    - Lassiter, D. (2017). Graded modality. OUP.
    - Rouillard, V. (2026). Maximal informativity and temporal in-adverbials.
    - Krantz, D. et al. (1971). Foundations of measurement, Vol. 1. -/
structure DirectedMeasure (D : Type*) [LinearOrder D] (E : Type*) extends ComparativeScale D where
  /-- Measure function: maps entities to degrees on the scale -/
  μ : E → D
  /-- Scale direction: positive (μ(x) ≥ θ) or negative (μ(x) ≤ θ).
      Determines which side of a threshold counts as satisfying the
      predicate. Positive: tall, likely, full. Negative: short,
      unlikely, empty. -/
  direction : ScalePolarity := .positive

namespace DirectedMeasure

variable {D : Type*} [LinearOrder D] {E : Type*}

/-- Licensing: licensed iff the bounded scale admits an optimum.
    See `Boundedness.isLicensed` for the caveat — this checks
    "any endpoint exists", not @cite{kennedy-2007}'s full
    modifier-class licensing matrix. -/
def licensed (dm : DirectedMeasure D E) : Bool := dm.boundedness.isLicensed

end DirectedMeasure

-- ════════════════════════════════════════════════════
-- § 2. Measurement Scales (via Mathlib)
-- ════════════════════════════════════════════════════

/-! ### Scale types as Mathlib typeclass combinations

For **theorems about concrete scales** — proving facts about a particular
type — use Mathlib typeclasses directly:

- **Measurement scale**: `[LinearOrder α]`
- **Dense measurement scale** (@cite{fox-2007} UDM): `[LinearOrder α] [DenselyOrdered α]`
- **Upper-bounded scale**: `[LinearOrder α] [OrderTop α]`
- **Lower-bounded scale**: `[LinearOrder α] [OrderBot α]`
- **Open scale**: `[LinearOrder α] [NoMaxOrder α] [NoMinOrder α]`

For **lexical-data tagging** — storing scale classification in fragment
entries or pattern-matching on it in derivation tables — use the §1
`Boundedness` enum. Mathlib typeclass instances cannot be stored in record
fields or matched against; the enum and the typeclass system serve different
roles and both are real. (The earlier "no wrapper classes needed" advice
was wrong about lexical data.)

Instances:
- Degree scales for gradable adjectives
- Duration measurement for temporal adverbials
- Numeral scales for number words

@cite{fox-2007} UDM: all natural language scales satisfy `DenselyOrdered`.
Use `[DenselyOrdered α]` when density matters for the derivation. -/

-- ════════════════════════════════════════════════════
-- § 3. Informativity on Scales
-- ════════════════════════════════════════════════════

variable {α : Type*} [LinearOrder α]

/-- A family of propositions indexed by scale values is **upward monotone**
    (entailments go from smaller to larger values).
    Kennedy: "tall" — if x is tall, x is tall-or-more.
    Rouillard: E-TIA with telic VP — if event fits in n days, it fits in m ≥ n days. -/
def IsUpwardMonotone {W : Type*} (P : α → W → Prop) : Prop :=
  ∀ (x y : α), x ≤ y → ∀ w, P x w → P y w

/-- A family is **downward monotone**: entailments go from larger to smaller.
    Rouillard: E-TIA with atelic VP — if sick during n-day time, sick during m ≤ n day time. -/
def IsDownwardMonotone {W : Type*} (P : α → W → Prop) : Prop :=
  ∀ (x y : α), x ≤ y → ∀ w, P y w → P x w

/-- A family is **constant**: every value yields the same proposition.
    This is information collapse — no value is more informative than another.
    Occurs when a family is both upward and downward monotone. -/
def IsConstant {W : Type*} (P : α → W → Prop) : Prop :=
  ∀ (x y : α) (w : W), P x w ↔ P y w

/-- If P is both upward and downward monotone, it is constant. -/
theorem bimonotone_constant {W : Type*} (P : α → W → Prop)
    (hUp : IsUpwardMonotone P) (hDown : IsDownwardMonotone P) :
    IsConstant P := by
  intro x y w
  constructor
  · intro hx
    rcases le_total x y with h | h
    · exact hUp x y h w hx
    · exact hDown y x h w hx
  · intro hy
    rcases le_total y x with h | h
    · exact hUp y x h w hy
    · exact hDown x y h w hy

/-- **Informativity licensing**: a scale admits a well-defined optimum iff
    it is NOT constant. When the family is constant (information collapse),
    no grammatical element operating on that scale is felicitous.

    This is the abstract pattern shared by:
    - Kennedy's Interpretive Economy: degree modifiers require non-trivial
      scale contribution
    - Rouillard's MIP: TIA numerals require maximally informative values -/
def AdmitsOptimum {W : Type*} (P : α → W → Prop) : Prop :=
  ¬ IsConstant P

/-- Bimonotone families do not admit an optimum: if a family is both upward
    and downward monotone, it collapses to a constant and no element is
    maximally informative. This is the abstract core of why open-scale
    degree modification and atelic-VP E-TIAs are both blocked. -/
theorem bimonotone_no_optimum {W : Type*} (P : α → W → Prop)
    (hUp : IsUpwardMonotone P) (hDown : IsDownwardMonotone P) :
    ¬ AdmitsOptimum P :=
  fun h => h (bimonotone_constant P hUp hDown)

-- ════════════════════════════════════════════════════
-- § 3b. Maximal Informativity (@cite{fox-2007}, @cite{rouillard-2026})
-- ════════════════════════════════════════════════════

/-- A scale value `x` is **maximally informative** in a degree property `P`
    at world `w` iff `P x w` is true and `P x` entails `P y` for every
    other true `P y w`.

    @cite{fox-2007} §4: the unified exhaustivity requirement underlying
    implicatures (*only*), degree questions, and definite
    descriptions.

    @cite{rouillard-2026} eq. (75): max⊨(w, P) specializes this to temporal domains.
    This definition is domain-general. -/
def IsMaxInf {W : Type*} (P : α → W → Prop) (x : α) (w : W) : Prop :=
  P x w ∧ ∀ y, P y w → (∀ w', P x w' → P y w')

/-- A degree property **has** a maximally informative element at world `w`. -/
def HasMaxInf {W : Type*} (P : α → W → Prop) (w : W) : Prop :=
  ∃ x, IsMaxInf P x w

/-- Information collapse: no element is maximally informative at any world.
    Fox & Hackl: this is why degree questions fail over dense complements,
    why *only* + "more than n" is contradictory, and why definite descriptions
    over dense open sets lack a presupposition-satisfying referent. -/
def InformationCollapse {W : Type*} (P : α → W → Prop) : Prop :=
  ∀ w, ¬ HasMaxInf P w

-- ════════════════════════════════════════════════════
-- § 4. Typeclass-Based Licensing Theorems
-- ════════════════════════════════════════════════════

/-- On a scale with no maximum (`NoMaxOrder`), any upward monotone family
    that is nontrivial (i.e., some value yields a different set of worlds
    than another) cannot have a ceiling: for any candidate optimum, a
    strictly larger value exists.

    This is the typeclass-level counterpart of the data-level prediction
    `Boundedness.open_.isLicensed = false`: open scales block degree
    modification and TIA licensing because no element is maximal.

    Proof sketch: For any `x`, `NoMaxOrder` gives `y > x`. If `P` is
    upward monotone, `P x w → P y w`, so `x` is never the unique optimum. -/
theorem open_no_upward_ceiling [NoMaxOrder α]
    (P : α → Prop) (hMono : ∀ (x y : α), x ≤ y → P x → P y) (x : α) (hx : P x) :
    ∃ y, x < y ∧ P y := by
  obtain ⟨y, hy⟩ := NoMaxOrder.exists_gt x
  exact ⟨y, hy, hMono x y (le_of_lt hy) hx⟩

/-- On a scale with a top element (`OrderTop`), the predicate `· = ⊤` is
    upward monotone (vacuously — only ⊤ satisfies it) and nonconstant
    (on nontrivial types). This witnesses that upper-bounded scales admit
    an optimum.

    Proof sketch: `⊤` satisfies `· = ⊤`, and for any `x < ⊤`, `x` does not.
    So the family is not constant → `AdmitsOptimum` holds. -/
theorem upperBound_admits_optimum [OrderTop α] (h_nontrivial : ∃ x : α, x ≠ ⊤) :
    ∃ (P : α → Prop), (∀ x y : α, x ≤ y → P x → P y) ∧ ¬ (∀ x y : α, P x ↔ P y) := by
  refine ⟨(· = ⊤), fun x y hxy hx => ?_, fun h => ?_⟩
  · rw [hx] at hxy; exact le_antisymm le_top hxy
  · obtain ⟨x, hx⟩ := h_nontrivial
    exact hx ((h x ⊤).mpr rfl)

/-- On a scale with a bottom element (`OrderBot`), the predicate `· = ⊥` is
    downward monotone and nonconstant (on nontrivial types). This witnesses
    that lower-bounded scales admit an optimum. -/
theorem lowerBound_admits_optimum [OrderBot α] (h_nontrivial : ∃ x : α, x ≠ ⊥) :
    ∃ (P : α → Prop), (∀ x y : α, x ≤ y → P y → P x) ∧ ¬ (∀ x y : α, P x ↔ P y) := by
  refine ⟨(· = ⊥), fun x y hxy hy => ?_, fun h => ?_⟩
  · rw [hy] at hxy; exact le_antisymm hxy bot_le
  · obtain ⟨x, hx⟩ := h_nontrivial
    exact hx ((h x ⊥).mpr rfl)

/-- Boundedness is necessary for licensing: on a scale with no upper bound
    and no lower bound, there exists a monotone family with no optimum.
    Contrapositive: if every monotone family admits an optimum, the scale
    has a bound. -/
theorem open_scale_unlicensable [NoMaxOrder α] [NoMinOrder α]
    (h : ∃ x y : α, x ≠ y) :
    ∃ (P : α → Prop), (∀ x y, x ≤ y → P x → P y) ∧ ¬ (∀ x y, P x ↔ P y) ∧
      ∀ x, P x → ∃ y, x < y ∧ P y := by
  obtain ⟨x₀, _, _⟩ := h
  refine ⟨(x₀ ≤ ·), fun a b hab ha => le_trans ha hab, ?_, fun x hx => ?_⟩
  · intro hconst
    obtain ⟨z, hz⟩ := NoMinOrder.exists_lt x₀
    exact absurd ((hconst z x₀).mpr (le_refl x₀)) (not_le.mpr hz)
  · obtain ⟨y, hy⟩ := NoMaxOrder.exists_gt x
    exact ⟨y, hy, le_trans hx (le_of_lt hy)⟩

-- ════════════════════════════════════════════════════
-- § 5. Licensing Predictions (Data-Level)
-- ════════════════════════════════════════════════════

/-- Closed scales predict licensing (Kennedy: "completely full" ✓;
    Rouillard: telic VP E-TIA ✓). -/
theorem closed_isLicensed : Boundedness.closed.isLicensed = true := rfl

/-- Open scales predict blocking (Kennedy: "??completely tall";
    Rouillard: atelic VP E-TIA ✗). -/
theorem open_notLicensed : Boundedness.open_.isLicensed = false := rfl

-- ════════════════════════════════════════════════════
-- § 6. Degree Properties (@cite{fox-2007} §2)
-- ════════════════════════════════════════════════════

/-! ### Degree properties for comparison relations

Five degree properties covering all comparison relations, parameterized by
a measure function `μ : W → α`. These are the building blocks for the named
numeral meanings (`Semantics.Numerals.atLeastMeaning` etc.) and degree
questions (`Theories/Semantics/Degree/Question.lean`).

- `atLeastDeg`: closed `≥`, always has max⊨
- `moreThanDeg`: open `>`, fails on dense scales
- `eqDeg`: equality `=`, trivially has max⊨
- `atMostDeg`: closed `≤`
- `lessThanDeg`: open `<`

The key divergence: on ℕ, `>` collapses to `≥` with successor, so both
have `HasMaxInf`. On dense scales, `>` yields an open set with no max⊨.
This is the UDM prediction (@cite{fox-2007} §2). -/

/-- Degree property for "exactly d": the measure at w equals d. -/
def eqDeg {W : Type*} (μ : W → α) : α → W → Prop :=
  fun d w => μ w = d

/-- Degree property for "at least d": the measure at w meets or exceeds d. -/
def atLeastDeg {W : Type*} (μ : W → α) : α → W → Prop :=
  fun d w => μ w ≥ d

/-- Degree property for "more than d": the measure strictly exceeds d. -/
def moreThanDeg {W : Type*} (μ : W → α) : α → W → Prop :=
  fun d w => μ w > d

/-- Degree property for "at most d": the measure at w is at most d. -/
def atMostDeg {W : Type*} (μ : W → α) : α → W → Prop :=
  fun d w => μ w ≤ d

/-- Degree property for "less than d": the measure is strictly less than d. -/
def lessThanDeg {W : Type*} (μ : W → α) : α → W → Prop :=
  fun d w => μ w < d

/-- "At least" is downward monotone: weaker thresholds are easier to satisfy. -/
theorem atLeastDeg_downMono {W : Type*} (μ : W → α) : IsDownwardMonotone (atLeastDeg μ) :=
  fun _ _ hxy _ hy => le_trans hxy hy

/-- "More than" is downward monotone: weaker thresholds are easier to satisfy. -/
theorem moreThanDeg_downMono {W : Type*} (μ : W → α) : IsDownwardMonotone (moreThanDeg μ) :=
  fun _ _ hxy _ hy => lt_of_le_of_lt hxy hy

/-- "At least d" always has a maximally informative element: d₀ = μ(w).

    This holds on ANY scale — dense or discrete — because the actual
    value μ(w) is always in the domain and "at least μ(w)" entails
    "at least d" for all d ≤ μ(w) by transitivity.

    This is why bare numerals generate scalar implicatures regardless
    of scale density: the `≥` relation creates a closed set with a
    natural maximum at the true value. -/
theorem atLeast_hasMaxInf {W : Type*} (μ : W → α) (w : W) :
    HasMaxInf (atLeastDeg μ) w :=
  ⟨μ w, le_refl _, fun _ hd _ hw' => le_trans hd hw'⟩

/-- **Implicature asymmetry** (@cite{fox-2007} §2):
    on a dense scale, "more than n" has NO maximally informative element.

    For any candidate d₀ < μ(w), density gives d' ∈ (d₀, μ(w)).
    A witness world w₁ with μ(w₁) ∈ (d₀, d') has "more than d₀"
    true but "more than d'" false — so d₀ does not entail d'.

    The `hSurj` hypothesis says every degree value is realized by some
    possible world. -/
theorem moreThan_noMaxInf {W : Type*} [DenselyOrdered α] (μ : W → α)
    (hSurj : Function.Surjective μ) (w : W) :
    ¬ HasMaxInf (moreThanDeg μ) w := by
  intro ⟨d₀, hd₀, hent⟩
  obtain ⟨d', hd₀d', hd'w⟩ := DenselyOrdered.dense d₀ (μ w) hd₀
  obtain ⟨m, hd₀m, hmd'⟩ := DenselyOrdered.dense d₀ d' hd₀d'
  obtain ⟨w₁, rfl⟩ := hSurj m
  exact absurd (hent d' hd'w w₁ hd₀m) (not_lt.mpr (le_of_lt hmd'))

/-- **Kennedy–F&H bridge**: `IsMaxInf` of the "at least" degree property
    at value m and world w holds iff the measure at w equals m. -/
theorem isMaxInf_atLeast_iff_eq {W : Type*} (μ : W → α) (m : α) (w : W)
    (hSurj : Function.Surjective μ) :
    IsMaxInf (atLeastDeg μ) m w ↔ μ w = m := by
  constructor
  · intro ⟨hge, hent⟩
    obtain ⟨w_m, hw_m⟩ := hSurj m
    have h : μ w_m ≥ μ w := hent (μ w) (le_refl _) w_m (le_of_eq hw_m.symm)
    have : μ w ≤ m := by rw [← hw_m]; exact h
    exact (le_antisymm hge this).symm
  · rintro rfl
    exact ⟨le_refl _, fun _ hd _ hn' => le_trans hd hn'⟩

/-- On ℕ, `>` collapses to `≥` with successor: "more than m" ↔ "at least m+1".
    This is the discrete equivalence that density breaks. -/
theorem moreThan_eq_atLeast_succ {W : Type*} (μ : W → ℕ) (m : ℕ) (w : W) :
    moreThanDeg μ m w ↔ atLeastDeg μ (m + 1) w :=
  Iff.rfl

/-- On ℕ, "more than m" has `HasMaxInf`: the discrete collapse rescues maximality.
    Contrast with `moreThan_noMaxInf`: on dense scales, `HasMaxInf` fails. -/
theorem moreThan_nat_hasMaxInf {W : Type*} (μ : W → ℕ) (w : W) (hw : moreThanDeg μ 0 w) :
    HasMaxInf (moreThanDeg μ) w := by
  refine ⟨μ w - 1, ?_, fun d hd w' hw' => ?_⟩
  · have : μ w > 0 := hw; show μ w > μ w - 1; omega
  · have : μ w' > μ w - 1 := hw'; have : μ w > d := hd; show μ w' > d; omega

-- ════════════════════════════════════════════════════
-- § 6b. Order-Sensitive MAX (@cite{rett-2026})
-- ════════════════════════════════════════════════════

/-! ### Scale-sensitive maximality operator

@cite{rett-2026}: MAX_R(X) picks the element(s)
of X that R-dominate all other members. For the `<` scale this is the GLB
(earliest / smallest), for `>` the LUB (latest / largest). The same operator
underlies both temporal connectives (*before*/*after*) and degree comparatives.

- Rett, J. (2026). Semantic ambivalence and expletive negation. Ms.
-/

/-- Order-sensitive maximality (@cite{rett-2026}, def. 1):
    MAX_R(X) = { x ∈ X | ∀ x' ∈ X, x' ≠ x → R x x' }.
    Domain-general over any relation R and set X. -/
def maxOnScale {α : Type*} (R : α → α → Prop) (X : Set α) : Set α :=
  { x | x ∈ X ∧ ∀ x' ∈ X, x' ≠ x → R x x' }

/-- MAX on a singleton is that singleton: MAX_R({x}) = {x}.
    The universal quantifier is vacuously satisfied. -/
theorem maxOnScale_singleton {α : Type*} (R : α → α → Prop) (x : α) :
    maxOnScale R {x} = {x} := by
  ext y
  simp only [maxOnScale, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl, _⟩; rfl
  · rintro rfl
    exact ⟨rfl, fun x' hx' hne => absurd hx' hne⟩

/-- MAX₍<₎ on a closed interval `{x | s ≤ x ∧ x ≤ f}` is the singleton `{s}`.
    The minimum element s R-dominates all others on the `<` scale.
    Dual: MAX₍>₎ on the same interval is `{f}`. -/
theorem maxOnScale_lt_closedInterval {α : Type*} [LinearOrder α]
    (s f : α) (hsf : s ≤ f) :
    maxOnScale (· < ·) { x : α | s ≤ x ∧ x ≤ f } = {s} := by
  ext x
  simp only [maxOnScale, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hxs, _⟩, hdom⟩
    by_contra hne
    have : s < x := lt_of_le_of_ne hxs (Ne.symm hne)
    have := hdom s ⟨le_refl _, hsf⟩ (ne_of_lt ‹s < x›)
    exact absurd ‹s < x› (not_lt.mpr (le_of_lt this))
  · rintro rfl
    exact ⟨⟨le_refl _, hsf⟩, fun x' ⟨hx's, _⟩ hne =>
      lt_of_le_of_ne hx's (Ne.symm hne)⟩

/-- MAX₍>₎ on a closed interval `{x | s ≤ x ∧ x ≤ f}` is the singleton `{f}`.
    The maximum element R-dominates all others on the `>` scale. -/
theorem maxOnScale_gt_closedInterval {α : Type*} [LinearOrder α]
    (s f : α) (hsf : s ≤ f) :
    maxOnScale (· > ·) { x : α | s ≤ x ∧ x ≤ f } = {f} := by
  ext x
  simp only [maxOnScale, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨_, hxf⟩, hdom⟩
    by_contra hne
    have : x < f := lt_of_le_of_ne hxf hne
    have := hdom f ⟨hsf, le_refl _⟩ (ne_of_gt ‹x < f›)
    exact absurd ‹x < f› (not_lt.mpr (le_of_lt this))
  · rintro rfl
    exact ⟨⟨hsf, le_refl _⟩, fun x' ⟨_, hx'f⟩ hne =>
      lt_of_le_of_ne hx'f hne⟩

/-- A scalar construction f is **ambidirectional** iff
    applying f to a set B and to its complement Bᶜ yields the same result,
    because MAX picks the same informative boundary from both.
    This is the mechanism behind expletive negation licensing: when
    f(B) ↔ f(Bᶜ), negating B is truth-conditionally vacuous. -/
def isAmbidirectional {α : Type*} (f : Set α → Prop) (B : Set α) : Prop :=
  f B ↔ f Bᶜ

/-- A predicate `f` is **MAX_R-determined** iff its value depends only on
    `maxOnScale R` of its argument: any two sets with the same `MAX_R`
    yield the same `f`-verdict. The before/until/comparative theorems all
    establish exactly this: *before* relates A to `MAX₍<₎` of B, the
    comparative *than*-clause to `MAX₍≥₎` of the degree set, etc. -/
def IsMaxDetermined {α : Type*} (R : α → α → Prop) (f : Set α → Prop) : Prop :=
  ∀ B₁ B₂ : Set α, maxOnScale R B₁ = maxOnScale R B₂ → (f B₁ ↔ f B₂)

/-- **Shared informative bound** ⇒ ambidirectionality. The general
    template behind Rett's typology: if a construction is `MAX_R`-determined
    and `B` and `Bᶜ` share their `MAX_R`-bound, then the construction is
    truth-conditionally insensitive to negation of B.

    Each per-construction ambidirectionality theorem in the library is an
    instance of this template — they prove the shared-bound side condition
    for a specific `f` and a class of `B`'s, then this lemma packages the
    result. See `Semantics.Tense.TemporalConnectives.before_preEvent_ambidirectional`
    for the canonical instance. -/
theorem ambidirectional_of_shared_max {α : Type*} {R : α → α → Prop}
    (f : Set α → Prop) (hf : IsMaxDetermined R f) (B : Set α)
    (hshared : maxOnScale R B = maxOnScale R Bᶜ) :
    isAmbidirectional f B :=
  hf B Bᶜ hshared

/-- **Converse**: an ambidirectional construction must share its `MAX_R`
    bound between B and Bᶜ — but only when MAX_R alone *witnesses* the
    distinction. Stated as a contrapositive to make the empirical content
    explicit: if MAX_R differs between B and Bᶜ but the construction
    cannot tell them apart by any *other* means (i.e. MAX_R-determined),
    then the construction is non-ambidirectional. The full converse
    requires assuming `f` separates sets with distinct MAX_R values, so
    we instead expose this as a derived fact only under that assumption. -/
theorem not_ambidirectional_of_distinct_max_separated {α : Type*}
    {R : α → α → Prop} (f : Set α → Prop) (B : Set α)
    (hsep : ∀ B₁ B₂ : Set α,
      maxOnScale R B₁ ≠ maxOnScale R B₂ → ¬ (f B₁ ↔ f B₂))
    (hdiff : maxOnScale R B ≠ maxOnScale R Bᶜ) :
    ¬ isAmbidirectional f B :=
  hsep B Bᶜ hdiff

/-- **Bridge**: `maxOnScale (· ≥ ·)` applied to the "at least" degree set
    `{d | d ≤ μ(w)}` yields `{μ(w)}` — the singleton containing the true
    value. This connects the relational MAX to `IsMaxInf`.

    The convention: `maxOnScale R X` picks elements x ∈ X with `R x x'` for
    all other x'. With `R = (· ≥ ·)`, this picks elements ≥ all others,
    i.e., the maximum. -/
theorem maxOnScale_atLeast_singleton {W : Type*} (μ : W → α) (w : W) :
    maxOnScale (· ≥ ·) { d : α | d ≤ μ w } = { μ w } := by
  ext x
  simp only [maxOnScale, Set.mem_setOf_eq, Set.mem_singleton_iff, ge_iff_le]
  constructor
  · rintro ⟨hx, hdom⟩
    by_contra hne
    have hlt : x < μ w := lt_of_le_of_ne hx hne
    have := hdom (μ w) (le_refl _) (Ne.symm hne)
    exact not_le.mpr hlt this
  · rintro rfl
    exact ⟨le_refl _, fun x' hx' hne => le_of_lt (lt_of_le_of_ne hx' hne)⟩

/-- MAX₍≥₎ on {d | d ≤ b} is {b}. Corollary of `maxOnScale_atLeast_singleton`
    with `μ = id`. Used by the comparative boundary theorems. -/
theorem maxOnScale_ge_atMost (b : α) :
    maxOnScale (· ≥ ·) {d | d ≤ b} = {b} :=
  maxOnScale_atLeast_singleton id b

-- ════════════════════════════════════════════════════
-- § 6c. Existential Lowering (Type-Shifting)
-- ════════════════════════════════════════════════════

/-! ## Existential lowering: exact → "at least"

@cite{partee-1987}'s BE + iota + existential closure, applied to a degree
property: from an exact reading `exact d w` ("the measure equals `d`"),
existentially close to `∃ d' ≥ d, exact d' w`. On any reflexive linear
order this collapses to `atLeastDeg μ d w` — witness `d' := μ w`.

This is the formal content of @cite{kennedy-2015}'s "de-Fregean" derivation
of the lower-bound numeral reading from the exact reading. The collapse
generalizes Numeral type-shifting to arbitrary scales. -/

/-- Existentially lower an exact-style degree property to its lower-bound
    counterpart: there exists some `d' ≥ d` such that the exact property
    holds at `d'`. -/
def typeLower {W : Type*} (exact : α → W → Prop) (d : α) (w : W) : Prop :=
  ∃ d', d' ≥ d ∧ exact d' w

/-- **Type-shift collapse**: `typeLower (eqDeg μ) = atLeastDeg μ`. -/
theorem typeLower_eqDeg_iff {W : Type*} (μ : W → α) (d : α) (w : W) :
    typeLower (eqDeg μ) d w ↔ atLeastDeg μ d w := by
  refine ⟨?_, fun h => ⟨μ w, h, rfl⟩⟩
  rintro ⟨d', hd', heq⟩
  -- heq : eqDeg μ d' w  unfolds to  μ w = d'
  have heq' : μ w = d' := heq
  show μ w ≥ d
  exact heq'.symm ▸ hd'

instance atLeastDeg.decidable {W : Type*} [DecidableLE α] (μ : W → α)
    (d : α) (w : W) : Decidable (atLeastDeg μ d w) := by
  unfold atLeastDeg; infer_instance

instance atMostDeg.decidable {W : Type*} [DecidableLE α] (μ : W → α)
    (d : α) (w : W) : Decidable (atMostDeg μ d w) := by
  unfold atMostDeg; infer_instance

instance moreThanDeg.decidable {W : Type*} [DecidableLT α] (μ : W → α)
    (d : α) (w : W) : Decidable (moreThanDeg μ d w) := by
  unfold moreThanDeg; infer_instance

instance lessThanDeg.decidable {W : Type*} [DecidableLT α] (μ : W → α)
    (d : α) (w : W) : Decidable (lessThanDeg μ d w) := by
  unfold lessThanDeg; infer_instance

instance eqDeg.decidable {W : Type*} [DecidableEq α] (μ : W → α)
    (d : α) (w : W) : Decidable (eqDeg μ d w) := by
  unfold eqDeg; infer_instance

instance typeLower_eqDeg.decidable {W : Type*} (μ : W → α) (d : α) (w : W) :
    Decidable (typeLower (eqDeg μ) d w) :=
  decidable_of_iff _ (typeLower_eqDeg_iff μ d w).symm

-- ════════════════════════════════════════════════════
-- § 6d. @cite{kennedy-2015}'s De-Fregean GQ
-- ════════════════════════════════════════════════════

/-! ## A unified GQ denotation parameterized by the comparison relation

@cite{kennedy-2015} proposes a single denotation for modified and
unmodified numerals: `λP. max{d | #P ≥ d} REL m`, where the only parameter
distinguishing surface forms is the relation `REL ∈ {=, ≥, >, ≤, <}`.

Specialised to a property of the form `atLeastDeg μ`, the maximum degree
satisfying `atLeastDeg μ d w` is `μ w` itself, so Kennedy's denotation
collapses to `rel (μ w) m` — captured here as `kennedyGQ rel μ m w`.

The five existing degree properties (`eqDeg`, `atLeastDeg`, `moreThanDeg`,
`atMostDeg`, `lessThanDeg`) are definitionally `kennedyGQ` instantiated at
the corresponding relation. The Class A vs Class B distinction
(@cite{geurts-nouwen-2007}, @cite{nouwen-2010}) collapses to a structural
property of `rel`: Class B ↔ `IsRefl α rel`; Class A ↔ `IsIrrefl α rel`. -/

/-- Kennedy's unified GQ denotation: `(rel) (μ w) d`. The five named degree
    properties are definitionally equal to instantiations of this. -/
def kennedyGQ {W : Type*} (rel : α → α → Prop) (μ : W → α) (d : α) (w : W) : Prop :=
  rel (μ w) d

omit [LinearOrder α] in
/-- Specialisation to `(· = ·)` recovers `eqDeg`. -/
theorem kennedyGQ_eq_eqDeg {W : Type*} (μ : W → α) :
    kennedyGQ (· = ·) μ = eqDeg μ := rfl

/-- Specialisation to `(· ≥ ·)` recovers `atLeastDeg`. -/
theorem kennedyGQ_ge_eq_atLeastDeg {W : Type*} (μ : W → α) :
    kennedyGQ (· ≥ ·) μ = atLeastDeg μ := rfl

/-- Specialisation to `(· > ·)` recovers `moreThanDeg`. -/
theorem kennedyGQ_gt_eq_moreThanDeg {W : Type*} (μ : W → α) :
    kennedyGQ (· > ·) μ = moreThanDeg μ := rfl

/-- Specialisation to `(· ≤ ·)` recovers `atMostDeg`. -/
theorem kennedyGQ_le_eq_atMostDeg {W : Type*} (μ : W → α) :
    kennedyGQ (· ≤ ·) μ = atMostDeg μ := rfl

/-- Specialisation to `(· < ·)` recovers `lessThanDeg`. -/
theorem kennedyGQ_lt_eq_lessThanDeg {W : Type*} (μ : W → α) :
    kennedyGQ (· < ·) μ = lessThanDeg μ := rfl

omit [LinearOrder α] in
/-- **Class B inclusion at the boundary** (general). If `rel` is reflexive,
    Kennedy's GQ holds at any world `w` whose measure equals the boundary `d`.
    Specialised to numerals: "at least 3" / "at most 3" hold at `w = 3`. -/
theorem kennedyGQ_refl_at_boundary {W : Type*} {rel : α → α → Prop}
    [Std.Refl rel] (μ : W → α) {d : α} {w : W} (h : μ w = d) :
    kennedyGQ rel μ d w := by
  show rel (μ w) d
  rw [h]; exact Std.Refl.refl _

omit [LinearOrder α] in
/-- **Class A exclusion at the boundary** (general). If `rel` is irreflexive,
    Kennedy's GQ fails at any world `w` whose measure equals the boundary `d`.
    Specialised to numerals: "more than 3" / "fewer than 3" fail at `w = 3`. -/
theorem kennedyGQ_irrefl_at_boundary {W : Type*} {rel : α → α → Prop}
    [Std.Irrefl rel] (μ : W → α) {d : α} {w : W} (h : μ w = d) :
    ¬ kennedyGQ rel μ d w := by
  intro hk
  have hdd : rel d d := h ▸ (hk : rel (μ w) d)
  exact (Std.Irrefl.irrefl (r := rel) d) hdd

-- ════════════════════════════════════════════════════
-- § 6e. Anti-Horn-Scale Lemmas (general)
-- ════════════════════════════════════════════════════

/-! ## Why exact bare numerals are not part of a Horn scale

@cite{kennedy-2015} argues that bare numerals (under their exact reading) are
**not monotone in their numerical argument** — neither upward nor downward —
so they fail the Horn-scale criterion. The classic Horn scale `⟨1, 2, 3, …⟩`
presupposes upward monotonicity; the dual scale `⟨…, 3, 2, 1⟩` presupposes
downward monotonicity. Kennedy's unified GQ accommodates both modifier
directions without needing a Horn scale at all.

The lemmas below state the failure-of-monotonicity and weakness-vs-exact
results purely in terms of `eqDeg` / `atLeastDeg` / `moreThanDeg` —
independent of any specific scale. The Nat-specific results in
`Theories/Semantics/Numerals/Basic.lean` are immediate corollaries. -/

/-- "More than `d`" and "exactly `d`" are disjoint (general). -/
theorem moreThanDeg_disjoint_eqDeg {W : Type*} (μ : W → α) (d : α) (w : W) :
    ¬ (eqDeg μ d w ∧ moreThanDeg μ d w) := by
  rintro ⟨h₁, h₂⟩
  exact lt_irrefl d (h₁ ▸ h₂)

/-- "Less than `d`" and "exactly `d`" are disjoint (general). -/
theorem lessThanDeg_disjoint_eqDeg {W : Type*} (μ : W → α) (d : α) (w : W) :
    ¬ (eqDeg μ d w ∧ lessThanDeg μ d w) := by
  rintro ⟨h₁, h₂⟩
  exact lt_irrefl d (h₁ ▸ h₂)

/-- Bare exact meaning entails "at least" (general half of Class B inclusion). -/
theorem eqDeg_imp_atLeastDeg {W : Type*} (μ : W → α) (d : α) (w : W) :
    eqDeg μ d w → atLeastDeg μ d w := fun h => h ▸ le_refl _

/-- Bare exact meaning entails "at most" (general; symmetric to above). -/
theorem eqDeg_imp_atMostDeg {W : Type*} (μ : W → α) (d : α) (w : W) :
    eqDeg μ d w → atMostDeg μ d w := fun h => h ▸ le_refl _

/-- "At least `d`" is strictly weaker than "exactly `d`" (general). Given a
    witness world `w` with `μ w = d'` where `d < d'`, "at least `d`" holds
    but "exactly `d`" fails. -/
theorem atLeastDeg_strictly_weaker_than_eqDeg {W : Type*} (μ : W → α)
    {d d' : α} (hlt : d < d') {w : W} (hμ : μ w = d') :
    atLeastDeg μ d w ∧ ¬ eqDeg μ d w := by
  refine ⟨?_, ?_⟩
  · show μ w ≥ d; rw [hμ]; exact le_of_lt hlt
  · show ¬ μ w = d; rw [hμ]; exact ne_of_gt hlt

/-- Exact `eqDeg` is **not upward-monotone** (general). Given two distinct
    boundary values `d ≤ d'` and a witness world with `μ w = d`, the universal
    "if exact at `d` then exact at `d'`" fails — `μ w` cannot equal both. -/
theorem eqDeg_not_upward_monotone {W : Type*} (μ : W → α)
    {d d' : α} (hne : d ≠ d') (hle : d ≤ d') {w : W} (hμ : μ w = d) :
    ¬ ∀ x y, x ≤ y → eqDeg μ x w → eqDeg μ y w := by
  intro h
  exact hne ((h d d' hle hμ).symm.trans hμ).symm

/-- Exact `eqDeg` is **not downward-monotone** (general). Symmetric to above. -/
theorem eqDeg_not_downward_monotone {W : Type*} (μ : W → α)
    {d d' : α} (hne : d ≠ d') (hle : d' ≤ d) {w : W} (hμ : μ w = d) :
    ¬ ∀ x y, y ≤ x → eqDeg μ x w → eqDeg μ y w := by
  intro h
  exact hne ((h d d' hle hμ).symm.trans hμ).symm

/-- Universal closure (the alternative to existential closure) is
    unsatisfiable when the closure range contains two distinct values:
    no single `x` can equal two different `k`s. This rules out the
    universal-closure reading of Partee's iota generally. -/
theorem distinct_no_universal_witness {α : Type*} (k₁ k₂ : α) (hne : k₁ ≠ k₂) :
    ¬ ∃ x, ∀ k, k = k₁ ∨ k = k₂ → x = k := by
  rintro ⟨x, h⟩
  exact hne ((h k₁ (Or.inl rfl)).symm.trans (h k₂ (Or.inr rfl)))

-- ════════════════════════════════════════════════════
-- § 7. "At most" Symmetry (Rouillard's direction)
-- ════════════════════════════════════════════════════

/-- "At most" is upward monotone: larger thresholds are easier to satisfy. -/
theorem atMostDeg_upMono {W : Type*} (μ : W → α) : IsUpwardMonotone (atMostDeg μ) :=
  fun _ _ hxy _ hy => le_trans hy hxy

/-- "At most d" always has a maximally informative element: d₀ = μ(w).
    Symmetric to `atLeast_hasMaxInf`. -/
theorem atMost_hasMaxInf {W : Type*} (μ : W → α) (w : W) :
    HasMaxInf (atMostDeg μ) w :=
  ⟨μ w, le_refl _, fun _ hd _ hw' => le_trans hw' hd⟩

/-- **Kennedy–Rouillard bridge**: `IsMaxInf` of "at most d" at value m and
    world w holds iff the measure at w equals m. Symmetric to
    `isMaxInf_atLeast_iff_eq`: the MIP derives exact meaning from "at most"
    just as it does from "at least". -/
theorem isMaxInf_atMost_iff_eq {W : Type*} (μ : W → α) (m : α) (w : W)
    (hSurj : Function.Surjective μ) :
    IsMaxInf (atMostDeg μ) m w ↔ μ w = m := by
  constructor
  · intro ⟨hle, hent⟩
    obtain ⟨w_m, hw_m⟩ := hSurj m
    have h : μ w_m ≤ μ w := hent (μ w) (le_refl _) w_m (le_of_eq hw_m)
    have : m ≤ μ w := hw_m ▸ h
    exact le_antisymm hle this
  · rintro rfl
    exact ⟨le_refl _, fun _ hd _ hw' => le_trans hw' hd⟩

-- ════════════════════════════════════════════════════
-- § 8. MIP Domain: Kennedy–Rouillard Unification
-- ════════════════════════════════════════════════════

/-! ### The Maximal Informativity Principle as a universal mechanism

@cite{kennedy-2015} proposes a de-Fregean type-shift that maps lower-bound numeral
meanings to exact meanings for Class B items (closed scales). @cite{rouillard-2026}
proposes the MIP as the licensing condition for temporal *in*-adverbials.

These are the SAME mechanism: given a measure function μ and a monotone degree
property P, the maximally informative value is always μ(w) — the true value.
The MIP derives exactness from monotone degree properties regardless of domain:

| Domain              | μ             | Degree prop  | Direction | MIP result    |
|---------------------|---------------|-------------|-----------|---------------|
| Kennedy numerals    | cardinality   | atLeastDeg  | down mono | max⊨ = μ(w)  |
| Kennedy adjectives  | degree        | atLeastDeg  | down mono | max⊨ = μ(w)  |
| Rouillard E-TIAs   | runtime       | atMostDeg   | up mono   | max⊨ = μ(w)  |

The `isMaxInf_atLeast_iff_eq` and `isMaxInf_atMost_iff_eq` theorems prove this
for both monotonicity directions. The Kennedy type-shift is not a separate
mechanism — it IS the MIP applied to "at least n". -/

namespace DirectedMeasure

-- ── MIP Domain Constructors ────────────────────────

variable {α : Type*} [LinearOrder α] {W : Type*}

/-- @cite{kennedy-2015} numeral domain: "at least n" over cardinality.
    Closed scale (ℕ well-ordered) → always licensed.
    Type-shift to exact = MIP applied to atLeastDeg. -/
def kennedyNumeral (μ : W → α) : DirectedMeasure α W :=
  { boundedness := .closed, μ := μ }

/-- @cite{kennedy-2007} gradable adjective domain.
    Boundedness varies by adjective class (tall: open, full: closed). -/
def kennedyAdjective (μ : W → α) (b : Boundedness) : DirectedMeasure α W :=
  { boundedness := b, μ := μ }

/-- @cite{rouillard-2026} E-TIA domain: event runtime ≤ interval size.
    Boundedness determined by Vendler class (telic → closed, atelic → open). -/
def rouillardETIA (μ : W → α) (b : Boundedness) : DirectedMeasure α W :=
  { boundedness := b, μ := μ, direction := .negative }

/-- @cite{rouillard-2026} G-TIA domain: PTS extent on open intervals.
    Always open → always blocked (information collapse). -/
def rouillardGTIA (μ : W → α) : DirectedMeasure α W :=
  { boundedness := .open_, μ := μ, direction := .negative }

-- ── Licensing Theorems ──────────────────────────────

/-- Kennedy numeral domains are always licensed (closed scale). -/
theorem kennedyNumeral_licensed (μ : W → α) :
    (kennedyNumeral μ).licensed = true := rfl

/-- Kennedy Class B adjectives (closed scale) are licensed. -/
theorem classB_licensed (μ : W → α) :
    (kennedyAdjective μ .closed).licensed = true := rfl

/-- Kennedy Class A adjectives (open scale) are blocked. -/
theorem classA_blocked (μ : W → α) :
    (kennedyAdjective μ .open_).licensed = false := rfl

/-- Rouillard telic E-TIAs are licensed (closed runtime scale). -/
theorem eTIA_telic_licensed (μ : W → α) :
    (rouillardETIA μ .closed).licensed = true := rfl

/-- Rouillard atelic E-TIAs are blocked (open runtime scale). -/
theorem eTIA_atelic_blocked (μ : W → α) :
    (rouillardETIA μ .open_).licensed = false := rfl

/-- Rouillard G-TIAs are always blocked (open PTS). -/
theorem gTIA_blocked (μ : W → α) :
    (rouillardGTIA μ).licensed = false := rfl

-- ── The Kennedy–Rouillard Isomorphism ───────────────

/-- The deep isomorphism: a Kennedy numeral domain and a Rouillard E-TIA
    domain on a closed scale have identical licensing, despite using
    opposite directions (positive vs negative). -/
theorem kennedy_rouillard_same_licensing (μ₁ μ₂ : W → α) :
    (kennedyNumeral μ₁).licensed = (rouillardETIA μ₂ .closed).licensed := rfl

/-- All four frameworks agree: licensing depends solely on boundedness.
    @cite{kennedy-2007}: closed-scale adjectives license degree modifiers.
    @cite{rouillard-2026}: closed-runtime VPs license E-TIAs.
    @cite{krifka-1989}: QUA predicates yield telic (bounded) VPs.
    @cite{zwarts-2005}: bounded paths yield telic VPs.
    All four route through Boundedness.isLicensed. -/
theorem four_frameworks_agree
    (b : Boundedness) {W : Type*} (μ₁ μ₂ : W → α) :
    (kennedyAdjective μ₁ b).licensed =
    (rouillardETIA μ₂ b).licensed := rfl

end DirectedMeasure

-- ════════════════════════════════════════════════════
-- § 9. MIP = Kennedy's Type-Shift
-- ════════════════════════════════════════════════════

/-! The punchline: Kennedy's de-Fregean type-shift is not a separate mechanism.
    It IS the MIP applied to a monotone degree property. For both "at least"
    (Kennedy) and "at most" (Rouillard), max⊨ at world w = μ(w), the true
    value. So the MIP universally derives exact meaning from monotone
    degree properties, regardless of monotonicity direction.

    `isMaxInf_atLeast_iff_eq`: max⊨(atLeastDeg μ, m, w) ↔ μ(w) = m
    `isMaxInf_atMost_iff_eq`: max⊨(atMostDeg μ, m, w) ↔ μ(w) = m

    Both directions yield `eqDeg μ m w` — exact meaning. -/

/-- MIP derives exact meaning from "at least" (Kennedy's direction). -/
theorem mip_atLeast_is_exact {W : Type*} (μ : W → α) (m : α) (w : W)
    (hSurj : Function.Surjective μ) :
    IsMaxInf (atLeastDeg μ) m w ↔ eqDeg μ m w :=
  isMaxInf_atLeast_iff_eq μ m w hSurj

/-- MIP derives exact meaning from "at most" (Rouillard's direction). -/
theorem mip_atMost_is_exact {W : Type*} (μ : W → α) (m : α) (w : W)
    (hSurj : Function.Surjective μ) :
    IsMaxInf (atMostDeg μ) m w ↔ eqDeg μ m w :=
  isMaxInf_atMost_iff_eq μ m w hSurj

/-- The MIP is direction-invariant: "at least" and "at most" yield the
    same exact meaning under maximal informativity. Kennedy's type-shift
    and Rouillard's MIP are literally the same operation. -/
theorem mip_direction_invariant {W : Type*} (μ : W → α) (m : α) (w : W)
    (hSurj : Function.Surjective μ) :
    IsMaxInf (atLeastDeg μ) m w ↔ IsMaxInf (atMostDeg μ) m w := by
  rw [mip_atLeast_is_exact μ m w hSurj, mip_atMost_is_exact μ m w hSurj]

-- ════════════════════════════════════════════════════
-- § 11. Discrete Bounded Scales
-- ════════════════════════════════════════════════════

/-! ### Degree and Threshold types for finite scales

Discretized scale types for gradable adjective RSA computations.
`Degree max` wraps `Fin (max + 1)` with `LinearOrder`, `BoundedOrder`, `Fintype`.
`Threshold max` wraps `Fin max` with coercion to `Degree max`.

These participate in the abstract `DirectedMeasure` infrastructure above via their
`LinearOrder` and `BoundedOrder` instances. -/

/-- A degree on a scale from 0 to max. Represents discretized continuous
    values like height, temperature, etc. -/
structure Degree (max : Nat) where
  value : Fin (max + 1)
  deriving Repr, DecidableEq

instance {n : Nat} : Inhabited (Degree n) := ⟨⟨0, Nat.zero_lt_succ n⟩⟩

/-- `Degree max` inherits a linear order from `Fin (max + 1)`. -/
instance {max : Nat} : LinearOrder (Degree max) :=
  LinearOrder.lift' Degree.value (fun a b h => by cases a; cases b; simp_all)

/-- `Degree max` is bounded: 0 is the minimum, `max` is the maximum. -/
instance {max : Nat} : BoundedOrder (Degree max) where
  top := ⟨Fin.last max⟩
  le_top d := Fin.le_last d.value
  bot := ⟨0, Nat.zero_lt_succ max⟩
  bot_le d := Fin.zero_le d.value

/-- All degrees from 0 to max -/
def allDegrees (max : Nat) : List (Degree max) :=
  List.finRange (max + 1) |>.map (⟨·⟩)

/-- Degree from Nat (clamped) -/
def Degree.ofNat (max : Nat) (n : Nat) : Degree max :=
  ⟨⟨min n max, by omega⟩⟩

/-- Get numeric value -/
def Degree.toNat {max : Nat} (d : Degree max) : Nat := d.value.val

/-- A threshold for a gradable adjective. x is "tall" iff degree(x) > threshold. -/
structure Threshold (max : Nat) where
  value : Fin max
  deriving Repr, DecidableEq

instance {n : Nat} (h : 0 < n := by omega) : Inhabited (Threshold n) := ⟨⟨0, h⟩⟩

/-- `Threshold max` inherits a linear order from `Fin max`. -/
instance {max : Nat} : LinearOrder (Threshold max) :=
  LinearOrder.lift' Threshold.value (fun a b h => by cases a; cases b; simp_all)

/-- All thresholds from 0 to max-1 -/
def allThresholds (max : Nat) (_ : 0 < max := by omega) : List (Threshold max) :=
  List.finRange max |>.map (⟨·⟩)

/-- Get numeric value -/
def Threshold.toNat {max : Nat} (t : Threshold max) : Nat := t.value.val

instance {max : Nat} : Fintype (Degree max) :=
  Fintype.ofEquiv (Fin (max + 1)) ⟨Degree.mk, Degree.value, fun _ => rfl, fun ⟨_⟩ => rfl⟩

instance {max : Nat} [NeZero max] : Fintype (Threshold max) :=
  Fintype.ofEquiv (Fin max) ⟨Threshold.mk, Threshold.value, fun _ => rfl, fun ⟨_⟩ => rfl⟩

/-- Coercion: Threshold embeds into Degree via Fin.castSucc -/
instance {max : Nat} : Coe (Threshold max) (Degree max) where
  coe t := ⟨t.value.castSucc⟩

theorem coe_threshold_toNat {max : Nat} (t : Threshold max) :
    (t : Degree max).toNat = t.toNat := rfl

/-- Construct a degree by literal: `deg 5 : Degree 10`. -/
abbrev deg (n : Nat) {max : Nat} (h : n ≤ max := by omega) : Degree max :=
  ⟨⟨n, by omega⟩⟩

/-- Construct a threshold by literal: `thr 5 : Threshold 10`. -/
abbrev thr (n : Nat) {max : Nat} (h : n < max := by omega) : Threshold max :=
  ⟨⟨n, h⟩⟩

-- ════════════════════════════════════════════════════
-- § 12. Bool Decision Wrappers
-- ════════════════════════════════════════════════════
-- § 13. Measure Function Typeclass
-- ════════════════════════════════════════════════════

/-- Typeclass for entities that have a degree/magnitude on some scale.
    This is the formal semantics "measure function" μ : Entity → Degree.

    The codomain `α` is polymorphic — heights might use ℚ (cm, exact),
    physical heights ℝ, durations ℕ (ticks), prices ℚ (USD), etc. `α` is
    an `outParam` so it can be inferred from the entity type via the
    instance. The canonical `Nat → ℚ` instance lives in
    `Theories/Semantics/Numerals/Basic.lean` (`CardinalityDegree`). -/
class HasDegree (E : Type) (α : outParam Type) where
  degree : E → α

end Core.Scale
