import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Max
import Mathlib.Data.Set.Basic

/-!
# Measurement Scales

Abstract measurement scale infrastructure shared by degree semantics
(Kennedy 2007: gradable adjectives) and temporal measurement (Krifka 1989,
Rouillard 2026: temporal *in*-adverbials).

## The Shared Pattern

Both Kennedy's adjective scales and Rouillard's temporal measurement exhibit
the same abstract structure:

1. A **linearly ordered domain** of scalar values (degrees, durations)
2. A **boundedness** classification (open vs. closed, bounded vs. unbounded)
3. A **density** property (dense ordering, inherited from ℝ via Mathlib)
4. An **informativity licensing** pattern: a grammatical element (degree
   modifier, temporal adverbial) is felicitous iff a scalar parameter
   can be **maximally informative** on the scale

## The Isomorphism

| Kennedy (Adjectives)                | Rouillard (TIAs)                     |
|-------------------------------------|--------------------------------------|
| Degree scale                        | Duration measurement domain          |
| Scale value (degree d)              | Temporal measure (μ(t) = n)          |
| Open scale (tall, expensive)        | Atelic VP / DIV predicate            |
| → no inherent bound → no standard   | → no max⊨ → information collapse    |
| → "??completely tall"               | → "*was sick in three days"          |
| Closed scale (full, empty)          | Telic VP / QUA predicate             |
| → inherent bound → standard exists  | → max⊨ exists → upward scalar       |
| → "completely full" ✓               | → "wrote a paper in three days" ✓   |
| Interpretive Economy (Kennedy 2007) | MIP (Rouillard 2026)                 |
| "Maximize conventional meaning"     | "Maximize numeral contribution"      |

The isomorphism is realized structurally: both domains use `Boundedness` to
classify their scales at the lexical/data level, and `Boundedness.isLicensed`
derives the licensing prediction from the classification. Actual scale types
encode boundedness via Mathlib typeclasses (`OrderTop`, `OrderBot`, `NoMaxOrder`,
`NoMinOrder`), and licensing theorems are proved directly from these typeclasses.

## References

- Kennedy, C. (2007). Vagueness and grammar.
- Krifka, M. (1989). Nominal reference, temporal constitution.
- Rouillard, V. (2026). Maximal informativity and temporal in-adverbials.
- Fox, D. & Hackl, M. (2006). The universal density of measurement.
-/

namespace Core.Scale

-- ════════════════════════════════════════════════════
-- § 1. Scale Boundedness
-- ════════════════════════════════════════════════════

/-- Classification of scale boundedness.
    Kennedy (2007): four scale types based on which endpoints exist.
    Rouillard (2026): temporal domains have similar boundary structure
    (closed intervals have both bounds, open intervals lack them).

    This enum is the **lexical data tag** for classifying scales in fragment
    entries and phenomena files. The actual order-theoretic properties of
    concrete scale types are encoded via Mathlib typeclasses (`OrderTop`,
    `OrderBot`, `NoMaxOrder`, `NoMinOrder`). -/
inductive Boundedness where
  | open_        -- no inherent bounds (Kennedy: tall; Rouillard: atelic VP)
  | lowerBounded -- minimum exists, no maximum (Kennedy: wet; Rouillard: N/A)
  | upperBounded -- maximum exists, no minimum (Kennedy: dry; Rouillard: N/A)
  | closed       -- both bounds exist (Kennedy: full; Rouillard: telic VP)
  deriving DecidableEq, Repr, BEq

/-- Does this scale have an inherent maximum? -/
def Boundedness.hasMax : Boundedness → Bool
  | .upperBounded | .closed => true
  | .open_ | .lowerBounded => false

/-- Does this scale have an inherent minimum? -/
def Boundedness.hasMin : Boundedness → Bool
  | .lowerBounded | .closed => true
  | .open_ | .upperBounded => false

/-- Licensing prediction: a bounded scale (any endpoint exists) admits a
    maximally informative element, licensing degree modifiers (Kennedy) or
    TIA numerals (Rouillard). An open scale does not.
    Kennedy (2007): Interpretive Economy requires non-trivial scale contribution.
    Rouillard (2026): MIP requires the numeral to be maximally informative. -/
def Boundedness.isLicensed : Boundedness → Bool
  | .closed | .lowerBounded | .upperBounded => true
  | .open_ => false

/-- Derive a `Boundedness` tag from order-theoretic properties of a type.
    Useful when you have a concrete type and want to classify it for
    compatibility with lexical data. -/
def Boundedness.ofType (hasTop : Bool) (hasBot : Bool) : Boundedness :=
  match hasTop, hasBot with
  | true, true => .closed
  | true, false => .upperBounded
  | false, true => .lowerBounded
  | false, false => .open_

-- ════════════════════════════════════════════════════
-- § 2. Measurement Scale
-- ════════════════════════════════════════════════════

/-- A measurement scale: a linearly ordered domain.
    Density is captured by Mathlib's `DenselyOrdered` typeclass,
    and boundedness by `OrderTop`/`OrderBot`/`NoMaxOrder`/`NoMinOrder`.

    Instances:
    - Degree scales for gradable adjectives (Kennedy 2007)
    - Duration measurement for temporal adverbials (Krifka 1989)
    - Numeral scales for number words (Fox & Hackl 2006)

    Fox & Hackl (2006) UDM: all natural language scales satisfy `DenselyOrdered`.
    Use `[DenselyOrdered α]` alongside `[MeasurementScale α]` when density is needed. -/
class MeasurementScale (α : Type*) extends LinearOrder α

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

-- ════════════════════════════════════════════════════
-- § 5. Licensing Predictions (Data-Level)
-- ════════════════════════════════════════════════════

/-- Closed scales predict licensing (Kennedy: "completely full" ✓;
    Rouillard: telic VP E-TIA ✓). -/
theorem closed_isLicensed : Boundedness.closed.isLicensed = true := rfl

/-- Open scales predict blocking (Kennedy: "??completely tall";
    Rouillard: atelic VP E-TIA ✗). -/
theorem open_notLicensed : Boundedness.open_.isLicensed = false := rfl

end Core.Scale
