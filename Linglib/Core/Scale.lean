import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Max
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Linglib.Tactics.OntSort

/-!
# Scales

Root algebraic infrastructure for all scale-based reasoning in linglib.

## Categorical Structure

The file defines a category of scales with two levels of enrichment:

```
                    ComparativeScale (α, ≤, boundedness)
                    ╱              ╲
          (+ join, ⊥, FA)    (linear, μ)
              ╱                      ╲
      AdditiveScale              MIPDomain
        ╱        ╲                    │
MereoScale   EpistemicScale (§14)    │
    │              │                  │
    │  additive    │  additive        │  μ
    │  representation  representation │
    ▼              ▼                  ▼
                  (ℚ, ≤)
```

**Objects**: `ComparativeScale α` — a preorder with boundedness classification.

**Morphisms**: `Monotone` (from Mathlib) — the categorical morphisms are just
  monotone maps between preorders. `MereoDim` (= `StrictMono`) is the injective
  subcategory.

**Enriched subcategory**: `AdditiveScale α` — comparative scale with join and
  finite additivity (FA). Two independent instances:
  - Mereological: `ExtMeasure.additive` (Krifka 1989)
  - Epistemic: `EpistemicSystemFA` + `FinAddMeasure` (Holliday & Icard 2013, § 14)

**Linear specialization**: `MIPDomain` — comparative scale with a linear order
  and measure function. Instances: Kennedy adjectives, Rouillard TIAs.

The commutative diagram: both additive arms (mereological, epistemic) land in
(ℚ, ≤) via additive representation morphisms. The MIP arm also lands in (ℚ, ≤)
via measure functions. All three paths factor through `ComparativeScale`.

## Measurement Scales

Below the root structures, the file provides measurement scale infrastructure
shared by degree semantics (Kennedy 2007) and temporal measurement (Krifka 1989,
Rouillard 2026):

| Kennedy (Adjectives)                | Rouillard (TIAs)                     |
|-------------------------------------|--------------------------------------|
| Degree scale                        | Duration measurement domain          |
| Open scale (tall, expensive)        | Atelic VP / DIV predicate            |
| → "??completely tall"               | → "*was sick in three days"          |
| Closed scale (full, empty)          | Telic VP / QUA predicate             |
| → "completely full" ✓               | → "wrote a paper in three days" ✓   |
| Interpretive Economy (Kennedy 2007) | MIP (Rouillard 2026)                 |

Both domains use `Boundedness` to classify scales, and `Boundedness.isLicensed`
derives the licensing prediction. Actual scale types encode boundedness via
Mathlib typeclasses (`OrderTop`, `OrderBot`, `NoMaxOrder`, `NoMinOrder`).

## References

- Kennedy, C. (2007). Vagueness and grammar.
- Krifka, M. (1989). Nominal reference, temporal constitution.
- Rouillard, V. (2026). Maximal informativity and temporal in-adverbials.
- Fox, D. & Hackl, M. (2006). The universal density of measurement.
- Holliday, W. & Icard, T. (2013). Measure semantics and qualitative semantics
  for epistemic modals.
- Krantz, D. et al. (1971). Foundations of measurement, Vol. 1.
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
-- § 1b. MereoTag + LicensingPipeline
-- ════════════════════════════════════════════════════

/-- Binary mereological classification: the shared abstraction underlying
    all four licensing frameworks (Kennedy, Rouillard, Krifka, Zwarts). -/
inductive MereoTag where
  | qua  -- quantized / bounded / telic / closed
  | cum  -- cumulative / unbounded / atelic / open
  deriving DecidableEq, BEq, Repr

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
    of which framework they come from. -/
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

    Krantz et al. (1971): a comparative scale is an ordered set with
    enough structure to support qualitative comparison. -/
@[ont_sort] structure ComparativeScale (α : Type*) [Preorder α] where
  /-- Scale boundedness classification -/
  boundedness : Boundedness

/-- An additive scale: a comparative scale enriched with join and finite
    additivity (FA). Two independent instances exist in linglib:
    - Mereological: `ExtMeasure.additive` (Krifka 1989)
    - Epistemic: probability FA (Holliday & Icard 2013)

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

/-- An additive scale is representable if there exists a monotone additive
    function into (ℚ, ≤). -/
def AdditiveScale.IsRepresentable {α : Type*} [SemilatticeSup α]
    (S : AdditiveScale α) : Prop :=
  ∃ (μ : α → ℚ), Monotone μ ∧
    ∀ (x y : α), S.disjoint x y → μ (x ⊔ y) = μ x + μ y

-- ════════════════════════════════════════════════════
-- § 2. Measurement Scales (via Mathlib)
-- ════════════════════════════════════════════════════

/-! ### Scale types as Mathlib typeclass combinations

A measurement scale is just a `LinearOrder`. Density is `DenselyOrdered`,
and boundedness is `OrderTop`/`OrderBot`/`NoMaxOrder`/`NoMinOrder`.
No wrapper classes needed — use Mathlib directly:

- **Measurement scale**: `[LinearOrder α]`
- **Dense measurement scale** (Fox & Hackl 2007 UDM): `[LinearOrder α] [DenselyOrdered α]`
- **Upper-bounded scale**: `[LinearOrder α] [OrderTop α]`
- **Lower-bounded scale**: `[LinearOrder α] [OrderBot α]`
- **Open scale**: `[LinearOrder α] [NoMaxOrder α] [NoMinOrder α]`

Instances:
- Degree scales for gradable adjectives (Kennedy 2007)
- Duration measurement for temporal adverbials (Krifka 1989)
- Numeral scales for number words (Fox & Hackl 2006)

Fox & Hackl (2007) UDM: all natural language scales satisfy `DenselyOrdered`.
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
-- § 3b. Maximal Informativity (Fox & Hackl 2007, Rouillard 2026)
-- ════════════════════════════════════════════════════

/-- A scale value `x` is **maximally informative** in a degree property `P`
    at world `w` iff `P x w` is true and `P x` entails `P y` for every
    other true `P y w`.

    Fox & Hackl (2007) §4: the unified exhaustivity requirement underlying
    implicatures (*only*), degree questions (Rullmann 1995), and definite
    descriptions (Link 1983).

    Rouillard (2026) eq. (75): max⊨(w, P) specializes this to temporal domains.
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
-- § 6. Degree Properties (Fox & Hackl 2007 §2)
-- ════════════════════════════════════════════════════

/-! ### Degree properties for comparison relations

Five degree properties covering all comparison relations, parameterized by
a measure function `μ : W → α`. These are the building blocks for numeral
semantics (`Numeral.Semantics.maxMeaning`) and degree questions
(`DegreeQuestion`).

- `atLeastDeg`: closed `≥`, always has max⊨
- `moreThanDeg`: open `>`, fails on dense scales
- `eqDeg`: equality `=`, trivially has max⊨
- `atMostDeg`: closed `≤`
- `lessThanDeg`: open `<`

The key divergence: on ℕ, `>` collapses to `≥` with successor, so both
have `HasMaxInf`. On dense scales, `>` yields an open set with no max⊨.
This is the UDM prediction (Fox & Hackl 2007 §2). -/

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

/-- **Implicature asymmetry** (Fox & Hackl 2007 §2):
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
-- § 6b. Order-Sensitive MAX (Rett 2026)
-- ════════════════════════════════════════════════════

/-! ### Scale-sensitive maximality operator

Rett (2026, def. 1, adapting Rullmann 1995): MAX_R(X) picks the element(s)
of X that R-dominate all other members. For the `<` scale this is the GLB
(earliest / smallest), for `>` the LUB (latest / largest). The same operator
underlies both temporal connectives (*before*/*after*) and degree comparatives.

- Rett, J. (2026). Semantic ambivalence and expletive negation. Ms.
-/

/-- Order-sensitive maximality (Rett 2026, def. 1):
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

/-- A scalar construction f is **ambidirectional** (Rett 2026, §3) iff
    applying f to a set B and to its complement Bᶜ yields the same result,
    because MAX picks the same informative boundary from both.
    This is the mechanism behind expletive negation licensing: when
    f(B) ↔ f(Bᶜ), negating B is truth-conditionally vacuous. -/
def isAmbidirectional {α : Type*} (f : Set α → Prop) (B : Set α) : Prop :=
  f B ↔ f Bᶜ

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

Kennedy (2015) proposes a de-Fregean type-shift that maps lower-bound numeral
meanings to exact meanings for Class B items (closed scales). Rouillard (2026)
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

/-- A maximal informativity domain: the abstract pattern shared by
    Kennedy (2007/2015) degree semantics and Rouillard (2026) temporal
    measurement.

    Given a measure function μ and a degree property P, the MIP determines
    licensing based on the scale's boundedness. Both Kennedy's Interpretive
    Economy and Rouillard's MIP are instances. -/
structure MIPDomain (α : Type*) [LinearOrder α] (W : Type*) extends ComparativeScale α where
  /-- Measure function from worlds/events to scale values -/
  measure : W → α
  /-- Degree property: P(d, w) iff measure at w relates to threshold d -/
  degProp : α → W → Prop

namespace MIPDomain

variable {α : Type*} [LinearOrder α] {W : Type*}

/-- MIP licensing: licensed iff bounded scale admits an optimum. -/
def licensed (d : MIPDomain α W) : Bool := d.boundedness.isLicensed

/-- MIP blocking: blocked iff open scale → information collapse. -/
def blocked (d : MIPDomain α W) : Bool := !d.licensed

-- ── Instances ──────────────────────────────────────

/-- Kennedy (2015) numeral domain: "at least n" over cardinality.
    Closed scale (ℕ well-ordered) → always licensed.
    Type-shift to exact = MIP applied to atLeastDeg. -/
def kennedyNumeral (μ : W → α) : MIPDomain α W :=
  { boundedness := .closed, measure := μ, degProp := atLeastDeg μ }

/-- Kennedy (2007) gradable adjective domain.
    Boundedness varies by adjective class (tall: open, full: closed). -/
def kennedyAdjective (μ : W → α) (b : Boundedness) : MIPDomain α W :=
  { boundedness := b, measure := μ, degProp := atLeastDeg μ }

/-- Rouillard (2026) E-TIA domain: event runtime ≤ interval size.
    Boundedness determined by Vendler class (telic → closed, atelic → open). -/
def rouillardETIA (μ : W → α) (b : Boundedness) : MIPDomain α W :=
  { boundedness := b, measure := μ, degProp := atMostDeg μ }

/-- Rouillard (2026) G-TIA domain: PTS extent on open intervals.
    Always open → always blocked (information collapse). -/
def rouillardGTIA (μ : W → α) : MIPDomain α W :=
  { boundedness := .open_, measure := μ, degProp := atMostDeg μ }

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

-- ── The Isomorphism ────────────────────────────────

/-- The Kennedy–Rouillard isomorphism: licensing is determined solely
    by boundedness, regardless of domain, measure function, or
    monotonicity direction. Two MIPDomains with the same boundedness
    have the same licensing prediction. -/
theorem licensing_from_boundedness (d₁ d₂ : MIPDomain α W)
    (h : d₁.boundedness = d₂.boundedness) :
    d₁.licensed = d₂.licensed := by
  simp [licensed, Boundedness.isLicensed, h]

/-- The deep isomorphism: a Kennedy numeral domain and a Rouillard E-TIA
    domain on a closed scale have identical licensing, despite using
    opposite monotonicity directions (atLeastDeg vs atMostDeg). -/
theorem kennedy_rouillard_same_licensing (μ₁ μ₂ : W → α) :
    (kennedyNumeral μ₁).licensed = (rouillardETIA μ₂ .closed).licensed := rfl

/-- All four frameworks agree: licensing depends solely on boundedness.
    Kennedy (2007): closed-scale adjectives license degree modifiers.
    Rouillard (2026): closed-runtime VPs license E-TIAs.
    Krifka (1989): QUA predicates yield telic (bounded) VPs.
    Zwarts (2005): bounded paths yield telic VPs.
    All four route through Boundedness.isLicensed. -/
theorem four_frameworks_agree
    (b : Boundedness) {W : Type*} (μ₁ μ₂ : W → α) :
    (MIPDomain.kennedyAdjective μ₁ b).licensed =
    (MIPDomain.rouillardETIA μ₂ b).licensed := rfl

end MIPDomain

-- ════════════════════════════════════════════════════
-- § 9. MIP = Kennedy's Type-Shift
-- ════════════════════════════════════════════════════

/-! The punchline: Kennedy's de-Fregean type-shift is not a separate mechanism.
    It IS the MIP applied to a monotone degree property. For both "at least"
    (Kennedy) and "at most" (Rouillard), max⊨ at world w = μ(w), the true
    value. So the MIP universally derives exact meaning from monotone
    degree properties, regardless of monotonicity direction.

    `isMaxInf_atLeast_iff_eq`: max⊨(atLeastDeg μ, m, w) ↔ μ(w) = m
    `isMaxInf_atMost_iff_eq`:  max⊨(atMostDeg μ, m, w)  ↔ μ(w) = m

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
-- § 10. ML Theory: Marginal and Large Differences
-- ════════════════════════════════════════════════════

/-! ### Dinis & Jacinto (2026) ML theory

ML theory enriches a linear order with a primitive "marginally smaller than"
relation M.  From R (= `<`) and M one derives L (largely smaller than):
L(x,y) := x < y ∧ ¬ M x y.  Five axioms govern M; Theorem 2.2 derives
M-TRANSITIVITY and M-BOUNDEDNESS as consequences.

This sits alongside `MIPDomain`: an `MIPDomain` determines licensing from
boundedness, while an `MLScale` adds granularity structure (marginal vs.
large difference) on the same `LinearOrder`.

- Dinis, B. & Jacinto, B. (2026). Marginality scales for gradable
  adjectives. *Linguistics and Philosophy* 49:101–131.
-/

/-- ML theory (Dinis & Jacinto 2026, Fig. 1): a linear order enriched with
    a primitive "marginally smaller than" relation M satisfying five axioms.
    The strict order `<` from `LinearOrder` is the paper's R;
    L (largely smaller) is derived as R ∧ ¬M. -/
structure MLScale (α : Type*) [LinearOrder α] where
  /-- x is marginally smaller than y (primitive) -/
  M : α → α → Prop
  /-- Axiom 1: ∃ x y, L(x,y) — largely different elements exist -/
  exists_large : ∃ x y, x < y ∧ ¬ M x y
  /-- Axiom 2: M(x,y) → R(x,y) -/
  m_implies_lt : ∀ x y, M x y → x < y
  /-- Axiom 3 (M-IRRELEVANCE): marginal steps preserve large-gap structure -/
  m_irrelevance : ∀ x y z, M x y →
    ((z < y ∧ ¬ M z y → z < x ∧ ¬ M z x) ∧
     (x < z ∧ ¬ M x z → y < z ∧ ¬ M y z))
  /-- Axiom 4: R extends along L — smaller-than propagates through large gaps -/
  r_extends_l : ∀ x y z, x < y →
    ((y < z ∧ ¬ M y z → x < z ∧ ¬ M x z) ∧
     (z < x ∧ ¬ M z x → z < y ∧ ¬ M z y))
  /-- Axiom 5 (DECOMPOSITION): every large gap decomposes via a marginal step -/
  decomposition : ∀ x y, (x < y ∧ ¬ M x y) →
    (∃ z, M x z ∧ z < y ∧ ¬ M z y) ∧ (∃ w, M w y ∧ x < w ∧ ¬ M x w)

namespace MLScale

variable {α : Type*} [LinearOrder α] (ml : MLScale α)

/-- Largely smaller than (Def 2.1): R(x,y) ∧ ¬M(x,y). -/
def L (x y : α) : Prop := x < y ∧ ¬ ml.M x y

/-- Marginal difference (Def 2.3): M(x,y) ∨ M(y,x). -/
def MarginalDiff (x y : α) : Prop := ml.M x y ∨ ml.M y x

/-- At most marginal difference: x = y ∨ MarginalDiff(x,y).
    The equivalence relation on degrees induced by M. -/
def AtMostMarginal (x y : α) : Prop := x = y ∨ ml.MarginalDiff x y

/-- Large difference: L(x,y) ∨ L(y,x). -/
def LargeDiff (x y : α) : Prop := ml.L x y ∨ ml.L y x

/-- **Theorem 2.2, part 1 (M-TRANSITIVITY)**: M is transitive.
    If x is marginally smaller than y and y marginally smaller than z,
    then x is marginally smaller than z.
    Proof: ¬L(y,z) since M(y,z); Axiom 3 contrapositive gives ¬L(x,z);
    since R(x,z), this forces M(x,z). -/
theorem m_transitive (x y z : α) (hxy : ml.M x y) (hyz : ml.M y z) :
    ml.M x z := by
  by_contra h
  exact ((ml.m_irrelevance x y z hxy).2
    ⟨lt_trans (ml.m_implies_lt x y hxy) (ml.m_implies_lt y z hyz), h⟩).2 hyz

/-- **Theorem 2.2, part 2 (M-BOUNDEDNESS)**: if x is marginally smaller
    than z and y is between them (x < y < z), then both gaps are marginal. -/
theorem m_bounded (x y z : α) (hxz : ml.M x z) (hxy : x < y) (hyz : y < z) :
    ml.M x y ∧ ml.M y z := by
  constructor
  · by_contra h
    exact absurd ((ml.m_irrelevance x z y hxz).2 ⟨hxy, h⟩).1
      (not_lt.mpr (le_of_lt hyz))
  · by_contra h
    exact absurd ((ml.m_irrelevance x z y hxz).1 ⟨hyz, h⟩).1
      (not_lt.mpr (le_of_lt hxy))

end MLScale

-- ════════════════════════════════════════════════════
-- § 11. Discrete Bounded Scales
-- ════════════════════════════════════════════════════

/-! ### Degree and Threshold types for finite scales

Discretized scale types for gradable adjective RSA computations.
`Degree max` wraps `Fin (max + 1)` with `LinearOrder`, `BoundedOrder`, `Fintype`.
`Threshold max` wraps `Fin max` with coercion to `Degree max`.

These participate in the abstract `MIPDomain` infrastructure above via their
`LinearOrder` and `BoundedOrder` instances. -/

/-- A degree on a scale from 0 to max. Represents discretized continuous
    values like height, temperature, etc. -/
structure Degree (max : Nat) where
  value : Fin (max + 1)
  deriving Repr, DecidableEq, BEq

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
  deriving Repr, DecidableEq, BEq

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

/-! ### Bool-valued degree comparisons

Bool wrappers around the Prop-valued degree properties from § 6.
These are the single source of truth for degree semantics at the
computation level — adjective meanings, numeral meanings, and RSA
domains all go through these. -/

/-- Bool wrapper for `moreThanDeg`: `μ(w) > d`. -/
def moreThanDeg? {W : Type*} (μ : W → α) (d : α) (w : W) : Bool :=
  decide (μ w > d)

/-- Bool wrapper for `lessThanDeg`: `μ(w) < d`. -/
def lessThanDeg? {W : Type*} (μ : W → α) (d : α) (w : W) : Bool :=
  decide (μ w < d)

/-- Bool wrapper for `atMostDeg`: `μ(w) ≤ d`. -/
def atMostDeg? {W : Type*} (μ : W → α) (d : α) (w : W) : Bool :=
  decide (μ w ≤ d)

/-- Bool wrapper for `atLeastDeg`: `μ(w) ≥ d`. -/
def atLeastDeg? {W : Type*} (μ : W → α) (d : α) (w : W) : Bool :=
  decide (μ w ≥ d)

/-- Bool wrapper for `eqDeg`: `μ(w) = d`. -/
def eqDeg? {W : Type*} (μ : W → α) (d : α) (w : W) : Bool :=
  decide (μ w = d)

theorem moreThanDeg?_iff {W : Type*} (μ : W → α) (d : α) (w : W) :
    moreThanDeg? μ d w = true ↔ moreThanDeg μ d w := by
  simp [moreThanDeg?, moreThanDeg, decide_eq_true_eq]

theorem lessThanDeg?_iff {W : Type*} (μ : W → α) (d : α) (w : W) :
    lessThanDeg? μ d w = true ↔ lessThanDeg μ d w := by
  simp [lessThanDeg?, lessThanDeg, decide_eq_true_eq]

theorem atMostDeg?_iff {W : Type*} (μ : W → α) (d : α) (w : W) :
    atMostDeg? μ d w = true ↔ atMostDeg μ d w := by
  simp [atMostDeg?, atMostDeg, decide_eq_true_eq]

theorem atLeastDeg?_iff {W : Type*} (μ : W → α) (d : α) (w : W) :
    atLeastDeg? μ d w = true ↔ atLeastDeg μ d w := by
  simp [atLeastDeg?, atLeastDeg, decide_eq_true_eq]

theorem eqDeg?_iff {W : Type*} (μ : W → α) (d : α) (w : W) :
    eqDeg? μ d w = true ↔ eqDeg μ d w := by
  simp [eqDeg?, eqDeg, decide_eq_true_eq]

-- ════════════════════════════════════════════════════
-- § 13. Measure Function Typeclass
-- ════════════════════════════════════════════════════

/-- Typeclass for entities that have a degree/magnitude on some scale.
    This is the formal semantics "measure function" μ : Entity → Degree. -/
class HasDegree (E : Type) where
  degree : E → ℚ

-- ════════════════════════════════════════════════════
-- § 14. Epistemic Comparative Likelihood (Holliday & Icard 2013)
-- ════════════════════════════════════════════════════

/-! ### Epistemic likelihood scales @cite{holliday-icard-2013}

Holliday & Icard (2013) study the logic of "at least as likely as" (≿) on
propositions, defining a hierarchy of axiom systems (W ⊂ F ⊂ FA) whose
qualitative additivity axiom is the epistemic counterpart of `AdditiveScale.fa`.
This fills the `EpistemicScale` arm of the categorical diagram (§ 0).

**Axiom hierarchy** (Table 1):

| System | Axioms         | Semantics                          |
|--------|----------------|------------------------------------|
| W      | R, T           | World-ordering + Halpern lift      |
| F      | R, T, F        | + bottom element                   |
| FA     | R, T, F, A     | Finitely additive measures         |

**Bridge**: Axiom A (epistemic qualitative additivity) and `AdditiveScale.fa`
(mereological finite additivity) are algebraically equivalent — both express
that a comparison factors through disjoint parts.

References:
- Holliday, W. & Icard, T. (2013). Measure Semantics and Qualitative
  Semantics for Epistemic Modals. SALT 23: 514–534.
- Halpern, J. (2003). Reasoning about Uncertainty. MIT Press.
- van der Hoek, W. (1996). Qualitative modalities. IJUFKS 4(1).
-/

-- ── Axioms (Table 1) ────────────────────────────

/-- Axiom R: reflexivity — A ≿ A. -/
def EpistemicAxiom.R {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A, ge A A

/-- Axiom T: monotonicity — A ⊆ B → B ≿ A. -/
def EpistemicAxiom.T {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A B, A ⊆ B → ge B A

/-- Axiom F: Ω ≿ ∅ — tautology is at least as likely as contradiction. -/
def EpistemicAxiom.F {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ge Set.univ ∅

/-- Axiom S: supplementation — A ≿ B → Bᶜ ≿ Aᶜ. -/
def EpistemicAxiom.S {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A B, ge A B → ge Bᶜ Aᶜ

/-- Axiom A: qualitative additivity — A ≿ B ↔ (A \ B) ≿ (B \ A).
    The comparative likelihood factors through disjoint parts. -/
def EpistemicAxiom.A {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A B, ge A B ↔ ge (A \ B) (B \ A)

/-- Axiom J: join — A ≿ C ∧ B ≿ C ∧ A ∩ B = ∅ → A ∪ B ≿ C. -/
def EpistemicAxiom.J {W : Type*} (ge : Set W → Set W → Prop) : Prop :=
  ∀ A B C, ge A C → ge B C → (∀ x, x ∈ A → x ∉ B) → ge (A ∪ B) C

-- ── Logic Hierarchy ─────────────────────────────

/-- System W: the weakest epistemic likelihood logic.
    Reflexivity + monotonicity (Holliday & Icard 2013, Table 1). -/
structure EpistemicSystemW (W : Type*) where
  ge : Set W → Set W → Prop
  refl : EpistemicAxiom.R ge
  mono : EpistemicAxiom.T ge

/-- System F: System W + Ω ≿ ∅. -/
structure EpistemicSystemF (W : Type*) extends EpistemicSystemW W where
  bottom : EpistemicAxiom.F ge

/-- System FA: System F + qualitative additivity.
    Characterizes finitely additive probability orderings
    (Holliday & Icard 2013, Fact 14). -/
structure EpistemicSystemFA (W : Type*) extends EpistemicSystemF W where
  additive : EpistemicAxiom.A ge

-- ── Measure Semantics ───────────────────────────

/-- A finitely additive probability measure on subsets of W. -/
structure FinAddMeasure (W : Type*) where
  /-- The measure function -/
  mu : Set W → ℚ
  /-- Non-negativity -/
  nonneg : ∀ A, 0 ≤ mu A
  /-- Finite additivity: μ(A ∪ B) = μ(A) + μ(B) when A ∩ B = ∅ -/
  additive : ∀ A B, (∀ x, x ∈ A → x ∉ B) → mu (A ∪ B) = mu A + mu B
  /-- Normalization -/
  total : mu Set.univ = 1

namespace FinAddMeasure

variable {W : Type*}

/-- Measure-induced comparative likelihood: A ≿ B ↔ μ(A) ≥ μ(B). -/
def inducedGe (m : FinAddMeasure W) (A B : Set W) : Prop :=
  m.mu A ≥ m.mu B

/-- Measure-induced ≿ is reflexive. -/
theorem inducedGe_axiomR (m : FinAddMeasure W) :
    EpistemicAxiom.R m.inducedGe :=
  fun _ => le_refl _

/-- Measure-induced ≿ satisfies monotonicity.
    A ⊆ B → B = A ∪ (B \ A) → μ(B) = μ(A) + μ(B \ A) ≥ μ(A). -/
theorem inducedGe_axiomT (m : FinAddMeasure W) :
    EpistemicAxiom.T m.inducedGe := by
  intro A B hAB
  show m.mu B ≥ m.mu A
  have hdecomp : B = A ∪ (B \ A) := (Set.union_diff_cancel hAB).symm
  have hdisj : ∀ x, x ∈ A → x ∉ B \ A := fun x hx ⟨_, hna⟩ => hna hx
  rw [hdecomp, m.additive A (B \ A) hdisj]
  exact le_add_of_nonneg_right (m.nonneg (B \ A))

/-- A finitely additive measure induces System FA. -/
def toSystemFA (m : FinAddMeasure W) : EpistemicSystemFA W where
  ge := m.inducedGe
  refl := m.inducedGe_axiomR
  mono := m.inducedGe_axiomT
  bottom := by
    show m.mu Set.univ ≥ m.mu ∅
    have hempty : m.mu (∅ ∪ ∅) = m.mu ∅ + m.mu ∅ :=
      m.additive ∅ ∅ (fun x hx => hx.elim)
    simp only [Set.empty_union] at hempty
    have hzero : m.mu ∅ = 0 := by
      have h : m.mu ∅ + m.mu ∅ = m.mu ∅ + 0 := by rw [add_zero]; exact hempty.symm
      exact add_left_cancel h
    rw [hzero]; exact m.nonneg Set.univ
  additive := by
    intro A B
    show m.mu A ≥ m.mu B ↔ m.mu (A \ B) ≥ m.mu (B \ A)
    have hdA : ∀ x, x ∈ A \ B → x ∉ A ∩ B := fun x ⟨_, hxnb⟩ ⟨_, hxb⟩ => hxnb hxb
    have hdB : ∀ x, x ∈ B \ A → x ∉ A ∩ B := fun x ⟨_, hxna⟩ ⟨hxa, _⟩ => hxna hxa
    have hmuA : m.mu A = m.mu (A \ B) + m.mu (A ∩ B) := by
      conv_lhs => rw [(Set.diff_union_inter A B).symm]
      exact m.additive _ _ hdA
    have hmuB : m.mu B = m.mu (B \ A) + m.mu (A ∩ B) := by
      conv_lhs => rw [show B = (B \ A) ∪ (A ∩ B) from by
        rw [Set.inter_comm]; exact (Set.diff_union_inter B A).symm]
      exact m.additive _ _ hdB
    rw [hmuA, hmuB]
    exact add_le_add_iff_right (m.mu (A ∩ B))

end FinAddMeasure

-- ── World-Ordering Semantics ────────────────────

/-- Halpern's lifting: a preorder on worlds induces a comparison on
    propositions. A ≿ B iff for every b ∈ B, ∃ a ∈ A with a ≥_w b.
    Holliday & Icard (2013) §3: characterizes System W (Thm 21). -/
def halpernLift {W : Type*} (ge_w : W → W → Prop) (A B : Set W) : Prop :=
  ∀ b, b ∈ B → ∃ a, a ∈ A ∧ ge_w a b

/-- Halpern lift from a reflexive relation satisfies Axiom R. -/
theorem halpernLift_axiomR {W : Type*} {ge_w : W → W → Prop}
    (hRefl : ∀ w, ge_w w w) :
    EpistemicAxiom.R (halpernLift ge_w) :=
  fun _ b hb => ⟨b, hb, hRefl b⟩

/-- Halpern lift from a reflexive relation satisfies Axiom T.
    If A ⊆ B and b ∈ A, then b ∈ B, so take a = b. -/
theorem halpernLift_axiomT {W : Type*} {ge_w : W → W → Prop}
    (hRefl : ∀ w, ge_w w w) :
    EpistemicAxiom.T (halpernLift ge_w) :=
  fun _ _ hAB b hbA => ⟨b, hAB hbA, hRefl b⟩

/-- Halpern lift from a reflexive preorder yields System W. -/
def halpernSystemW {W : Type*} (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w) :
    EpistemicSystemW W where
  ge := halpernLift ge_w
  refl := halpernLift_axiomR hRefl
  mono := halpernLift_axiomT hRefl

-- ── Representation Theorems ─────────────────────

/-- **Fact 14** (Holliday & Icard 2013; van der Hoek 1996):
    System FA characterizes finitely additive event orderings.
    ≿ satisfies FA iff it is representable by a finitely additive
    probability measure. -/
theorem fa_characterizes_measure {W : Type*} (sys : EpistemicSystemFA W) :
    ∃ (m : FinAddMeasure W), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  sorry -- Deep: constructing a measure from qualitative axioms (Krantz et al. 1971)

/-- **Theorem 21** (Holliday & Icard 2013):
    System W characterizes world-ordering semantics with Halpern's lift. -/
theorem w_characterizes_halpern {W : Type*} (sys : EpistemicSystemW W) :
    ∃ (ge_w : W → W → Prop), (∀ w, ge_w w w) ∧
      ∀ A B, sys.ge A B ↔ halpernLift ge_w A B :=
  sorry -- Deep: constructing a world ordering from proposition ordering

-- ── Bridge: Axiom A ↔ FA ────────────────────────

/-- **Algebraic bridge**: Axiom A and the finite additivity property
    of `AdditiveScale` are equivalent for any comparison on sets.
    - FA: ge A B ↔ ge (A ∪ C) (B ∪ C) when C disjoint from A and B
    - Axiom A: ge A B ↔ ge (A \ B) (B \ A)
    Proof sketch:
    - A → FA: (A∪C)\(B∪C) = A\B when A∩C = ∅; apply A twice.
    - FA → A: take C = A ∩ B; (A\B)∪(A∩B) = A; apply FA. -/
theorem axiomA_iff_fa {W : Type*} (ge : Set W → Set W → Prop) :
    EpistemicAxiom.A ge ↔
    (∀ A B C : Set W, (∀ x, x ∈ A → x ∉ C) → (∀ x, x ∈ B → x ∉ C) →
      (ge A B ↔ ge (A ∪ C) (B ∪ C))) :=
  sorry -- Set algebra: both directions require decomposition identities

-- ── EpistemicTag + Five Frameworks ──────────────

/-- Binary epistemic classification, parallel to `MereoTag`.
    - `finitelyAdditive`: probability-representable (System FA), closed
    - `qualitative`: general comparative (System W only), open -/
inductive EpistemicTag where
  | finitelyAdditive  -- FA: closed, probability-representable
  | qualitative       -- W: no guaranteed bounds, open
  deriving DecidableEq, BEq, Repr

instance : LicensingPipeline EpistemicTag where
  toBoundedness
    | .finitelyAdditive => .closed
    | .qualitative => .open_

/-- FA epistemic scales are licensed (closed → admits optimum). -/
theorem epistemicFA_licensed :
    LicensingPipeline.isLicensed EpistemicTag.finitelyAdditive = true := rfl

/-- Qualitative epistemic scales are blocked (open → no optimum). -/
theorem epistemicQualitative_blocked :
    LicensingPipeline.isLicensed EpistemicTag.qualitative = false := rfl

/-- **Five frameworks agree on licensing**: Kennedy (adjective degree
    boundedness), Rouillard (temporal MIP), Krifka (mereological QUA/CUM),
    Zwarts (path shape), and Holliday–Icard (epistemic likelihood) all
    route through `Boundedness.isLicensed` via `LicensingPipeline`.

    This extends `four_frameworks_agree` with the epistemic arm:
    epistemic FA ↔ mereological QUA ↔ closed → licensed;
    epistemic qualitative ↔ mereological CUM ↔ open → blocked. -/
theorem five_frameworks_agree
    (m : MereoTag) (e : EpistemicTag)
    (h : LicensingPipeline.toBoundedness m = LicensingPipeline.toBoundedness e) :
    LicensingPipeline.isLicensed m = LicensingPipeline.isLicensed e :=
  LicensingPipeline.universal m e h

/-- Epistemic FA agrees with mereological QUA. -/
theorem epistemicFA_eq_qua :
    LicensingPipeline.isLicensed EpistemicTag.finitelyAdditive =
    LicensingPipeline.isLicensed MereoTag.qua := rfl

/-- Epistemic qualitative agrees with mereological CUM. -/
theorem epistemicQualitative_eq_cum :
    LicensingPipeline.isLicensed EpistemicTag.qualitative =
    LicensingPipeline.isLicensed MereoTag.cum := rfl

end Core.Scale
