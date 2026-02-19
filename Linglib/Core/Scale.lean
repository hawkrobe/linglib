import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Max
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Rat.Defs

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
MereoScale   EpistemicScale          │
    │              │                  │
    │  additive    │  additive        │  μ
    │  representation  representation │
    ▼              ▼                  ▼
                  (ℚ, ≤)
```

**Objects**: `ComparativeScale α` — a preorder with boundedness classification.

**Morphisms**: `ScaleMorphism` — monotone maps between comparative scales.
  Generalizes `MereoDim` (which is `StrictMono` = injective scale morphism).

**Enriched subcategory**: `AdditiveScale α` — comparative scale with join and
  finite additivity (FA). Two independent instances:
  - Mereological: `ExtMeasure.additive` (Krifka 1989)
  - Epistemic: probability measure (Holliday & Icard 2013)

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
-- § 1b. Comparative Scale (Root Algebraic Structure)
-- ════════════════════════════════════════════════════

/-- A comparative scale: a preorder with a boundedness classification.
    This is the root object in the category of scales. All scale-based
    reasoning in linglib (degree semantics, mereological measurement,
    epistemic comparison) factors through this structure.

    Krantz et al. (1971): a comparative scale is an ordered set with
    enough structure to support qualitative comparison. -/
structure ComparativeScale (α : Type*) where
  /-- The ordering relation -/
  le : α → α → Prop
  /-- Reflexivity -/
  le_refl : ∀ (x : α), le x x
  /-- Transitivity -/
  le_trans : ∀ (x y z : α), le x y → le y z → le x z
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
      Join is Mathlib's `⊔` from `SemilatticeSup`. -/
  fa : ∀ (x y z : α), disjoint x z → disjoint y z →
    (le x y ↔ le (x ⊔ z) (y ⊔ z))

/-- A scale morphism: a monotone map between comparative scales.
    Generalizes `MereoDim` (= injective scale morphism = `StrictMono`). -/
def ScaleMorphism {α β : Type*}
    (S₁ : ComparativeScale α) (S₂ : ComparativeScale β)
    (f : α → β) : Prop :=
  ∀ (x y : α), S₁.le x y → S₂.le (f x) (f y)

namespace ComparativeScale

/-- Lift a Mathlib `Preorder` to a `ComparativeScale`. -/
def ofPreorder (α : Type*) [Preorder α] (b : Boundedness) :
    ComparativeScale α where
  le := (· ≤ ·)
  le_refl := _root_.le_refl
  le_trans := fun _ _ _ => _root_.le_trans
  boundedness := b

/-- Lift a Mathlib `LinearOrder` to a `ComparativeScale`. -/
def ofLinearOrder (α : Type*) [LinearOrder α] (b : Boundedness) :
    ComparativeScale α :=
  ofPreorder α b

/-- Licensing prediction from the underlying boundedness. -/
def isLicensed {α : Type*} (S : ComparativeScale α) : Bool :=
  S.boundedness.isLicensed

end ComparativeScale

-- ── Morphism theorems (categorical structure) ────

namespace ScaleMorphism

/-- Identity is a scale morphism. -/
theorem id {α : Type*} (S : ComparativeScale α) :
    ScaleMorphism S S _root_.id :=
  fun _ _ h => h

/-- Composition of scale morphisms is a scale morphism. -/
theorem comp {α β γ : Type*}
    {S₁ : ComparativeScale α} {S₂ : ComparativeScale β} {S₃ : ComparativeScale γ}
    {g : β → γ} {f : α → β}
    (hg : ScaleMorphism S₂ S₃ g) (hf : ScaleMorphism S₁ S₂ f) :
    ScaleMorphism S₁ S₃ (g ∘ f) :=
  fun x y h => hg _ _ (hf x y h)

/-- A constant map is a scale morphism (into any scale). -/
theorem const {α β : Type*}
    (S₁ : ComparativeScale α) (S₂ : ComparativeScale β) (b : β) :
    ScaleMorphism S₁ S₂ (fun _ => b) :=
  fun _ _ _ => S₂.le_refl b

/-- Every `Monotone` function between preorders is a scale morphism.
    This is the bridge from Mathlib's order theory into the categorical
    framework: any monotone map lifts to a `ScaleMorphism`. -/
theorem ofMonotone {α β : Type*}
    [Preorder α] [Preorder β] {f : α → β}
    (hf : Monotone f) (b₁ b₂ : Boundedness) :
    ScaleMorphism (ComparativeScale.ofPreorder α b₁)
                  (ComparativeScale.ofPreorder β b₂) f :=
  fun _ _ hxy => hf hxy

/-- Every `StrictMono` function is a scale morphism (since `StrictMono → Monotone`).
    This connects `MereoDim` (strictly monotone maps between partial orders)
    to the categorical framework. -/
theorem ofStrictMono {α β : Type*}
    [PartialOrder α] [Preorder β] {f : α → β}
    (hf : StrictMono f) (b₁ b₂ : Boundedness) :
    ScaleMorphism (ComparativeScale.ofPreorder α b₁)
                  (ComparativeScale.ofPreorder β b₂) f :=
  ofMonotone hf.monotone b₁ b₂

end ScaleMorphism

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
  { ComparativeScale.ofLinearOrder α .closed with
    measure := μ, degProp := atLeastDeg μ }

/-- Kennedy (2007) gradable adjective domain.
    Boundedness varies by adjective class (tall: open, full: closed). -/
def kennedyAdjective (μ : W → α) (b : Boundedness) : MIPDomain α W :=
  { ComparativeScale.ofLinearOrder α b with
    measure := μ, degProp := atLeastDeg μ }

/-- Rouillard (2026) E-TIA domain: event runtime ≤ interval size.
    Boundedness determined by Vendler class (telic → closed, atelic → open). -/
def rouillardETIA (μ : W → α) (b : Boundedness) : MIPDomain α W :=
  { ComparativeScale.ofLinearOrder α b with
    measure := μ, degProp := atMostDeg μ }

/-- Rouillard (2026) G-TIA domain: PTS extent on open intervals.
    Always open → always blocked (information collapse). -/
def rouillardGTIA (μ : W → α) : MIPDomain α W :=
  { ComparativeScale.ofLinearOrder α .open_ with
    measure := μ, degProp := atMostDeg μ }

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

end Core.Scale
