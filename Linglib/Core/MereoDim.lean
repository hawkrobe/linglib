import Linglib.Core.Mereology
import Linglib.Core.MeasurementScale

/-!
# Mereology ↔ MeasurementScale Bridge

Cross-pillar connection between `Core/Mereology.lean` (CUM/QUA/ExtMeasure)
and `Core/MeasurementScale.lean` (Boundedness/MIP/degree properties).

The two pillars are independently motivated:
- **Mereology**: algebraic part-whole structure (Krifka 1989/1998, Champollion 2017)
- **MeasurementScale**: degree/scale structure (Kennedy 2007, Rouillard 2026)

This file bridges them:

- **Annotation bridge** (§1): QUA ↔ `Boundedness.closed`, CUM ↔ `Boundedness.open_`
- **Constructor bridge** (§2): `ExtMeasure` → `MIPDomain`
- **Structural support** (§3–4): `singleton_qua` ↔ `.closed`, CUM sum extensibility

## The GRAD square (lax commutativity)

The Krifka (1989/1998) linking theory involves two dimension chains:

```
Events →θ Entities →μ ℚ       (object dimension)
Events →τ Times    →dur ℚ     (temporal dimension)
```

These form a square that commutes *laxly*: the two paths Events → ℚ need not
agree pointwise, but they are related by a proportionality constant (the "rate"
of gradual change). This is captured by `MeasureProportional.rate` in
`Events/Krifka1998.lean`.

## References

- Krifka, M. (1989). Nominal reference, temporal constitution and
  quantification in event semantics.
- Krifka, M. (1998). The origins of telicity.
- Kennedy, C. (2007). Vagueness and grammar.
- Rouillard, V. (2026). Maximal informativity and temporal in-adverbials.
- Champollion, L. (2017). *Parts of a Whole*. OUP.
-/

namespace Mereology

-- ════════════════════════════════════════════════════
-- § 1. Mereological Scale Annotations
-- ════════════════════════════════════════════════════

/-- QUA predicates correspond to closed/bounded scales.

    Krifka: QUA(P) means P-elements have no P-proper-parts, so
    measurement reaches a definite value at each P-element — the scale
    has an inherent endpoint.
    Kennedy (2007): closed scales license degree modifiers.
    Rouillard (2026): closed scales license temporal *in*-adverbials.

    This is the mereological root of the Kennedy–Rouillard isomorphism:
    QUA → telic → closed → licensed. -/
def quaBoundedness : Core.Scale.Boundedness := .closed

/-- CUM predicates correspond to open/unbounded scales.

    Krifka: CUM(P) means P is closed under ⊔, so measurement can
    always be extended upward — the scale has no inherent endpoint.
    Kennedy (2007): open scales block degree modifiers.
    Rouillard (2026): open scales cause information collapse for TIAs.

    This is the mereological root: CUM → atelic → open → blocked. -/
def cumBoundedness : Core.Scale.Boundedness := .open_

/-- QUA → licensed: closed scales admit maximally informative elements. -/
theorem qua_boundedness_licensed : quaBoundedness.isLicensed = true := rfl

/-- CUM → blocked: open scales have information collapse. -/
theorem cum_boundedness_blocked : cumBoundedness.isLicensed = false := rfl

-- ════════════════════════════════════════════════════
-- § 2. ExtMeasure → MIPDomain Constructor
-- ════════════════════════════════════════════════════

/-- An extensive measure induces a Kennedy-style MIP domain.

    The measure function μ : α → ℚ from `ExtMeasure` becomes the
    measure function of a `MIPDomain`, with `atLeastDeg` as the degree
    property (Kennedy 2007/2015: "at least n" with type-shift to exact).
    The boundedness annotation comes from the mereological property
    of the source predicate: QUA → `.closed`, CUM → `.open_`.

    See also `extMeasure_rouillardMIP` for the Rouillard (2026)
    direction (`atMostDeg`). -/
def extMeasure_kennedyMIP {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} (_hμ : ExtMeasure α μ) (b : Core.Scale.Boundedness) :
    Core.Scale.MIPDomain ℚ α :=
  { measure := μ, degProp := Core.Scale.atLeastDeg μ, boundedness := b }

/-- An extensive measure induces a Rouillard-style MIP domain.

    Same measure function, but with `atMostDeg` as the degree property
    (Rouillard 2026: E-TIA semantics uses "at most n" for runtime bounds).
    Boundedness again from the mereological source predicate. -/
def extMeasure_rouillardMIP {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} (_hμ : ExtMeasure α μ) (b : Core.Scale.Boundedness) :
    Core.Scale.MIPDomain ℚ α :=
  { measure := μ, degProp := Core.Scale.atMostDeg μ, boundedness := b }

/-- QUA predicates yield licensed Kennedy MIPDomains. -/
theorem qua_kennedyMIP_licensed {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} (hμ : ExtMeasure α μ) :
    (extMeasure_kennedyMIP hμ quaBoundedness).licensed = true := rfl

/-- CUM predicates yield blocked Kennedy MIPDomains. -/
theorem cum_kennedyMIP_blocked {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} (hμ : ExtMeasure α μ) :
    (extMeasure_kennedyMIP hμ cumBoundedness).licensed = false := rfl

/-- The Kennedy–Rouillard direction invariance for mereological domains:
    a QUA-induced MIPDomain is licensed regardless of whether we use
    Kennedy's `atLeastDeg` or Rouillard's `atMostDeg`. -/
theorem qua_direction_invariant {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} (hμ : ExtMeasure α μ) :
    (extMeasure_kennedyMIP hμ quaBoundedness).licensed =
    (extMeasure_rouillardMIP hμ quaBoundedness).licensed := rfl

-- ════════════════════════════════════════════════════
-- § 3. singleton_qua ↔ Boundedness.closed
-- ════════════════════════════════════════════════════

/-- Singletons are both QUA (mereologically) and closed (scale-theoretically).

    `singleton_qua n` proves `{x | x = n}` is quantized.
    A singleton set `{n}` has both a maximum and minimum (namely `n`
    itself), so its scale boundedness is `.closed`.

    This is the base case of the QUA ↔ Boundedness correspondence:
    the simplest QUA predicate (a singleton) maps to the simplest
    closed scale (a point). The connection is non-trivial:
    `singleton_qua` is proved from `lt_irrefl` (mereological), while
    `.closed` is a scale-theoretic classification — two independent
    proofs arriving at the same conclusion. -/
theorem singleton_qua_closed (n : ℚ) :
    QUA (· = n) ∧ quaBoundedness = Core.Scale.Boundedness.closed :=
  ⟨singleton_qua n, rfl⟩

/-- ExtMeasure singletons `{x | μ(x) = n}` are QUA and correspond to
    closed scales. Combines `extMeasure_qua'` (mereological) with the
    boundedness annotation (scale-theoretic).

    This is the measure-theoretic version of `singleton_qua_closed`:
    measuring a QUA predicate by an extensive measure yields a singleton
    on the scale (exactly one measure value), which is closed. -/
theorem extMeasure_singleton_closed {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ] (n : ℚ) :
    QUA (fun x => μ x = n) ∧ quaBoundedness = Core.Scale.Boundedness.closed :=
  ⟨extMeasure_qua' n, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. CUM Sum Extensibility
-- ════════════════════════════════════════════════════

/-- CUM predicates with incomparable elements can always produce larger
    measure values via sum.

    If P is CUM and has elements x, y where x ≤ y fails (they are
    incomparable), then x ⊔ y satisfies P (by CUM) and μ(x ⊔ y) > μ(y)
    (because y < x ⊔ y and μ is StrictMono).

    This is the structural mechanism behind open/unbounded scales for
    CUM predicates: given fresh material, CUM can always produce a
    larger measurement. The incomparability condition is satisfied
    whenever two P-elements have non-overlapping parts (e.g., two
    distinct portions of rice, two non-overlapping running events). -/
theorem cum_sum_exceeds {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ]
    {P : α → Prop} (hCum : CUM P)
    {x y : α} (hx : P x) (hy : P y) (h_not_le : ¬ x ≤ y) :
    P (x ⊔ y) ∧ μ (x ⊔ y) > μ y := by
  constructor
  · exact hCum x y hx hy
  · have hle : y ≤ x ⊔ y := le_sup_right
    have hne : y ≠ x ⊔ y := by
      intro heq; exact h_not_le (heq ▸ le_sup_left)
    exact hμ.strict_mono _ _ (lt_of_le_of_ne hle hne)

/-- CUM predicates with incomparable elements yield measure values
    strictly exceeding both inputs.

    Symmetric version of `cum_sum_exceeds`: μ(x ⊔ y) > μ(x) AND
    μ(x ⊔ y) > μ(y) when x and y are incomparable. -/
theorem cum_sum_exceeds_both {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ]
    {P : α → Prop} (hCum : CUM P)
    {x y : α} (hx : P x) (hy : P y)
    (hxy : ¬ x ≤ y) (hyx : ¬ y ≤ x) :
    P (x ⊔ y) ∧ μ (x ⊔ y) > μ x ∧ μ (x ⊔ y) > μ y := by
  refine ⟨hCum x y hx hy, ?_, (cum_sum_exceeds hCum hx hy hxy).2⟩
  have hle : x ≤ x ⊔ y := le_sup_left
  have hne : x ≠ x ⊔ y := by
    intro heq; exact hyx (heq ▸ le_sup_right)
  exact hμ.strict_mono _ _ (lt_of_le_of_ne hle hne)

end Mereology
