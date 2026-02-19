import Linglib.Core.Mereology
import Linglib.Core.Scale
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Field.Rat

/-!
# Mereology ↔ Scale Bridge

Cross-pillar connection between `Core/Mereology.lean` (CUM/QUA/ExtMeasure)
and `Core/Scale.lean` (ComparativeScale/Boundedness/MIP/degree properties).

The two pillars are independently motivated:
- **Mereology**: algebraic part-whole structure (Krifka 1989/1998, Champollion 2017)
- **Scale**: comparative/additive scale structure (Kennedy 2007, Rouillard 2026)

This file bridges them at four levels:

- **Annotation bridge** (§1): QUA ↔ `Boundedness.closed`, CUM ↔ `Boundedness.open_`
- **Constructor bridge** (§2): `ExtMeasure` → `MIPDomain`
- **Structural bridge** (§3–4): `singleton_qua` ↔ `.closed`, CUM sum extensibility
- **Categorical bridge** (§11): `MereoDim` → `Monotone`, `ExtMeasure` → `Monotone μ`

## The lax measure square

The Krifka (1989/1998) linking theory involves two dimension chains:

```
Events →θ Entities →μ ℚ       (object dimension)
Events →τ Times    →dur ℚ     (temporal dimension)
```

These form a square that commutes *laxly*: the two paths Events → ℚ need not
agree pointwise, but they are related by a proportionality constant (the "rate"
of gradual change). This is captured by `MeasureProportional` (§9) and
`LaxMeasureSquare` (§10) below. The SINC-specific extension `GRADSquare`
lives in `Events/Krifka1998.lean`.

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
  { boundedness := b, measure := μ, degProp := Core.Scale.atLeastDeg μ }

/-- An extensive measure induces a Rouillard-style MIP domain.

    Same measure function, but with `atMostDeg` as the degree property
    (Rouillard 2026: E-TIA semantics uses "at most n" for runtime bounds).
    Boundedness again from the mereological source predicate. -/
def extMeasure_rouillardMIP {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} (_hμ : ExtMeasure α μ) (b : Core.Scale.Boundedness) :
    Core.Scale.MIPDomain ℚ α :=
  { boundedness := b, measure := μ, degProp := Core.Scale.atMostDeg μ }

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

-- ════════════════════════════════════════════════════
-- § 5. MereoDim Typeclass
-- ════════════════════════════════════════════════════

/-- Morphism class of Mereo^op: the category of partially ordered types
    with strictly monotone maps. A `MereoDim d` instance witnesses that
    `d` is a mereological dimension — a map along which QUA pulls back.

    Unifies three sources of `StrictMono`:
    - `ExtMeasure` (via `extMeasure_strictMono`)
    - `IsSumHom` + `Injective` (via `strictMono_of_injective`)
    - Compositions of the above (Krifka dimension chains) -/
class MereoDim {α β : Type*} [PartialOrder α] [PartialOrder β]
    (d : α → β) : Prop where
  /-- The underlying strict monotonicity proof. -/
  toStrictMono : StrictMono d

-- ════════════════════════════════════════════════════
-- § 6. MereoDim Instances and Constructors
-- ════════════════════════════════════════════════════

/-- Any `ExtMeasure` is automatically a `MereoDim`: extensive measures
    are strictly monotone by `extMeasure_strictMono`. -/
instance instMereoDimOfExtMeasure {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ] : MereoDim μ :=
  ⟨extMeasure_strictMono hμ⟩

/-- An injective sum homomorphism is a `MereoDim`. Not an instance because
    `Function.Injective` is not inferrable by typeclass search. -/
def MereoDim.ofInjSumHom {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} [hf : IsSumHom f] (hinj : Function.Injective f) : MereoDim f :=
  ⟨hf.strictMono_of_injective hinj⟩

-- ════════════════════════════════════════════════════
-- § 7. MereoDim Composition
-- ════════════════════════════════════════════════════

/-- Composition of `MereoDim` morphisms. Captures Krifka's dimension
    chains: `Events →θ Entities →μ ℚ` gives `MereoDim (μ ∘ θ)` when
    both components are `MereoDim`.

    Stated as a theorem (not an instance) to avoid typeclass inference
    loops from decomposing arbitrary composed functions. -/
theorem MereoDim.comp {α β γ : Type*}
    [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {f : β → γ} {g : α → β} (hf : MereoDim f) (hg : MereoDim g) :
    MereoDim (f ∘ g) :=
  ⟨hf.toStrictMono.comp hg.toStrictMono⟩

-- ════════════════════════════════════════════════════
-- § 8. MereoDim QUA Pullback
-- ════════════════════════════════════════════════════

/-- QUA pullback via `MereoDim`: typeclass-dispatched version of
    `qua_pullback`. When `[MereoDim d]` is available (automatically
    for any `ExtMeasure`), QUA pulls back without manual `StrictMono`
    threading. -/
theorem qua_pullback_mereoDim {α β : Type*} [PartialOrder α] [PartialOrder β]
    {d : α → β} [hd : MereoDim d] {P : β → Prop} (hP : QUA P) :
    QUA (P ∘ d) :=
  qua_pullback hd.toStrictMono hP

/-- QUA pullback along a composed dimension chain. Given two `MereoDim`
    morphisms `d₁ : α → β` and `d₂ : β → γ`, QUA on γ pulls back to
    QUA on α through the chain `d₂ ∘ d₁`. -/
theorem qua_pullback_mereoDim_comp {α β γ : Type*}
    [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {d₁ : α → β} {d₂ : β → γ} (hd₁ : MereoDim d₁) (hd₂ : MereoDim d₂)
    {P : γ → Prop} (hP : QUA P) :
    QUA (P ∘ d₂ ∘ d₁) :=
  qua_pullback (hd₂.comp hd₁).toStrictMono hP

-- ════════════════════════════════════════════════════
-- § 9. Measure Proportionality
-- ════════════════════════════════════════════════════

/-- Measure proportionality: two measure functions are proportional on pairs
    related by a relation R. For any R-pair (x,e), μ₂(e) = rate * μ₁(x)
    for some positive constant `rate`.

    This captures the idealized "constant rate" linking two dimensions:
    measuring x is proportional to measuring e whenever R relates them.
    For instance, in Krifka's (1989) telicity theory, eating twice as much
    food takes twice as long, so the object measure and event duration are
    proportional on θ-related pairs. -/
structure MeasureProportional {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (R : α → β → Prop) (μ₁ : α → ℚ) (μ₂ : β → ℚ) where
  /-- The proportionality constant (rate). -/
  rate : ℚ
  /-- The rate is positive. -/
  rate_pos : 0 < rate
  /-- For any R-pair, μ₂(e) = rate × μ₁(x). -/
  proportional : ∀ (x : α) (e : β), R x e → μ₂ e = rate * μ₁ x

-- ════════════════════════════════════════════════════
-- § 10. Lax Measure Square
-- ════════════════════════════════════════════════════

/-- A lax commutative square of mereological dimensions:

    ```
    α →R γ →f β →μ₂ ℚ        (composed path: μ₂ ∘ f)
    α →──── μ₁ ────→ ℚ       (direct path)
    ```

    The two paths α → ℚ commute *laxly*: they don't agree pointwise,
    but are proportional on R-related pairs (via `MeasureProportional`).
    Both paths are required to be extensive measures (`ExtMeasure`),
    making them `MereoDim` morphisms that support QUA pullback.

    This is the general mereological square; `GRADSquare` in Krifka1998
    extends it with strict incrementality (SINC) to derive GRAD. -/
structure LaxMeasureSquare {α β γ : Type*}
    [SemilatticeSup α] [SemilatticeSup γ]
    (R : α → γ → Prop) (μ₁ : α → ℚ)
    (f : γ → β) (μ₂ : β → ℚ) where
  /-- Lax commutativity: μ₂(f(e)) = rate * μ₁(x) for R-pairs. -/
  laxComm : MeasureProportional R μ₁ (μ₂ ∘ f)
  /-- First arm is an extensive measure. -/
  ext₁ : ExtMeasure α μ₁
  /-- Second arm (composed path) is an extensive measure. -/
  ext₂ : ExtMeasure γ (μ₂ ∘ f)

/-- The defining equation of the lax measure square: for any R-pair (x,e),
    μ₂(f(e)) = rate * μ₁(x). -/
theorem LaxMeasureSquare.laxCommutativity {α β γ : Type*}
    [SemilatticeSup α] [SemilatticeSup γ]
    {R : α → γ → Prop} {μ₁ : α → ℚ}
    {f : γ → β} {μ₂ : β → ℚ}
    (sq : LaxMeasureSquare R μ₁ f μ₂)
    {x : α} {e : γ} (hR : R x e) :
    μ₂ (f e) = sq.laxComm.rate * μ₁ x :=
  sq.laxComm.proportional x e hR

/-- The first arm (direct path) is a `MereoDim` (via ExtMeasure). -/
theorem LaxMeasureSquare.mereoDim₁ {α β γ : Type*}
    [SemilatticeSup α] [SemilatticeSup γ]
    {R : α → γ → Prop} {μ₁ : α → ℚ}
    {f : γ → β} {μ₂ : β → ℚ}
    (sq : LaxMeasureSquare R μ₁ f μ₂) :
    MereoDim μ₁ := by
  haveI := sq.ext₁
  exact instMereoDimOfExtMeasure

/-- The second arm (composed path) is a `MereoDim` (via ExtMeasure). -/
theorem LaxMeasureSquare.mereoDim₂ {α β γ : Type*}
    [SemilatticeSup α] [SemilatticeSup γ]
    {R : α → γ → Prop} {μ₁ : α → ℚ}
    {f : γ → β} {μ₂ : β → ℚ}
    (sq : LaxMeasureSquare R μ₁ f μ₂) :
    MereoDim (μ₂ ∘ f) := by
  haveI := sq.ext₂
  exact instMereoDimOfExtMeasure

/-- QUA pullback through the composed path: QUA on ℚ pulls back to
    QUA on γ via the composed measure `μ₂ ∘ f`. -/
theorem LaxMeasureSquare.qua_pullback₂ {α β γ : Type*}
    [SemilatticeSup α] [SemilatticeSup γ]
    {R : α → γ → Prop} {μ₁ : α → ℚ}
    {f : γ → β} {μ₂ : β → ℚ}
    (sq : LaxMeasureSquare R μ₁ f μ₂)
    {P : ℚ → Prop} (hP : QUA P) :
    QUA (P ∘ μ₂ ∘ f) := by
  haveI := sq.ext₂
  exact qua_pullback_mereoDim hP

-- ════════════════════════════════════════════════════
-- § 11. MereoDim ↔ Monotone Bridge
-- ════════════════════════════════════════════════════

/-! ### The categorical connection

`MereoDim` is a strengthened morphism: it requires `StrictMono`
(injective monotone map between partial orders), while the categorical
morphism of comparative scales is `Monotone` (between preorders).

```
Monotone  ⊇  MereoDim  =  injective Monotone (on partial orders)
```

The bridge theorems below make this precise:

1. Every `MereoDim` is `Monotone` (`mereoDim_monotone`)
2. Every `ExtMeasure μ` gives `Monotone μ` (`extMeasure_monotone`)
3. `IsSumHom f → Monotone f` (`IsSumHom.monotone`, already in `Mereology.lean`)

The forgetful functor from AdditiveScale morphisms (IsSumHom) to
ComparativeScale morphisms (Monotone) is just `IsSumHom.monotone`.

Together with the boundedness annotations (§1: QUA → `.closed`, CUM → `.open_`)
and the `MIPDomain` constructors (§2), the entire mereological pipeline
factors through `ComparativeScale`:

```
  (α, ≤)  ——MereoDim d——→  (β, ≤)  ——ExtMeasure μ——→  (ℚ, ≤)
     ↓                        ↓                          ↓
ComparativeScale b₁      ComparativeScale b₂     ComparativeScale .closed
     └─────── Monotone ───────┘                          │
                └──────────── Monotone ──────────────────┘
```
-/

/-- Every `MereoDim d` is `Monotone`: the forgetful map from the category
    of partial orders with strict monotone maps to the category of
    preorders with monotone maps. -/
theorem mereoDim_monotone {α β : Type*}
    [PartialOrder α] [PartialOrder β]
    {d : α → β} (hd : MereoDim d) :
    Monotone d :=
  hd.toStrictMono.monotone

/-- Every `ExtMeasure μ` gives a monotone map to (ℚ, ≤). -/
theorem extMeasure_monotone {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} (hμ : ExtMeasure α μ) :
    Monotone μ :=
  (extMeasure_strictMono hμ).monotone

/-- **Boundedness coherence**: the mereological classification (QUA → `.closed`,
    CUM → `.open_`) is definitional — `ComparativeScale` is now just a
    boundedness tag on an ambient preorder, so the classification is stored
    directly as the `boundedness` field. -/
theorem qua_cum_boundedness_coherence :
    quaBoundedness = Core.Scale.Boundedness.closed ∧
    cumBoundedness = Core.Scale.Boundedness.open_ :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 12. DimensionChain Structure
-- ════════════════════════════════════════════════════

/-- A mereological dimension chain: a two-leg pipeline
    Source →f Inter →μ Measure where both legs are MereoDim.
    The three canonical instances:
    - Temporal: Events →τ Intervals →dur ℚ
    - Spatial:  Events →σ Paths     →dist ℚ
    - Object:   Events →θ Entities  →μ   ℚ  -/
structure DimensionChain
    {Source Inter Measure : Type*}
    [PartialOrder Source] [PartialOrder Inter] [PartialOrder Measure]
    (f : Source → Inter) (μ : Inter → Measure) where
  leg₁ : MereoDim f
  leg₂ : MereoDim μ

namespace DimensionChain

variable {Source Inter Measure : Type*}
    [PartialOrder Source] [PartialOrder Inter] [PartialOrder Measure]
    {f : Source → Inter} {μ : Inter → Measure}

/-- The composed map is a MereoDim. -/
def composed (dc : DimensionChain f μ) : MereoDim (μ ∘ f) :=
  MereoDim.comp dc.leg₂ dc.leg₁

/-- QUA on Measure pulls back to QUA on Source through the full chain. -/
theorem qua_transfer (dc : DimensionChain f μ)
    {P : Measure → Prop} (hP : QUA P) :
    QUA (P ∘ μ ∘ f) := by
  haveI := dc.composed
  exact qua_pullback_mereoDim hP

/-- QUA on Inter pulls back to QUA on Source through the first leg. -/
theorem qua_transfer_leg₁ (dc : DimensionChain f μ)
    {P : Inter → Prop} (hP : QUA P) :
    QUA (P ∘ f) := by
  haveI := dc.leg₁
  exact qua_pullback_mereoDim hP

/-- QUA on Measure pulls back to QUA on Inter through the second leg. -/
theorem qua_transfer_leg₂ (dc : DimensionChain f μ)
    {P : Measure → Prop} (hP : QUA P) :
    QUA (P ∘ μ) := by
  haveI := dc.leg₂
  exact qua_pullback_mereoDim hP

end DimensionChain

-- ════════════════════════════════════════════════════
-- § 13. Deep Mereological Bridge
-- ════════════════════════════════════════════════════

/-- CUM + fresh incomparable element → exists P-element with strictly
    larger measure. The structural content of "CUM → open scale."

    Given P(x) and fresh y with P(y) and ¬ y ≤ x, then x ⊔ y satisfies P
    (by CUM) and μ(x ⊔ y) > μ(x) (by StrictMono, since x < x ⊔ y). -/
theorem cum_exceeds_source {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ]
    {P : α → Prop} (hCum : CUM P)
    {x y : α} (hx : P x) (hy : P y) (hyx : ¬ y ≤ x) :
    P (x ⊔ y) ∧ μ (x ⊔ y) > μ x := by
  constructor
  · exact hCum x y hx hy
  · have hle : x ≤ x ⊔ y := le_sup_left
    have hne : x ≠ x ⊔ y := fun heq => hyx (heq ▸ le_sup_right)
    exact hμ.strict_mono _ _ (lt_of_le_of_ne hle hne)

/-- CUM + disjoint fresh supply with minimum measure → measurement unbounded.

    If P is CUM and for every P-element x there exists a disjoint P-element y
    with μ(y) ≥ δ > 0, then P-elements achieve arbitrarily large measure.
    This is the structural content of information collapse: CUM predicates
    with enough disjoint material have no inherent measurement ceiling.

    The hypothesis requires `¬ Overlap x y` (not merely `¬ y ≤ x`) because
    overlap allows the increment μ(x ⊔ y) - μ(x) to shrink to zero, making
    the series of increments convergent. With `¬ Overlap`, additivity gives
    μ(x ⊔ y) = μ(x) + μ(y) ≥ μ(x) + δ, guaranteeing linear growth.

    The proof iterates `k` disjoint extensions from `x₀`, each adding at
    least δ to the measure. By the Archimedean property of ℚ, choosing
    k > (M - μ(x₀)) / δ suffices. -/
theorem cum_measure_unbounded {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ]
    {P : α → Prop} (hCum : CUM P)
    {δ : ℚ} (hδ : 0 < δ)
    (hSupply : ∀ (x : α), P x → ∃ (y : α), P y ∧ ¬ Overlap x y ∧ δ ≤ μ y)
    (x₀ : α) (hx₀ : P x₀) (M : ℚ) :
    ∃ (z : α), P z ∧ μ z > M := by
  -- After k disjoint extensions from any P-element, measure grows by ≥ k * δ
  have iterate : ∀ (k : ℕ) (x : α), P x →
      ∃ (z : α), P z ∧ μ z ≥ μ x + ↑k * δ := by
    intro k
    induction k with
    | zero => intro x hx; exact ⟨x, hx, by simp⟩
    | succ k ih =>
      intro x hx
      obtain ⟨z, hPz, hμz⟩ := ih x hx
      obtain ⟨y, hPy, hDisj, hμy⟩ := hSupply z hPz
      refine ⟨z ⊔ y, hCum z y hPz hPy, ?_⟩
      rw [hμ.additive z y hDisj, Nat.cast_succ, add_mul, one_mul]
      linarith
  -- By Archimedean ℚ, find n with n * δ > M - μ(x₀)
  obtain ⟨n, hn⟩ := exists_nat_gt ((M - μ x₀) / δ)
  obtain ⟨z, hPz, hμz⟩ := iterate n x₀ hx₀
  exact ⟨z, hPz, by rw [div_lt_iff₀ hδ] at hn; linarith⟩

-- ════════════════════════════════════════════════════
-- § 14. Generic Pullback Patterns
-- ════════════════════════════════════════════════════

/-- The three dimension chains all instantiate the same pattern:
    IsSumHom + Injective → MereoDim → QUA pullback.
    This theorem states the pattern for any sum homomorphism. -/
theorem sumHom_qua_pullback_pattern {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} [hf : IsSumHom f] (hinj : Function.Injective f)
    {P : β → Prop} (hP : QUA P) :
    QUA (P ∘ f) := by
  haveI := MereoDim.ofInjSumHom hinj
  exact qua_pullback_mereoDim hP

/-- CUM always pulls back through any sum homomorphism (no injectivity needed).
    All three dimension chains preserve atelicity/cumulativity. -/
theorem sumHom_cum_pullback_pattern {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} [hf : IsSumHom f]
    {P : β → Prop} (hP : CUM P) :
    CUM (P ∘ f) :=
  cum_pullback hf hP

-- ════════════════════════════════════════════════════
-- § 15. Named Licensing Theorems (Krifka)
-- ════════════════════════════════════════════════════

/-- Krifka: QUA → closed → licensed. -/
theorem krifka_qua_licensed :
    quaBoundedness.isLicensed = true := rfl

/-- Krifka: CUM → open → blocked. -/
theorem krifka_cum_blocked :
    cumBoundedness.isLicensed = false := rfl

end Mereology
