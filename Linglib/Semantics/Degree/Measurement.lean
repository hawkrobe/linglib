import Linglib.Semantics.Mereology
import Linglib.Features.Aktionsart
import Linglib.Semantics.Degree.Gradability.StatesBased
import Linglib.Semantics.Kinds.MeaningPreservation

/-!
# Cross-Categorial Measurement Semantics

[wellwood-2015] [kennedy-2007]

[wellwood-2015] argues that all comparative sentences contain a covert `much`
morpheme whose semantics is a measure function μ assigned by a variable
assignment A:

    ⟦much_μ⟧^A = A(μ)

The measure function must be **monotonic**: for all α, β in a
part-whole ordered domain, if α ≺^Part β then μ(α) ≺^Deg μ(β). This is
the monotonicity condition of [schwarzschild-2002] and [schwarzschild-2006],
and corresponds exactly to `StrictMono` / `MereoDim` / CSW's
`admissibleMeasure` in linglib.

The key insight is a three-way cross-categorial parallel:

- **Nominal**: mass nouns (CUM) → measurable by `much`; count nouns (QUA) → `many`
- **Verbal**: atelic VPs (CUM) → measurable by `much`; telic VPs (QUA) → `many`
- **Adjectival**: gradable adjectives predicate of states with mereological
  structure → measurable by `much`; non-gradable adjectives predicate of
  atomic, unordered states → not measurable

Dimensionality differences (VOLUME vs TEMPERATURE vs DURATION) follow from
*what is measured* (entities, events, states), not from *which expression*
introduces the measurement (§3.4). This is formalized as `DimensionallyRestricted`:
a domain is dimensionally restricted iff any two admissible measure functions
agree on the comparative ordering — which holds exactly for linear orders
(GA state domains) and fails for partial orders with incomparable elements
(entity/event domains where weight and volume can disagree).

## Key Identifications

- [wellwood-2015]'s monotonicity condition = `StrictMono` = `MereoDim` = CSW's `admissibleMeasure`
- [wellwood-2015]'s measurability condition = `CUM` (mereological structure)
- [wellwood-2015]'s counting condition = `QUA` (quantized reference)
- [wellwood-2015]'s dimensional restriction = `LinearOrder` on the measured domain
- [wellwood-2015]'s comparative = CSW's `statesComparativeSem` = `μ b < μ a`

## Interpretive Note

[wellwood-2015] does not explicitly label GA state domains as "cumulative" in
Krifka's technical sense (closure under join). She argues they "form
mereologies" — ordered domains with proper parts. We classify
them as `.cumulative` because the structural consequence is the same:
mereological structure enables monotonic measurement by `much`.

Likewise, identifying dimensional restriction with a `LinearOrder` on the
measured domain is a reconstruction, not the paper's own statement: the paper
argues dimension availability tracks the measured domain (states vs
entities/events) without stating the totality condition, and describes GA
state domains as mereologies (partial orders). The linear-order reading is
the tightest order-theoretic condition delivering her generalization
(`linearOrder_dimensionallyRestricted` and, conversely,
`prod_not_dimensionallyRestricted`).

-/

namespace Semantics.Measurement

open _root_.Mereology
open Features
open Semantics.Kinds.MeaningPreservation (NumberFeature)

-- ════════════════════════════════════════════════════
-- § 1. Mereological Status
-- ════════════════════════════════════════════════════

/-- Cross-categorial mereological classification (§2–3).

    Predicates across nominal, verbal, and adjectival domains fall into
    two classes based on their mereological properties:

    - `cumulative`: domain has mereological structure with proper parts,
      enabling monotonic measurement by `much`. Includes mass nouns
      (CUM), atelic VPs (CUM), and gradable adjectives (states form
      mereologies).
    - `quantized`: domain lacks non-trivial part-whole structure for
      measurement. Count nouns (QUA), telic VPs (QUA), and non-gradable
      adjectives (atomic, unordered states). -/
inductive MereologicalStatus where
  | cumulative
  | quantized
  deriving DecidableEq, Repr

/-- Map mereological status to Kennedy scale boundedness.

    CUM → no inherent endpoint → open scale (→ blocked degree modifiers)
    QUA → inherent endpoint → closed scale (→ licensed degree modifiers)

    This connects cross-categorial classification to Kennedy's
    scale structure: CUM predicates admit ever-larger sums
    (`Mereology.cum_measure_unbounded`), so their scale has no inherent
    endpoint; QUA predicates measure to a definite value
    ([kennedy-2007], [rouillard-2026]). -/
def MereologicalStatus.toBoundedness : MereologicalStatus → Core.Order.Boundedness
  | .cumulative => .open_
  | .quantized  => .closed

/-- Direct conversion from [wellwood-2015]'s `MereologicalStatus` to
    the cross-framework `Core.Order.MereoTag` substrate. Wellwood's
    framework uses "monotonic" / "structure-preserving" terminology
    (see module docstring "Interpretive Note"); we lift to [krifka-1989]'s
    `cum`/`qua` labels for cross-framework dialogue. -/
def MereologicalStatus.toMereoTag : MereologicalStatus → Core.Order.MereoTag
  | .cumulative => .cum
  | .quantized  => .qua

/-- The `MereologicalStatus → Boundedness` mapping agrees with the
    `MereoTag → Boundedness` mapping via `toMereoTag`. Closes the
    silent divergence between [wellwood-2015]'s labels and the
    cross-framework `MereoTag` substrate noted by the Scale.lean §1b
    "shared abstraction underlying all four licensing frameworks" claim. -/
theorem toBoundedness_matches_mereoTag :
    MereologicalStatus.cumulative.toBoundedness = Core.Order.MereoTag.cum.toBoundedness ∧
    MereologicalStatus.quantized.toBoundedness = Core.Order.MereoTag.qua.toBoundedness :=
  ⟨rfl, rfl⟩

/-- `MereologicalStatus` joins `Boundedness` and `MereoTag` as a
    `LicensingPipeline` instance, putting [wellwood-2015] in literal
    dialogue with [krifka-1989]/[kennedy-2007]/[rouillard-2026]
    via `Core.Order.LicensingPipeline.universal` (which now derives
    cross-framework licensing agreement automatically when the underlying
    boundedness coincides). -/
instance : Core.Order.LicensingPipeline MereologicalStatus where
  toBoundedness := MereologicalStatus.toBoundedness

-- ════════════════════════════════════════════════════
-- § 2. `much` as Structure-Preserving Map
-- ════════════════════════════════════════════════════

/-- Every `MereoDim` witness yields the unbundled `admissibleMeasure`
    Prop. `MereoDim` (`Semantics/Mereology.lean`) bundles `StrictMono` in a
    typeclass with `[PartialOrder]` carriers; `admissibleMeasure`
    (Semantics/Gradability/StatesBased.lean) is the equivalent
    Prop with the more permissive `[Preorder]` carriers. The single
    multi-tradition naming convention lives on `admissibleMeasure`'s
    docstring. -/
theorem admissibleMeasure_of_mereoDim
    {A D : Type*} [PartialOrder A] [PartialOrder D]
    {μ : A → D} (h : MereoDim μ) :
    Semantics.Gradability.StatesBased.admissibleMeasure (S := A) μ :=
  h.toStrictMono

-- ════════════════════════════════════════════════════
-- § 3. Cross-Categorial Bridges
-- ════════════════════════════════════════════════════

/-- Telicity determines mereological status:
    atelic VPs have CUM domains (activities, states), telic VPs have QUA
    domains (achievements, accomplishments). -/
def telicityToStatus : Telicity → MereologicalStatus
  | .atelic => .cumulative
  | .telic  => .quantized

/-- Number feature determines mereological status:
    mass nouns have CUM domains; count nouns (sg/pl) have QUA domains.

    Note: plural count nouns are CUM at the plurality level
    ("Plural predicates are cumulative"), but their measurement is restricted
    to NUMBER (counting atoms). At the lexical level, count nouns are QUA. -/
def numberToStatus : NumberFeature → MereologicalStatus
  | .mass    => .cumulative
  | .sg      => .quantized
  | .pl      => .quantized
  | .neutral => .quantized  -- Number-neutral nouns (Shan) have identifiable
                             -- atomic parts despite lacking obligatory number
                             -- marking ([moroney-2021] §2.2).

/-- Gradable adjectives predicate of states that "form mereologies", enabling monotonic measurement by `much`.

    Interpretive note: does not explicitly use the label CUM for
    GA state domains. She argues they have mereological structure (ordered
    domains with proper parts). We classify them as `.cumulative` because
    the structural consequence is identical: mereological structure enables
    monotonic measurement. -/
def gradableToStatus : MereologicalStatus := .cumulative

/-- Non-gradable adjectives (wooden, triangular) predicate of "atomic,
    unordered objects". Their state domains
    lack both mereological structure and comparative ordering, making
    them not measurable by `much`.

    This is stronger than QUA in the strict technical sense: QUA merely
    requires no P-proper-parts on a partial order, while non-GA states
    lack ordering entirely. We classify them as `.quantized` as the
    closest approximation. -/
def nonGradableToStatus : MereologicalStatus := .quantized

/-- Vendler classification determines mereological status via telicity.
    States and activities are atelic → cumulative; achievements and
    accomplishments are telic → quantized. -/
def vendlerToStatus (c : VendlerClass) : MereologicalStatus :=
  telicityToStatus c.telicity

theorem state_is_cumulative : vendlerToStatus .state = .cumulative := rfl
theorem activity_is_cumulative : vendlerToStatus .activity = .cumulative := rfl
theorem achievement_is_quantized : vendlerToStatus .achievement = .quantized := rfl
theorem accomplishment_is_quantized : vendlerToStatus .accomplishment = .quantized := rfl

-- ════════════════════════════════════════════════════
-- § 4. Aspectual Shift Bridges
-- ════════════════════════════════════════════════════

/-- Telicization shifts measurement status from cumulative to quantized.

    Adding a goal PP to an atelic VP ("ran" → "ran to the park") changes
    the predicate's mereological status, blocking extensive dimensions
    (DURATION, DISTANCE) and restricting to NUMBER. This connects
    grammar-shifts-measurement claim to the existing
    `AspectualProfile.telicize` operation. -/
theorem telicize_shifts_status (p : AspectualProfile) (h : p.telicity = .atelic) :
    telicityToStatus p.telicity = .cumulative ∧
    telicityToStatus p.telicize.telicity = .quantized :=
  ⟨by rw [h]; rfl, rfl⟩

/-- Atelicization shifts measurement status from quantized to cumulative.

    The progressive on a telic VP ("built the house" → "was building the
    house") restores extensive dimensions. -/
theorem atelicize_shifts_status (p : AspectualProfile) (h : p.telicity = .telic) :
    telicityToStatus p.telicity = .quantized ∧
    telicityToStatus p.atelicize.telicity = .cumulative :=
  ⟨by rw [h]; rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Dimensional Restriction
-- ════════════════════════════════════════════════════

/-- A domain is dimensionally restricted when any two admissible measure
    functions (StrictMono maps to ℚ) agree on the comparative ordering
    of all elements.

    This captures the claim that the state domains GAs measure afford a
    single dimension while entity/event domains allow contextual
    dimension selection:

    - GA state domains: linearly ordered → any two StrictMono μ₁, μ₂
      agree on the comparative → dimensionally restricted
    - Entity/event domains: partially ordered with incomparable elements →
      different ExtMeasures (weight vs volume) can disagree →
      not dimensionally restricted

    The structural content: dimensional restriction holds iff the
    ambient preorder is total (a `LinearOrder`). The forward direction
    is `linearOrder_dimensionallyRestricted`; the converse is witnessed
    by any two incomparable elements with disagreeing measures. -/
def DimensionallyRestricted (α : Type*) [Preorder α] : Prop :=
  ∀ (μ₁ μ₂ : α → ℚ), StrictMono μ₁ → StrictMono μ₂ →
    ∀ (a b : α), μ₁ a < μ₁ b ↔ μ₂ a < μ₂ b

/-- Linear orders are dimensionally restricted: the comparative ordering
    is uniquely determined by the ambient order, regardless of which
    admissible measure function is chosen. -/
theorem linearOrder_dimensionallyRestricted {α : Type*} [LinearOrder α] :
    DimensionallyRestricted α :=
  fun _ _ hμ₁ hμ₂ _ _ => hμ₁.lt_iff_lt.trans hμ₂.lt_iff_lt.symm

/-- If two admissible measures disagree on some pair, the domain is NOT
    dimensionally restricted. -/
theorem not_restricted_of_disagreement {α : Type*} [Preorder α]
    {μ₁ μ₂ : α → ℚ} (hμ₁ : StrictMono μ₁) (hμ₂ : StrictMono μ₂)
    {a b : α} (h₁ : μ₁ a < μ₁ b) (h₂ : ¬ μ₂ a < μ₂ b) :
    ¬ DimensionallyRestricted α :=
  fun hDR => h₂ ((hDR μ₁ μ₂ hμ₁ hμ₂ a b).mp h₁)

/-- The converse witness: a partially ordered domain with incomparable
    elements is not dimensionally restricted. On `ℚ × ℚ` (componentwise
    order — think weight × volume on portions of matter), the two
    admissible measures `2·w + v` and `w + v` order the incomparable
    portions `(0, 1)` and `(1, 0)` differently, so the choice of measure
    function matters — the multi-dimensional signature of entity/event
    domains. -/
theorem prod_not_dimensionallyRestricted :
    ¬ DimensionallyRestricted (ℚ × ℚ) := by
  have hmono : ∀ c : ℚ, 0 < c → StrictMono (fun p : ℚ × ℚ => c * p.1 + p.2) := by
    intro c hc p q hpq
    rcases Prod.lt_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := mul_lt_mul_of_pos_left h1 hc
      dsimp only
      nlinarith
    · have := mul_le_mul_of_nonneg_left h1 hc.le
      dsimp only
      nlinarith
  exact not_restricted_of_disagreement (μ₁ := fun p => 2 * p.1 + p.2)
    (μ₂ := fun p => 1 * p.1 + p.2) (hmono 2 (by norm_num)) (hmono 1 (by norm_num))
    (a := (0, 1)) (b := (1, 0)) (by norm_num) (by norm_num)

/-- A `StatesBasedEntry` over a linearly ordered state domain is
    dimensionally restricted: the comparative meaning is independent
    of which admissible measure function is chosen.

    This explains CSW's observation (72): scale-mates like `confident`
    and `certain` share a background ordering, and any admissible
    measure on that ordering gives the same comparative truth conditions.
    The comparative is determined by the ordering alone, not by which
    adjective introduces it. -/
theorem statesBasedEntry_restricted
    {S : Type*} [LinearOrder S]
    (_entry : Semantics.Gradability.StatesBased.StatesBasedEntry S) :
    DimensionallyRestricted S :=
  linearOrder_dimensionallyRestricted

end Semantics.Measurement
