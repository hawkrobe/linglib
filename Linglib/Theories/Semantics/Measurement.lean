import Linglib.Core.Mereology
import Linglib.Core.Scales.MereoDim
import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect
import Linglib.Theories.Semantics.Gradability.StatesBased
import Linglib.Theories.Semantics.Noun.Kind.Dayal2004

/-!
# Cross-Categorial Measurement Semantics

@cite{wellwood-2015} @cite{kennedy-2007}

@cite{wellwood-2015} argues that all comparative sentences contain a covert `much`
morpheme whose semantics is a measure function μ assigned by a variable
assignment A:

    ⟦much_μ⟧^A = A(μ)

The measure function must be **monotonic**: for all α, β in a
part-whole ordered domain, if α ≺^Part β then μ(α) ≺^Deg μ(β). This is
@cite{schwarzschild-wilkinson-2002}'s monotonicity condition, and corresponds exactly
to `StrictMono` / `MereoDim` / CSW's `admissibleMeasure` in linglib.

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

- @cite{wellwood-2015}'s monotonicity condition = `StrictMono` = `MereoDim` = CSW's `admissibleMeasure`
- @cite{wellwood-2015}'s measurability condition = `CUM` (mereological structure)
- @cite{wellwood-2015}'s counting condition = `QUA` (quantized reference)
- @cite{wellwood-2015}'s dimensional restriction = `LinearOrder` on the measured domain
- @cite{wellwood-2015}'s comparative = CSW's `statesComparativeSem` = `μ b < μ a`

## Interpretive Note

@cite{wellwood-2015} does not explicitly label GA state domains as "cumulative" in
Krifka's technical sense (closure under join). She argues they "form
mereologies" — ordered domains with proper parts. We classify
them as `.cumulative` because the structural consequence is the same:
mereological structure enables monotonic measurement by `much`.

-/

namespace Semantics.Measurement

open Mereology
open Core.Verbs
open Semantics.Noun.Kind.Dayal2004 (NumberFeature)

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
    scale structure, via the existing `cumBoundedness`/`quaBoundedness`
    annotations in `Core.MereoDim`. -/
def MereologicalStatus.toBoundedness : MereologicalStatus → Core.Scale.Boundedness
  | .cumulative => .open_
  | .quantized  => .closed

/-- The `toBoundedness` mapping agrees with the existing mereological
    scale annotations in `Core.MereoDim`. -/
theorem toBoundedness_coherent :
    MereologicalStatus.cumulative.toBoundedness = cumBoundedness ∧
    MereologicalStatus.quantized.toBoundedness = quaBoundedness := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. `much` as Structure-Preserving Map
-- ════════════════════════════════════════════════════

/-- Every `MereoDim` witness yields the unbundled `admissibleMeasure`
    Prop. `MereoDim` (Core/Scales/MereoDim.lean) bundles `StrictMono` in a
    typeclass with `[PartialOrder]` carriers; `admissibleMeasure`
    (Theories/Semantics/Gradability/StatesBased.lean) is the equivalent
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
                             -- marking (@cite{moroney-2021} §2.2).

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
    telicityToStatus p.telicize.telicity = .quantized := by
  exact ⟨by simp only [h, telicityToStatus],
         by simp only [AspectualProfile.telicize, telicityToStatus]⟩

/-- Atelicization shifts measurement status from quantized to cumulative.

    The progressive on a telic VP ("built the house" → "was building the
    house") restores extensive dimensions. -/
theorem atelicize_shifts_status (p : AspectualProfile) (h : p.telicity = .telic) :
    telicityToStatus p.telicity = .quantized ∧
    telicityToStatus p.atelicize.telicity = .cumulative := by
  exact ⟨by simp only [h, telicityToStatus],
         by simp only [AspectualProfile.atelicize, telicityToStatus]⟩

-- ════════════════════════════════════════════════════
-- § 5. Dimensional Restriction
-- ════════════════════════════════════════════════════

/-- A domain is dimensionally restricted when any two admissible measure
    functions (StrictMono maps to ℚ) agree on the comparative ordering
    of all elements.

    This captures claim that GAs lexically fix a single
    dimension while nouns/verbs allow contextual dimension selection:

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
    admissible measure function is chosen.

    Proof: on a linear order, `StrictMono` reflects the strict order
    (by trichotomy + irreflexivity), so μ₁ a < μ₁ b ↔ a < b ↔ μ₂ a < μ₂ b. -/
theorem linearOrder_dimensionallyRestricted {α : Type*} [LinearOrder α] :
    DimensionallyRestricted α := by
  intro μ₁ μ₂ hμ₁ hμ₂ a b
  constructor
  · intro h
    rcases lt_trichotomy a b with hab | hab | hab
    · exact hμ₂ hab
    · subst hab; exact absurd h (lt_irrefl _)
    · exact absurd (lt_trans h (hμ₁ hab)) (lt_irrefl _)
  · intro h
    rcases lt_trichotomy a b with hab | hab | hab
    · exact hμ₁ hab
    · subst hab; exact absurd h (lt_irrefl _)
    · exact absurd (lt_trans h (hμ₂ hab)) (lt_irrefl _)

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
