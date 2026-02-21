import Linglib.Core.Mereology
import Linglib.Core.MereoDim
import Linglib.Theories.Semantics.Lexical.Verb.Aspect
import Linglib.Theories.Semantics.Lexical.Adjective.StatesBased
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Dayal2004

/-!
# Cross-Categorial Measurement Semantics

@cite{wellwood-2015}

Wellwood (2015) argues that all comparative sentences contain a covert `much`
morpheme whose semantics is a measure function μ assigned by a variable
assignment A (eq. 28):

    ⟦much_μ⟧^A = A(μ)

The measure function must be **monotonic** (eq. 26): for all α, β in a
part-whole ordered domain, if α ≺^Part β then μ(α) ≺^Deg μ(β). This is
Schwarzschild's (2002, 2006) monotonicity condition, and corresponds exactly
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

- Wellwood's monotonicity (eq. 26) = `StrictMono` = `MereoDim` = CSW's `admissibleMeasure`
- Wellwood's measurability condition = `CUM` (mereological structure)
- Wellwood's counting condition = `QUA` (quantized reference)
- Wellwood's dimensional restriction = `LinearOrder` on the measured domain
- Wellwood's comparative = CSW's `statesComparativeSem` = `μ b < μ a`

## Interpretive Note

Wellwood does not explicitly label GA state domains as "cumulative" in
Krifka's technical sense (closure under join). She argues they "form
mereologies" (p. 81) — ordered domains with proper parts. We classify
them as `.cumulative` because the structural consequence is the same:
mereological structure enables monotonic measurement by `much`.

## References

- Wellwood, A. (2015). On the semantics of comparison across categories.
  Linguistics and Philosophy 38(1): 67-101.
- Schwarzschild, R. (2006). The role of dimensions in the syntax of
  noun phrases. Syntax 9(1): 67-110.
-/

namespace Semantics.Lexical.Measurement

open Mereology
open Semantics.Lexical.Verb.Aspect (Telicity VendlerClass AspectualProfile)
open Semantics.Lexical.Noun.Kind.Dayal2004 (NumberFeature)

-- ════════════════════════════════════════════════════
-- § 1. Mereological Status
-- ════════════════════════════════════════════════════

/-- Cross-categorial mereological classification (Wellwood 2015, §2–3).

    Predicates across nominal, verbal, and adjectival domains fall into
    two classes based on their mereological properties:

    - `cumulative`: domain has mereological structure with proper parts,
      enabling monotonic measurement by `much`. Includes mass nouns
      (CUM), atelic VPs (CUM), and gradable adjectives (states form
      mereologies — §3.2, p. 81).
    - `quantized`: domain lacks non-trivial part-whole structure for
      measurement. Count nouns (QUA), telic VPs (QUA), and non-gradable
      adjectives (atomic, unordered states — §3.1, p. 80). -/
inductive MereologicalStatus where
  | cumulative
  | quantized
  deriving DecidableEq, BEq, Repr

/-- Map mereological status to Kennedy scale boundedness (Kennedy 2007).

    CUM → no inherent endpoint → open scale (→ blocked degree modifiers)
    QUA → inherent endpoint → closed scale (→ licensed degree modifiers)

    This connects Wellwood's cross-categorial classification to Kennedy's
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

/-- Wellwood's `much` (eq. 28): ⟦much_μ⟧^A = A(μ), where μ is a
    monotonic measure function. The monotonicity condition (eq. 26)
    requires strict order preservation:

      for all α, β ∈ D_≤Part, if α ≺^Part β then μ(α) ≺^Deg μ(β)

    This is `StrictMono`, equivalently `MereoDim.toStrictMono` or
    CSW's `admissibleMeasure`. The comparative across all categories
    is the existing `statesComparativeSem`: μ(b) < μ(a). -/
abbrev MuchSem {A D : Type*} [Preorder A] [Preorder D] (μ : A → D) : Prop :=
  StrictMono μ

/-- `MuchSem` is definitionally equal to CSW's admissible measure
    constraint (CSW eq. 21). Both require strict order preservation.
    This makes the Wellwood–CSW identification explicit: changing
    either definition breaks this theorem. -/
theorem muchSem_eq_admissibleMeasure
    {S D : Type*} [Preorder S] [Preorder D] (μ : S → D) :
    MuchSem μ ↔ Semantics.Lexical.Adjective.StatesBased.admissibleMeasure μ :=
  Iff.rfl

/-- Every `MereoDim` witness provides a `MuchSem` proof.
    `MereoDim` bundles `StrictMono` in a typeclass; `MuchSem` is the
    unbundled predicate. -/
theorem muchSem_of_mereoDim
    {A D : Type*} [PartialOrder A] [PartialOrder D]
    {μ : A → D} (h : MereoDim μ) : MuchSem μ :=
  h.toStrictMono

-- ════════════════════════════════════════════════════
-- § 3. Cross-Categorial Bridges
-- ════════════════════════════════════════════════════

/-- Telicity determines mereological status (Wellwood 2015, §2.2, p. 74–76):
    atelic VPs have CUM domains (activities, states), telic VPs have QUA
    domains (achievements, accomplishments). -/
def telicityToStatus : Telicity → MereologicalStatus
  | .atelic => .cumulative
  | .telic  => .quantized

/-- Number feature determines mereological status (Wellwood 2015, §2.1, p. 73–74):
    mass nouns have CUM domains; count nouns (sg/pl) have QUA domains.

    Note: plural count nouns are CUM at the plurality level (p. 92:
    "Plural predicates are cumulative"), but their measurement is restricted
    to NUMBER (counting atoms). At the lexical level, count nouns are QUA. -/
def numberToStatus : NumberFeature → MereologicalStatus
  | .mass => .cumulative
  | .sg   => .quantized
  | .pl   => .quantized

/-- Gradable adjectives predicate of states that "form mereologies"
    (Wellwood 2015, §3.2, p. 81), enabling monotonic measurement by `much`.

    Interpretive note: Wellwood does not explicitly use the label CUM for
    GA state domains. She argues they have mereological structure (ordered
    domains with proper parts). We classify them as `.cumulative` because
    the structural consequence is identical: mereological structure enables
    monotonic measurement. -/
def gradableToStatus : MereologicalStatus := .cumulative

/-- Non-gradable adjectives (wooden, triangular) predicate of "atomic,
    unordered objects" (Wellwood 2015, §3.1, p. 80). Their state domains
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

/-- Telicization shifts measurement status from cumulative to quantized
    (Wellwood 2015, §5, p. 91–93).

    Adding a goal PP to an atelic VP ("ran" → "ran to the park") changes
    the predicate's mereological status, blocking extensive dimensions
    (DURATION, DISTANCE) and restricting to NUMBER. This connects
    Wellwood's grammar-shifts-measurement claim to the existing
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
    of all elements (Wellwood 2015, §3.4, p. 85–86).

    This captures Wellwood's claim that GAs lexically fix a single
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
    (_entry : Semantics.Lexical.Adjective.StatesBased.StatesBasedEntry S) :
    DimensionallyRestricted S :=
  linearOrder_dimensionallyRestricted

end Semantics.Lexical.Measurement
