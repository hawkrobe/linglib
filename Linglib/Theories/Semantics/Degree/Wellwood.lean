import Linglib.Theories.Semantics.Events.ThematicRoles
import Linglib.Theories.Semantics.Lexical.Measurement
import Linglib.Theories.Semantics.Degree.Comparative

/-!
# Compositional Comparative Derivation (Wellwood 2015, §2–3)

@cite{wellwood-2015}

Wellwood (2015) argues that comparatives across nominal, verbal, and
adjectival domains share a uniform DegP pipeline yielding truth conditions
of the form:

    ∃ea. role(a, ea) ∧ P(ea) ∧ ∀eb. role(b, eb) → P(eb) →
         μ(extract(eb)) < μ(extract(ea))

The three domains differ only in the thematic relation (`role`), the
extraction function (`extract`), and what is measured:

| Domain     | role   | extract  | Measured | Example                   |
|------------|--------|----------|----------|---------------------------|
| Nominal    | Agent  | themeOf  | Entity   | "more coffee than"        |
| Verbal     | Agent  | id       | Event    | "ran more than"           |
| Adjectival | Holder | id       | State    | "hotter than"             |

Under unique-max assumptions (each individual has exactly one relevant
eventuality), this reduces to direct comparison: `μ(extract(ea)) > μ(extract(eb))`,
bridging to `comparativeSem` (Rett/Schwarzschild) and `statesComparativeSem` (CSW).

The `DimensionallyRestricted` predicate from `Measurement.lean` explains WHY
dimension type tracks measured domain (§3.4):
- State domains (linear orders) → dimensionally restricted → unique dimension
- Entity/event domains (partial orders) → not restricted → multiple dimensions

## References

- Wellwood, A. (2015). On the semantics of comparison across categories.
  Linguistics and Philosophy 38(1): 67-101.
- Schwarzschild, R. (2008). The semantics of comparatives.
- Cariani, F., Santorio, P. & Wellwood, A. (2024). Confidence reports.
-/

namespace Semantics.Degree.Wellwood

open Semantics.Events
open Semantics.Events.ThematicRoles
open Semantics.Lexical.Measurement (DimensionallyRestricted
  linearOrder_dimensionallyRestricted)

-- ════════════════════════════════════════════════════
-- § 1. Comparative Domain
-- ════════════════════════════════════════════════════

/-- The three comparative domains of Wellwood (2015).
    Each domain determines the thematic relation (role), extraction
    function, and measured ontological sort. -/
inductive ComparativeDomain where
  | nominal    -- "more coffee than" — measures thematic object
  | verbal     -- "ran more than" — measures event directly
  | adjectival -- "hotter than" — measures state directly
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Universal Comparative Truth Condition
-- ════════════════════════════════════════════════════

/-- Universal comparative truth condition (Wellwood 2015, eq. 35/43/59).

    "a V-s more than b does" is true iff there exists an eventuality ea
    with `role(a, ea)` and `P(ea)` such that for ALL eventualities eb
    with `role(b, eb)` and `P(eb)`, `μ(extract(eb)) < μ(extract(ea))`.

    Parameters:
    - `role`: thematic relation linking individual to eventuality
      (Agent for nominal/verbal, Holder for adjectival)
    - `P`: event/state predicate (the VP or GA denotation)
    - `extract`: what to measure from the eventuality
      (themeOf for nominal, id for verbal/adjectival)
    - `μ`: measure function on the extracted domain -/
def comparativeTruth {Entity Time Measured : Type*} [LE Time]
    (role : Entity → Ev Time → Prop)
    (P : EvPred Time)
    (extract : Ev Time → Measured)
    (μ : Measured → ℚ)
    (a b : Entity) : Prop :=
  ∃ ea : Ev Time, role a ea ∧ P ea ∧
    ∀ eb : Ev Time, role b eb → P eb → μ (extract eb) < μ (extract ea)

-- ════════════════════════════════════════════════════
-- § 3. Three Domain Instantiations
-- ════════════════════════════════════════════════════

/-- Nominal comparative (Wellwood eq. 35):
    "Al bought more coffee than Bill did." -/
def nominalComparative {Entity Time : Type*} [LE Time]
    (frame : ThematicFrame Entity Time)
    (P : EvPred Time) (themeOf : Ev Time → Entity)
    (μ : Entity → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.agent P themeOf μ a b

/-- Verbal comparative (Wellwood eq. 43):
    "Al ran more than Bill did." -/
def verbalComparative {Entity Time : Type*} [LE Time]
    (frame : ThematicFrame Entity Time)
    (P : EvPred Time) (μ : Ev Time → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.agent P id μ a b

/-- Adjectival comparative (Wellwood eq. 59):
    "This coffee is hotter than that coffee." -/
def adjectivalComparative {Entity Time : Type*} [LE Time]
    (frame : ThematicFrame Entity Time)
    (P : EvPred Time) (μ : Ev Time → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.holder P id μ a b

-- ════════════════════════════════════════════════════
-- § 4. Maximality Reduction
-- ════════════════════════════════════════════════════

/-- Maximality reduction (Wellwood 2015, passim).

    Under unique-event assumptions — each individual has exactly one
    eventuality satisfying P with the appropriate role — the full
    truth condition reduces to direct comparison of measured values. -/
theorem comparativeTruth_max {Entity Time Measured : Type*} [LE Time]
    {role : Entity → Ev Time → Prop}
    {P : EvPred Time}
    {extract : Ev Time → Measured}
    {μ : Measured → ℚ}
    {a b : Entity}
    {ea eb : Ev Time}
    (ha : role a ea ∧ P ea)
    (ha_unique : ∀ e, role a e → P e → e = ea)
    (hb : role b eb ∧ P eb)
    (hb_unique : ∀ e, role b e → P e → e = eb) :
    comparativeTruth role P extract μ a b ↔
      μ (extract eb) < μ (extract ea) := by
  constructor
  · rintro ⟨ea', hra, hpa, hall⟩
    have heq := ha_unique ea' hra hpa
    rw [heq] at hall
    exact hall eb hb.1 hb.2
  · intro hlt
    exact ⟨ea, ha.1, ha.2, fun e hr hp => by rw [hb_unique e hr hp]; exact hlt⟩

-- ════════════════════════════════════════════════════
-- § 5. Bridges to Existing Infrastructure
-- ════════════════════════════════════════════════════

/-- Adjectival comparative under maximality reduces to direct state
    comparison: `μ(sb) < μ(sa)`. -/
theorem adjectival_max_reduces {Entity Time : Type*} [LE Time]
    {frame : ThematicFrame Entity Time}
    {P : EvPred Time} {μ : Ev Time → ℚ}
    {a b : Entity} {sa sb : Ev Time}
    (ha : frame.holder a sa ∧ P sa)
    (ha_unique : ∀ s, frame.holder a s → P s → s = sa)
    (hb : frame.holder b sb ∧ P sb)
    (hb_unique : ∀ s, frame.holder b s → P s → s = sb) :
    adjectivalComparative frame P μ a b ↔ μ sb < μ sa :=
  comparativeTruth_max ha ha_unique hb hb_unique

/-- CSW's `statesComparativeSem` is definitionally the direct comparison
    `μ sb < μ sa`. -/
theorem statesComparativeSem_is_lt {S D : Type*} [Preorder S] [Preorder D]
    (μ : S → D) (sa sb : S) :
    Semantics.Lexical.Adjective.StatesBased.statesComparativeSem μ sa sb ↔
      μ sb < μ sa :=
  Iff.rfl

/-- All comparative domains under maximality = comparativeSem (Rett/Schwarzschild).

    The Wellwood pipeline under maximality reduces to the same direct
    comparison as `comparativeSem` from Degree.Comparative on measured values. -/
theorem max_eq_comparativeSem {Entity Time Measured : Type*} [LE Time]
    {role : Entity → Ev Time → Prop}
    {P : EvPred Time}
    {extract : Ev Time → Measured}
    {μ : Measured → ℚ}
    {a b : Entity} {ea eb : Ev Time}
    (ha : role a ea ∧ P ea)
    (ha_unique : ∀ e, role a e → P e → e = ea)
    (hb : role b eb ∧ P eb)
    (hb_unique : ∀ e, role b e → P e → e = eb) :
    comparativeTruth role P extract μ a b ↔
      Semantics.Degree.Comparative.comparativeSem
        (μ ∘ extract) ea eb .positive :=
  comparativeTruth_max ha ha_unique hb hb_unique

-- ════════════════════════════════════════════════════
-- § 6. DimensionalRestriction Connection
-- ════════════════════════════════════════════════════

/-- State domains are dimensionally restricted when linearly ordered. -/
theorem state_domain_restricted {S : Type*} [LinearOrder S] :
    DimensionallyRestricted S :=
  linearOrder_dimensionallyRestricted

/-- If two admissible measures disagree on some pair, the domain is NOT
    dimensionally restricted. -/
theorem not_restricted_of_disagreement {α : Type*} [Preorder α]
    {μ₁ μ₂ : α → ℚ} (hμ₁ : StrictMono μ₁) (hμ₂ : StrictMono μ₂)
    {a b : α} (h₁ : μ₁ a < μ₁ b) (h₂ : ¬ μ₂ a < μ₂ b) :
    ¬ DimensionallyRestricted α := by
  intro hDR
  exact h₂ ((hDR μ₁ μ₂ hμ₁ hμ₂ a b).mp h₁)

end Semantics.Degree.Wellwood
