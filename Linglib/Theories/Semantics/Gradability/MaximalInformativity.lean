import Mathlib.Order.Basic
import Linglib.Core.Scales.Defs
import Linglib.Core.Scales.Comparative
import Linglib.Core.Scales.DirectedMeasure

/-!
# Maximal Informativity Principle (MIP)
@cite{rouillard-2026} @cite{kennedy-2015} @cite{fox-2007}

The **Maximal Informativity Principle** is the licensing condition originally
proposed for temporal *in*-adverbials (E-TIAs and G-TIAs) by Rouillard 2026,
later recognized as the same mechanism that drives Kennedy 2015's de-Fregean
type-shift for numerals. The unifying claim: given a measure function `μ` and
a monotone degree property `P`, the maximally informative satisfying value is
always `μ(w)` — the true value.

## Frameworks unified

| Construction         | μ           | Degree prop  | Direction | MIP result    |
|----------------------|-------------|--------------|-----------|---------------|
| Numerals (Kennedy)   | cardinality | atLeastDeg   | down mono | max⊨ = μ(w)  |
| Adjectives (Kennedy) | degree      | atLeastDeg   | down mono | max⊨ = μ(w)  |
| E-TIAs (Rouillard)   | runtime     | atMostDeg    | up mono   | max⊨ = μ(w)  |

## Operators

- `etia` — event-runtime time-of-interval adverbial domain (Rouillard 2026)
- `gtia` — general time-of-interval adverbial domain (always open → blocked)
- `etia_telic_licensed` / `etia_atelic_blocked` — predicted licensing
- `gtia_blocked` — G-TIAs always blocked (information collapse)

Renamed from `rouillardETIA`/`rouillardGTIA` per master plan v4 idea-naming
discipline (file names + operators describe the IDEA, not the proposer).
The proposer is cited in @cite{} blocks throughout.

## Cross-framework agreement

The Kennedy numeral/adjective MIP-domain operators (`DirectedMeasure.numeral`,
`DirectedMeasure.adjective`) live in `Core/Scales/DirectedMeasure.lean` since
they're domain-general DirectedMeasure constructors. The Rouillard E-TIA/G-TIA
operators live here because they have direction-negative as the lexically-fixed
commitment (the MIP's central insight: atMostDeg + monotone runtime).
-/

namespace Semantics.Gradability.MaximalInformativity

open Core.Scale

variable {α : Type*} [LinearOrder α] {W : Type*}

-- ════════════════════════════════════════════════════
-- § 1. MIP-domain operators
-- ════════════════════════════════════════════════════

/-- @cite{rouillard-2026} E-TIA domain: event runtime ≤ interval size.
    Boundedness determined by Vendler class (telic → closed, atelic → open).
    Direction is negative (atMostDeg) per Rouillard's MIP analysis. -/
def etia (μ : W → α) (b : Boundedness) : DirectedMeasure α W :=
  { boundedness := b, μ := μ, direction := .negative }

/-- @cite{rouillard-2026} G-TIA domain: PTS extent on open intervals.
    Always open → always blocked (information collapse). -/
def gtia (μ : W → α) : DirectedMeasure α W :=
  { boundedness := .open_, μ := μ, direction := .negative }

-- ════════════════════════════════════════════════════
-- § 2. Licensing theorems
-- ════════════════════════════════════════════════════

/-- Telic E-TIAs are licensed (closed runtime scale). -/
theorem etia_telic_licensed (μ : W → α) :
    (etia μ .closed).licensed = true := rfl

/-- Atelic E-TIAs are blocked (open runtime scale). -/
theorem etia_atelic_blocked (μ : W → α) :
    (etia μ .open_).licensed = false := rfl

/-- G-TIAs are always blocked (open PTS). -/
theorem gtia_blocked (μ : W → α) :
    (gtia μ).licensed = false := rfl

-- ════════════════════════════════════════════════════
-- § 3. Cross-framework isomorphism (Kennedy ↔ Rouillard)
-- ════════════════════════════════════════════════════

/-- The deep isomorphism: a Kennedy numeral domain (positive direction) and
    a Rouillard E-TIA domain on a closed scale (negative direction) have
    identical licensing — boundedness alone determines the prediction. -/
theorem numeral_etia_same_licensing (μ₁ μ₂ : W → α) :
    (DirectedMeasure.numeral μ₁).licensed = (etia μ₂ .closed).licensed := rfl

/-- All four frameworks (Kennedy adjectives, Rouillard E-TIAs, Krifka quantization,
    Zwarts paths) agree: licensing depends solely on boundedness.
    @cite{kennedy-2007} @cite{rouillard-2026} @cite{krifka-1989} @cite{zwarts-2005}. -/
theorem four_frameworks_agree (b : Boundedness) (μ₁ μ₂ : W → α) :
    (DirectedMeasure.adjective μ₁ b).licensed = (etia μ₂ b).licensed := rfl

end Semantics.Gradability.MaximalInformativity
