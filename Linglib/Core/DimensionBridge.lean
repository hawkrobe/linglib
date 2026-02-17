import Linglib.Core.MereoDim
import Linglib.Core.MeasurementScale
import Linglib.Core.Time
import Linglib.Core.Path
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Field.Rat

/-!
# Cross-Dimension Bridge (Core)

Theory-neutral infrastructure connecting the mereological dimension pipeline
(`MereoDim → Boundedness → MIPDomain → licensing`) across its component files.

The core contribution of this file is three levels of cross-domain unification:

1. **Structural unification** (`DimensionChain`): A first-class object bundling
   a two-leg pipeline Source →f Inter →μ Measure with `MereoDim` proofs on both
   legs. Generic QUA/CUM transfer theorems. All three dimension chains (τ, σ, θ)
   instantiate it.

2. **Classification unification** (`LicensingPipeline`): A typeclass mapping any
   classification type to `Boundedness`, instantiated by all six entry types
   (`Boundedness`, `Telicity`, `VendlerClass`, `PathShape`, `BoundaryType`,
   `MereoTag`). A parameterized `universal` theorem proves that any two inputs
   mapping to the same `Boundedness` yield the same licensing prediction.

3. **Deep mereological bridge** (`cum_exceeds_source`, `cum_measure_unbounded`):
   Non-trivial theorems connecting CUM to measurement growth, bridging
   `Core/Mereology` ↔ `Core/MeasurementScale` at the *proof* level.
   `cum_measure_unbounded` requires a *disjoint* fresh supply (¬ Overlap)
   with a minimum measure bound δ, since mere incomparability (¬ y ≤ x)
   allows convergent increment series.

## Three Dimension Chains

```
Temporal:  Events →τ Intervals →dur ℚ     (τ is IsSumHom; dur is ExtMeasure)
Spatial:   Events →σ Paths     →dist ℚ    (σ is IsSumHom; dist hypothetical)
Object:    Events →θ Entities  →μ   ℚ     (θ is SINC⊃IsSumHom; μ is ExtMeasure)
```

Theory-specific commutativity squares (VendlerClass, PathShape → Telicity) and
concrete chain instantiations live in `Theories/Semantics/Events/DimensionBridge.lean`.

## References

- Kennedy, C. (2007). Vagueness and grammar.
- Rouillard, V. (2026). Maximal informativity and temporal in-adverbials.
- Krifka, M. (1989). Nominal reference, temporal constitution.
- Krifka, M. (1998). The origins of telicity.
- Zwarts, J. (2005). Prepositional aspect and the algebra of paths.
-/

namespace Core.DimensionBridge

open Core.Scale
open Core.Path
open Mereology

-- ════════════════════════════════════════════════════
-- § 1. BoundaryType → Boundedness Bridge (Interval Generalization)
-- ════════════════════════════════════════════════════

/-- Interval boundary type maps to scale boundedness.
    Rouillard (2026): closed runtimes correspond to closed scales (licensed);
    open PTSs correspond to open scales (blocked/information collapse).
    This is the "interval generalization": `BoundaryType.closed`/`.open_`
    in `Core/Time` is isomorphic to `Boundedness.closed`/`.open_` in
    `Core/MeasurementScale`. -/
def boundaryTypeToBoundedness : Core.Time.Interval.BoundaryType → Boundedness
  | .closed => .closed
  | .open_ => .open_

theorem closedBoundary_licensed :
    (boundaryTypeToBoundedness .closed).isLicensed = true := rfl

theorem openBoundary_blocked :
    (boundaryTypeToBoundedness .open_).isLicensed = false := rfl

-- ════════════════════════════════════════════════════
-- § 2. MereoTag + LicensingPipeline Typeclass
-- ════════════════════════════════════════════════════

/-- Binary mereological classification: the shared abstraction underlying
    all four licensing frameworks. -/
inductive MereoTag where
  | qua  -- quantized / bounded / telic / closed
  | cum  -- cumulative / unbounded / atelic / open
  deriving DecidableEq, BEq, Repr

def MereoTag.toBoundedness : MereoTag → Boundedness
  | .qua => .closed
  | .cum => .open_

/-- A licensing pipeline: any type whose elements can be classified into
    scale boundedness. Kennedy, Rouillard, Krifka, and Zwarts all
    instantiate this with different source types but the same target. -/
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

instance : LicensingPipeline Core.Time.Interval.BoundaryType where
  toBoundedness := boundaryTypeToBoundedness

/-- The universal licensing theorem: any two pipeline inputs that map to
    the same Boundedness yield the same licensing prediction, regardless
    of which framework they come from. -/
theorem universal {α β : Type*} [LicensingPipeline α] [LicensingPipeline β]
    (a : α) (b : β) (h : toBoundedness a = toBoundedness b) :
    isLicensed a = isLicensed b := by
  simp only [isLicensed, h]

end LicensingPipeline

-- ════════════════════════════════════════════════════
-- § 3. DimensionChain Structure
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
-- § 4. Deep Mereological Bridge
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
-- § 5. Generic Pullback Patterns
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
-- § 6. Named Licensing Theorems
-- ════════════════════════════════════════════════════

/-- Krifka: QUA → closed → licensed. -/
theorem krifka_qua_licensed :
    quaBoundedness.isLicensed = true := rfl

/-- Krifka: CUM → open → blocked. -/
theorem krifka_cum_blocked :
    cumBoundedness.isLicensed = false := rfl

/-- Zwarts: bounded path → closed → licensed. -/
theorem zwarts_bounded_licensed :
    (PathShape.bounded.toBoundedness).isLicensed = true := rfl

/-- Zwarts: unbounded path → open → blocked. -/
theorem zwarts_unbounded_blocked :
    (PathShape.unbounded.toBoundedness).isLicensed = false := rfl

/-- All four frameworks agree: licensing depends solely on boundedness.
    Kennedy (2007): closed-scale adjectives license degree modifiers.
    Rouillard (2026): closed-runtime VPs license E-TIAs.
    Krifka (1989): QUA predicates yield telic (bounded) VPs.
    Zwarts (2005): bounded paths yield telic VPs.
    All four route through Boundedness.isLicensed. -/
theorem four_frameworks_agree
    (b : Boundedness) {W : Type*} (μ₁ μ₂ : W → ℚ) :
    (MIPDomain.kennedyAdjective μ₁ b).licensed =
    (MIPDomain.rouillardETIA μ₂ b).licensed := rfl

end Core.DimensionBridge
